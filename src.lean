section MinimalLogic

variable (α β γ : Prop)


theorem ex001 : (α → β) → (β → γ) → α → γ := by
  intro (hab : α → β)
  intro (hbg : β → γ)
  intro (ha : α) 
  exact hbg (hab ha)


theorem ex002 : (α → β) → (β → γ) → α → β := by
  intro (hab : α → β)
  intro
  intro (ha : α)
  exact hab ha


theorem ex003 : (α → γ) → (β → γ) → α ∨ β → γ := by
  intro (hag : α → γ)
  intro (hbg : β → γ)
  intro (h : α ∨ β)
  apply Or.elim h
  . intro (ha : α)
    exact hag ha
  . intro (hb : β)
    exact hbg hb


theorem ex004 : α ∧ β → β := by
  intro (hab : α ∧ β)
  exact hab.right


theorem ex005 : α ∧ (β ∧ γ) → (α ∧ β) ∧ γ := by
  intro (h : α ∧ (β ∧ γ))
  apply And.intro
  . apply And.intro
    exact h.left
    exact h.right.left
  . exact h.right.right


theorem ex006 : (α ∧ β) ∧ γ → α ∧ (β ∧ γ) := by
  intro (h : (α ∧ β) ∧ γ)
  apply And.intro
  . exact h.left.left
  . apply And.intro
    . exact h.left.right
    . exact h.right


theorem ex007 : ((α ∨ β) ∧ (α → β)) → β := by
  intro (h : (α ∨ β) ∧ (α → β))
  have hab := h.left
  apply Or.elim hab
  . intro ha
    exact h.right ha
  . intro hb
    exact hb

theorem ex007' : ((α ∨ β) ∧ (α → β)) → β :=
  fun h =>
    Or.elim h.left
      (fun ha => h.right ha)
      (fun hb => hb)


theorem ex008 : α ∨ (α ∧ β) → α := by
  intro h
  apply Or.elim h
  . intro (ha : α)
    exact ha
  . intro (hab : α ∧ β)
    exact hab.left


theorem ex009 : α ∨ (β ∧ γ) → (α ∨ β) ∧ (α ∨ γ) :=
  fun h : α ∨ (β ∧ γ) =>
    Or.elim h
      (fun ha : α =>
        And.intro (Or.inl ha) (Or.inl ha))
      (fun hbg : β ∧ γ =>
        And.intro (Or.inr hbg.left) (Or.inr hbg.right))


theorem ex010 : (α ∧ β) ∨ (α ∧ γ) → α ∧ (β ∨ γ) :=
  fun h : (α ∧ β) ∨ (α ∧ γ) =>
    Or.elim h
      (fun hab : α ∧ β =>
        And.intro hab.left (Or.inl hab.right))
      (fun hag : α ∧ γ =>
        And.intro hag.left (Or.inr hag.right))

end MinimalLogic



section IntuitionisticLogic

variable (α β γ δ σ : Prop)


theorem ex011 : ¬(α ∧ ¬α) :=
  fun h : α ∧ ¬α => h.right h.left


theorem ex012 : ¬α ∨ ¬β → ¬(α ∧ β) :=
  fun h : ¬α ∨ ¬β =>
    fun hab : α ∧ β =>
      Or.elim h
        (fun hna : ¬α => hna hab.left)
        (fun hnb : ¬β => hnb hab.right)


theorem ex013 : ¬(α ∨ β) → ¬α ∧ ¬β :=
  fun h : ¬(α ∨ β) =>
    And.intro
      (fun ha : α => h (Or.inl ha))
      (fun hb : β => h (Or.inr hb))


theorem ex014 : ¬α ∧ ¬β → ¬(α ∨ β) :=
  fun h : ¬α ∧ ¬β =>
    fun hab : α ∨ β =>
      Or.elim hab
        (fun ha : α => h.left ha)
        (fun hb : β => h.right hb)


theorem ex015 : False → α :=
  fun h : False => False.elim h


theorem ex016 : (¬α ∧ α) → β :=
  fun h : ¬α ∧ α => absurd h.right h.left


theorem ex017 : (¬γ ∧ (α ∧ β)) ∧ (α ∧ (β ∧ γ)) → (¬¬(α ∧ β) ∧ γ) ∨ (¬(α ∧ β) ∧ ¬γ) :=
  fun h : (¬γ ∧ (α ∧ β)) ∧ (α ∧ (β ∧ γ)) =>
    have ha : α := h.right.left
    have hb : β := h.right.right.left
    have hg : γ := h.right.right.right
    have hnnab : ¬¬(α ∧ β) :=
      fun hnab : ¬(α ∧ β) => hnab (And.intro ha hb)
    Or.inl (And.intro hnnab hg)


theorem ex018 : (α ∧ β) → (α ∨ β) :=
  fun h : α ∧ β => Or.inl h.left


theorem ex019 : α → ¬¬α ∧ (False → ¬α) :=
  fun ha : α =>
    And.intro
      (fun hna : ¬α => hna ha)
      (fun hf : False => False.elim hf)


theorem ex020 : ¬¬(¬α ∨ α) :=
  fun hn : ¬(¬α ∨ α) =>
    have hna : ¬α := fun ha : α => hn (Or.inr ha)
    have h : ¬α ∨ α := Or.inl hna
    hn h


theorem ex021 : (α → β) → (α → ¬β) → α → γ :=
  fun h₁ : α → β =>
    fun h₂ : α → ¬β =>
      fun ha : α =>
        absurd (h₁ ha) (h₂ ha)


theorem ex022 : ¬α → α → β :=
  fun hna : ¬α =>
    fun ha : α =>
      absurd ha hna


theorem ex023 : ¬¬((¬α → β) ∧ (β → α) → α) :=
  fun hn : ¬((¬α → β) ∧ (β → α) → α) =>
    (hn (fun h : (¬α → β) ∧ (β → α) =>
          (h.right (h.left (fun ha : α =>
                             (hn (fun _ => ha)))))))


theorem ex024 : (α → β) → ¬β → ¬α :=
  fun hab : α → β =>
    fun hnb : ¬β =>
      fun ha : α =>
        absurd (hab ha) hnb


theorem ex025 : (¬α → ¬β) → ¬¬(β → α) :=
  fun hnanb : ¬α → ¬β =>
    fun hnba : ¬(β → α) =>
      have hna : ¬α := fun ha : α => hnba (fun _ : β => ha)
      have hnb : ¬β := hnanb hna
      hnba (fun hb : β => absurd hb hnb)

example : ¬(β → α) → ¬α :=
  fun h =>
    fun ha => h (fun _ => ha)


theorem ex026 : (α ∧ β → γ) → α → β → γ :=
  fun (h : α ∧ β → γ) (ha : α) (hb : β) =>
    h (And.intro ha hb)


theorem ex027 : ((α → β) → α) → ¬¬α :=
  fun h : (α → β) → α =>
    fun hna : ¬α =>
      (hna (h (fun ha : α => absurd ha hna)))


theorem ex028 : α → (α → β) → β :=
  fun (ha : α) (hab : α → β) =>
    hab ha


theorem ex029 : ((α → β) → γ) → ((β → α) → δ) → ¬¬(γ ∨ δ) :=
  fun (h₁ : (α → β) → γ) (h₂ : (β → α) → δ) =>
    fun hngd : ¬(γ ∨ δ) =>
      hngd
      (Or.inl
        (h₁ (fun ha : α =>
              absurd
                (Or.inr (h₂ (fun _ : β => ha)))
                hngd)))
 

theorem ex030 : (α → γ) ∧ (β → ¬γ) → ¬(α ∧ β) :=
  fun h : (α → γ) ∧ (β → ¬γ) =>
    fun hab : α ∧ β =>
      (h.right hab.right) (h.left hab.left)


end IntuitionisticLogic



section ClassicalLogic

open Classical

variable (α β γ δ: Prop)

theorem ex031 : ¬α ∨ α :=
  Or.elim (em α)
    (fun ha : α => Or.inr ha)
    (fun hna : ¬α => Or.inl hna)


theorem ex032 : ¬¬α ∨ ¬α :=
  Or.elim (em α)
    (fun ha : α => Or.inl (fun hna : ¬α => hna ha))
    (fun hna : ¬α => Or.inr hna)


theorem ex033 : ((α → β) → α) → α :=
  fun h : (α → β) → α =>
    byContradiction
    fun hna : ¬α =>
      hna (h (fun ha : α => absurd ha hna))


theorem ex034 : ((α → β) → γ) → ((β → α) → δ) → γ ∨ δ :=
  fun (habg : (α → β) → γ) (hbad : (β → α) → δ) =>
    Or.elim (em α)
      (fun ha : α =>
        Or.inr (hbad (fun _ : β => ha)))
      (fun hna : ¬α =>
        Or.inl (habg (fun ha : α => absurd ha hna)))


theorem ex035 : (¬α → β) ∧ (β → α) → α :=
  fun h : (¬α → β) ∧ (β → α) =>
    byContradiction
    fun hna : ¬α =>
      have hnab : ¬α → β := h.left
      have hba : β → α := h.right
      have ha : α := hba (hnab hna)
      show False from hna ha
 

theorem ex036 : (¬α → ¬β) → β → α :=
  fun (hnanb : ¬α → ¬β) (hb : β) =>
    byContradiction
    fun hna : ¬α =>
      absurd hb (hnanb (fun ha : α => hna ha))


theorem ex037 : ((α ∧ β → γ) → α ∧ β) → α ∧ β :=
  fun h : (α ∧ β → γ) → α ∧ β =>
    byContradiction
    fun hnab : ¬(α ∧ β) =>
      hnab (h (fun hab : α ∧ β => absurd hab hnab))


theorem ex038 : ((α ∨ β → α ∧ β) → α ∨ β) → α ∨ β :=
  fun h : (α ∨ β → α ∧ β) → α ∨ β =>
  byContradiction
  fun hnab : ¬(α ∨ β) =>
    hnab (h (fun hab : α ∨ β => absurd hab hnab))


theorem ex039 : (α → α → β) → α → β :=
  fun (haab : α → α → β) (ha : α) =>
    haab ha ha


theorem ex040 : ¬α ∨ (β ∨ (β → α)) :=
  Or.elim (em α)
    (fun ha : α =>
      Or.inr (Or.inr (fun _ : β => ha)))
    (fun hna : ¬α => Or.inl hna)


theorem ex041 : (α → β) ∨ α :=
  Or.elim (em α)
    (fun ha : α => Or.inr ha)
    (fun hna : ¬α =>
      Or.inl (fun ha : α => absurd ha hna))


theorem ex042 : (α ∧ β → α ∨ β) ∨ (α ∨ β → α ∧ β) :=
  Or.inl (fun hab : α ∧ β => Or.inl hab.left)

theorem ex042' : ((α → β) ∧ (β → α)) → (α ∨ β → α ∧ β) :=
  fun h : ((α → β) ∧ (β → α)) =>
    fun hab : α ∨ β =>
      Or.elim hab
        (fun ha : α => ⟨ha, h.left ha⟩)
        (fun hb : β => ⟨h.right hb, hb⟩)


theorem ex043 : (α → β) → (α → ¬β) → ¬α :=
  fun (hab : α → β) (hanb : α → ¬β) =>
    fun ha : α =>
      (hanb ha) (hab ha)


theorem ex044 : (¬α → β) → (¬α → ¬β) → α :=
  fun (hnab : ¬α → β) (hnanb : ¬α → ¬β) =>
    byContradiction
    fun hna : ¬α => (hnanb hna) (hnab hna)


theorem ex045 : α ∨ ¬(α ∧ β) :=
  Or.elim (em α)
    (fun ha : α => Or.inl ha)
    (fun hna : ¬α =>
      Or.inr (fun hab : α ∧ β => hna hab.left))


theorem ex046 : (α ∧ β → α ∨ β) → (α → α ∨ β) ∨ (β → α ∨ β) :=
  fun _ => Or.inl fun ha : α => Or.inl ha


theorem ex047 : (α ∧ β → γ) → (α → γ) ∨ (β → γ) :=
  fun h : α ∧ β → γ =>
    Or.elim (em α)
      (fun ha : α =>
        Or.elim (em β)
          (fun hb : β => Or.inl (fun _ : α => h ⟨ha, hb⟩))
          (fun hnb : ¬β => Or.inr (fun hb : β => absurd hb hnb)))
      (fun _ : ¬α =>
        Or.elim (em β)
          (fun hb : β => Or.inl (fun ha : α => h ⟨ha, hb⟩))
          (fun hnb : ¬β => Or.inr (fun hb : β => absurd hb hnb)))


theorem ex048 : (¬α → (α ∧ ¬β)) → α :=
  fun h : ¬α → (α ∧ ¬β) =>
    byContradiction
    fun hna : ¬α =>
      absurd (h hna).left hna
      

theorem ex049 : (α → β) ∧ (¬α → β) → β :=
  fun h : (α → β) ∧ (¬α → β) =>
    Or.elim (em α)
      (fun ha : α => h.left ha)
      (fun hna : ¬α => h.right hna)


theorem ex050 : ((α ∧ β) ∨ ¬α) → α → β :=
  fun (h₁ : (α ∧ β) ∨ ¬α) (h₂ : α) =>
    Or.elim h₁
      (fun hab : α ∧ β => hab.right)
      (fun hna : ¬α => absurd h₂ hna)


theorem ex051 : (α ∧ ¬β → ¬γ) → α ∧ γ → β :=
  fun (h₁ : α ∧ ¬β → ¬γ) (h₂ : α ∧ γ) =>
    byContradiction
    fun hnb : ¬β =>
      have hg : γ := h₂.right
      have hng : ¬γ := h₁ (And.intro h₂.left hnb)
      absurd hg hng


theorem ex052 : α ∨ ¬α → β ∨ ¬(α ∧ β) :=
  fun h : α ∨ ¬α =>
    Or.elim h
      (fun _ : α =>
        Or.elim (em β)
          (fun hb : β => Or.inl hb)
          (fun hnb : ¬β =>
            Or.inr (fun hab : α ∧ β => hnb hab.right)))
      (fun hna : ¬α =>
        Or.inr (fun hab : α ∧ β => hna hab.left))


theorem ex053 : (α ∧ β → γ) → α → β → γ :=
  fun (h : α ∧ β → γ) (ha : α) (hb : β) =>
    h (And.intro ha hb)
  

theorem ex054 : (α → β → γ) → α ∧ β → γ :=
  fun (habg : α → β → γ) (hab : α ∧ β) =>
    habg hab.left hab.right


-- should find another proof (using ¬α → β)
theorem ex055 : (¬α → β) → ((β → α) → β) → β :=
  fun _ (h : (β → α) → β) =>
    byContradiction
    fun hnb : ¬β =>
      hnb (h (fun hb : β => absurd hb hnb))


theorem ex056 : α ∨ (α → (β ∨ (β → (γ → (γ → δ ∨ ¬δ))))) :=
  Or.elim (em α)
    (fun ha : α => Or.inl ha)
    (fun hna : ¬α => Or.inr (fun ha : α => absurd ha hna))
 

-- should find another proof (using dne and em)
theorem ex057 : ((¬¬α → α) → (α ∨ ¬α)) → ¬¬α ∨ ¬α :=
  fun _ =>
    Or.elim (em ¬α)
      (fun hna : ¬α => Or.inr hna)
      (fun hnna : ¬¬α => Or.inl hnna)
  

theorem ex058 : (¬α → β ∨ γ) → (¬α → β) ∨ (¬α → γ) :=
  fun h : ¬α → β ∨ γ =>
    Or.elim (em α)
      (fun ha : α =>
        Or.inl (fun hna : ¬α => absurd ha hna))
      (fun hna : ¬α =>
        Or.elim (h hna)
          (fun hb : β => Or.inl fun _ : ¬α => hb)
          (fun hg : γ => Or.inr fun _ : ¬α => hg))


theorem ex059 : (α → β) ∨ (β → α) :=
  Or.elim (em α)
    (fun ha : α => Or.inr (fun _ : β => ha))
    (fun hna : ¬α => Or.inl (fun ha : α => absurd ha hna))


theorem ex060 : (α ∨ β → γ) → (α → γ) ∧ (β → γ) :=
  fun h : α ∨ β → γ =>
    And.intro
      (fun ha : α => h (Or.inl ha))
      (fun hb : β => h (Or.inr hb))

end ClassicalLogic


section PredicateLogic

open Classical

variable (U : Type)
variable (A : Prop)
variable (P Q α β: U → Prop)

theorem ex061 : ∀ _ : U, (False → False) :=
  fun _ : U =>
    fun hf : False => hf


theorem ex062 : (∃ x, α x) → (∃ y, α y) :=
  fun h : ∃ x, α x =>
    Exists.elim h
      fun (t : U) (ht : α t) =>
        Exists.intro t ht


theorem ex063 : (∀ x, P x → Q x) → (∀ x, P x) → ∀ x, Q x :=
  fun (h₁ : ∀ x, P x → Q x) (h₂ : ∀ x, P x) =>
    fun x : U =>
      (h₁ x) (h₂ x)


theorem ex064 : (∀ x, A → P x) → A → ∀ x, P x :=
  fun (h : ∀ x, A → P x) (ha : A) =>
    fun x : U =>
      h x ha


theorem ex065 : (∀ x, α x) → α t :=
  fun h : ∀ x, α x =>
    h t


theorem ex066 : α t → ∃ x, α x :=
  fun h : α t =>
    Exists.intro t h


theorem ex067 : (∀ x, P x → A) → (∃ x, P x) → A :=
  fun (h₁ : ∀ x, P x → A) (h₂ : ∃ x, P x) =>
    Exists.elim h₂
      fun (t : U) (h₂t : P t) =>
        h₁ t h₂t


theorem ex068 : (A ∧ ∃ x, P x) → ∃ x, A ∧ P x :=
  fun h : A ∧ ∃ x, P x =>
    Exists.elim h.right
      fun (t : U) (ht : P t) =>
        Exists.intro t (And.intro h.left ht)


theorem ex069 : (∃ x, A ∧ P x) → A ∧ ∃ x, P x :=
  fun h : ∃ x, (A ∧ P x) =>
    Exists.elim h
      fun (t : U) (ht : A ∧ P t) =>
        And.intro ht.left (Exists.intro t ht.right)


theorem ex070 : (A ∧ ∀ x, P x) → ∀ x, A ∧ P x :=
  fun h : A ∧ ∀ x, P x =>
    fun x : U =>
      And.intro h.left (h.right x)


theorem ex071 (α : U → U → Prop) : (∀ x, ∀ y, α x y) → (∀ y, ∀ x, α x y) :=
  fun h : ∀ x, ∀ y, α x y =>
    fun y x : U => h x y


theorem ex072 : (∀ x, ¬¬α x) → ¬¬(∀ x, α x) :=
  fun h₁ : ∀ x, ¬¬α x =>
    fun h₂ : ¬(∀ x, α x) =>
      h₂ (fun x : U =>
            byContradiction
            fun hnax : ¬(α x) =>
              (h₁ x) hnax)


theorem ex073 : ¬¬(∀ x, α x) → (∀ x, ¬¬α x) :=
  fun h : ¬¬(∀ x, α x) =>
    fun x : U =>
      fun hnax : ¬(α x) =>
        h (fun h' : ∀ x, α x => hnax (h' x))
 

theorem ex074 : (∃ x, ¬¬α x) → ¬¬(∃ x, α x) :=
  fun h : ∃ x, ¬¬α x =>
    Exists.elim h
      fun (t : U) (hnnat : ¬¬(α t)) =>
        fun hnxax : ¬(∃ x, α x) =>
          hnxax
          (Exists.intro t
            (byContradiction
             fun hnat : ¬(α t) =>
               hnnat hnat))


theorem ex075 : ¬¬(∃ x, α x) → (∃ x, ¬¬(α x)) :=
  fun h₁ : ¬¬(∃ x, α x) =>
    byContradiction
    fun h₂ : ¬(∃ x, ¬¬(α x)) =>
      h₁ (fun h₁' : ∃ x, α x =>
            Exists.elim h₁'
            fun (t : U) (hat : α t) =>
              h₂ (Exists.intro t
                   (fun hnat : ¬(α t) =>
                      hnat hat)))


theorem ex076 : (∀ x, α x ∧ β x) → (∀ x, α x) ∧ (∀ x, β x) :=
  fun h : ∀ x, α x ∧ β x =>
    And.intro
      (fun x : U => (h x).left)
      (fun x : U => (h x).right)


theorem ex077 : (∀ x, α x) ∧ (∀ x, β x) → ∀ x, α x ∧ β x :=
  fun h : (∀ x, α x) ∧ (∀ x, β x) =>
    fun x : U => And.intro (h.left x) (h.right x)


theorem ex078 : (∃ x, α x ∧ β x) → (∃ x, α x) ∧ (∃ x, β x) :=
  fun h :  ∃ x, α x ∧ β x =>
    Exists.elim h
      fun (t : U) (ht : α t ∧ β t) =>
        And.intro
          (Exists.intro t ht.left)
          (Exists.intro t ht.right)


theorem ex079 : (∀ x, α x) ∨ (∀ x, β x) → (∀ x, α x ∨ β x) :=
  fun h : (∀ x, α x) ∨ (∀ x, β x) =>
    fun x : U =>
      Or.elim h
        (fun hxax : ∀ x, α x => Or.inl (hxax x))
        (fun hxbx : ∀ x, β x => Or.inr (hxbx x))


theorem ex080 : (∃ x, α x ∨ β x) → (∃ x, α x) ∨ (∃ x, β x) :=
  fun h : ∃ x, (α x ∨ β x) =>
    Exists.elim h
      fun (t : U) (ht : α t ∨ β t) =>
        Or.elim ht
          (fun hat : α t => Or.inl (Exists.intro t hat))
          (fun hbt : β t => Or.inr (Exists.intro t hbt))


theorem ex081 : (∃ x, α x) ∨ (∃ x, β x) → ∃ x, α x ∨ β x :=
  fun h : (∃ x, α x) ∨ (∃ x, β x) =>
    Or.elim h
      (fun hxax : ∃ x, α x =>
        Exists.elim hxax
          fun (t : U) (ht : α t) =>
            Exists.intro t (Or.inl ht))
      (fun hxbx : ∃ x, β x =>
        Exists.elim hxbx
          fun (t : U) (ht : β t) =>
            Exists.intro t (Or.inr ht))


theorem ex082 (α : Prop) : α ∧ (∃ x, β x) → ∃ x, α ∧ β x :=
  fun h : α ∧ (∃ x, β x) =>
    Exists.elim h.right
      fun (t : U) (hbt : β t) =>
        Exists.intro t (And.intro h.left hbt)


theorem ex083 (α : Prop) : (∀ x, α → β x) → α → ∀ x, β x :=
  fun (hxabx : ∀ x, (α → β x)) (ha : α) =>
    fun x : U => hxabx x ha


theorem ex084 (α : Prop) : (α → ∀ x, β x) → (∀ x, α → β x) :=
  fun h : α → ∀ x, β x =>
    fun x : U =>
      fun ha : α =>
        h ha x

theorem ex085 (β : Prop) : (∀ x, α x → β) → (∃ x, α x) → β :=
  fun (h₁ : ∀ x, (α x → β)) (h₂ : ∃ x, α x) =>
    Exists.elim h₂
      fun (t : U) (hat : α t) =>
        h₁ t hat


theorem ex086 : (∀ x, ¬α x) → ¬(∃ x, α x) :=
  fun h : ∀ x, ¬α x =>
    fun hxax : ∃ x, α x =>
      Exists.elim hxax
        fun (t : U) (hat : α t) =>
          h t hat


theorem ex087 : (¬∃ x, α x) → (∀ x, ¬α x) :=
  fun h : ¬∃ x, α x =>
    fun x : U =>
      fun hax : α x =>
        h (Exists.intro x hax)


theorem ex088 : (∃ x, ¬α x) → ¬(∀ x, α x) :=
  fun h : ∃ x, ¬α x =>
    fun hxax : ∀ x, α x =>
      Exists.elim h
        fun (t : U) (hnat : ¬α t) =>
          hnat (hxax t)


theorem ex089 : ¬(∀ x, α x) → (∃ x, ¬α x) :=
  fun hnxax : ¬(∀ x, α x) =>
    byContradiction
    fun hnxnax : ¬(∃ x, ¬α x) =>
      hnxax (fun x : U =>
              byContradiction
              fun hnax : ¬α x =>
                hnxnax (Exists.intro x hnax))


theorem ex090 (s : U) : (∀ x, ∃ y, P x ∧ Q y) → ∃ y, ∀ x, P x ∧ Q y :=
  fun h : ∀ x, ∃ y, P x ∧ Q y =>
    Exists.elim (h s)
      fun (t : U) (hst : P s ∧ Q t) =>
        Exists.intro t
          fun x : U =>
            And.intro
              (Exists.elim (h x)
                fun (t : U) (hxt : P x ∧ Q t) => hxt.left)
              hst.right

  
theorem ex091 : (∃ y, ∀ x, P x ∧ Q y) → ∀ x, ∃ y, P x ∧ Q y :=
  fun h : ∃ y, ∀ x, (P x ∧ Q y) =>
    Exists.elim h
      fun (y₁ : U) (hy₁ : ∀ x, (P x ∧ Q y₁)) =>
        fun x : U => Exists.intro y₁ (hy₁ x)


theorem ex092 (s : U) : (∀ x, ∃ y, (P x ∨ Q y)) → ∃ y, ∀ x, P x ∨ Q y := sorry
    

theorem ex093 : (∃ y, ∀ x, P x ∨ Q y) → ∀ x, ∃ y, P x ∨ Q y :=
  fun h : ∃ y, ∀ x, (P x ∨ Q y) =>
    Exists.elim h
      fun (y₁ : U) (hy₁ : ∀ x, (P x ∨ Q y₁)) =>
        fun x : U => Exists.intro y₁ (hy₁ x)


theorem ex094 (R : U → U → Prop) (t : U) : (∀ x, ∀ y, R x y ∧ R y x) → ∃ z, R z z :=
  fun h : ∀ x, ∀ y, R x y ∧ R y x =>
    Exists.intro t (h t t).left


theorem ex095 (R : U → U → Prop) : (∃ x, R x x) → ∃ y, ∃ z, R y z ∨ R z y :=
  fun h : ∃ x, R x x =>
    Exists.elim h
      fun (s : U) (hrss : R s s) =>
        Exists.intro s
          (Exists.intro s (Or.inl hrss))


theorem ex096' (s : U) : ∃ x, (P x → ∀ y, P y) := by
  apply byContradiction
  intro h
  apply h
  apply Exists.intro s
  intro hps
  intro y
  apply byContradiction
  intro hnpy
  apply h
  apply Exists.intro y
  intro hpy
  apply absurd hpy hnpy

example (h1 : ∀ x, P x → Q x) (h2 : ∃ x, P x) : ∃ x, Q x := by
  apply Exists.elim h2
  intro y
  intro hpy
  apply Exists.intro y
  apply h1
  apply hpy

end PredicateLogic
