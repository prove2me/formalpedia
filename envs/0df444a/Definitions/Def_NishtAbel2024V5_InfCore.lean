-- Prove2me | Definitions.Def_NishtAbel2024V5_InfCore
-- name    : NishtAbel2024V5_InfCore
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:28:27.290206+00:00
-- url     : https://prove2.me/theorems/b6cb0ece-0876-461f-9c16-9bde5c83024b
-- title:
--   Chapter 6.1–6.3 (V5 Support): Constraint Verification, Size-Erasure Kinding Bridge, Subtype Comparison, Spine Elaboration (Theorems 8–9), and Coherent Inference Soundness (Theorem 13)
-- statement:
--   Establishes the core soundness theorems for Chapter 6 size inference: soundness of the decidable constraint and scope checkers (`checkScope_sound`, `checkCoherent_sound`), the size-erasure kinding bridge (`EKinding`), soundness of algorithmic subtype comparison (`compare_subTy`), soundness of pattern and copattern spine inference (`inferPat_sound`, `inferSpine_sound`, Theorems 8 and 9), commutation of signature encoding with flexible substitutions, and Theorem 13 (`inference_sound`).
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 6, Sections 6.1-6.3, pp. 42-57, Theorems 8, 9 & 13

import Definitions.Def_NishtAbel2024V5_Inference
import Definitions.Def_NishtAbel2024V5_SemSubSpine

/-! ## Solutions/V5/InfCheck.lean -/

/-! # V5 inference: soundness of the executable size checks (Theorem 14, checked form) -/

namespace NishtAbel2024V5

theorem lookup_mem_gen {β : Type} {L : List (Nat × β)} {x : Nat} {v : β}
    (h : L.lookup x = some v) : (x, v) ∈ L := by
  induction L with
  | nil => simp [List.lookup] at h
  | cons p L ih =>
    obtain ⟨y, w⟩ := p
    by_cases hxy : x = y
    · subst hxy
      simp [List.lookup] at h
      subst h
      simp
    · have hb : (x == y) = false := by simpa using hxy
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem Size.wfB_sound {Ψ : SizeCtx} : ∀ {a : Size}, a.wfB Ψ = true → SizeWf Ψ a
  | .inf _, _ => trivial
  | .var i _, h => by
    show i ∈ Ψ.dom
    simpa [Size.wfB] using h
  | .bvar _ _, h => by simp [Size.wfB] at h
  | .meet _ _, h => by
    simp only [Size.wfB, Bool.and_eq_true] at h
    exact ⟨Size.wfB_sound h.1, Size.wfB_sound h.2⟩

theorem Size.wfB_complete {Ψ : SizeCtx} : ∀ {a : Size}, SizeWf Ψ a → a.wfB Ψ = true
  | .inf _, _ => rfl
  | .var i _, h => by
    have : i ∈ Ψ.dom := h
    simpa [Size.wfB] using this
  | .bvar _ _, h => absurd h (Nat.not_lt_zero _)
  | .meet _ _, h => by
    simp only [Size.wfB, Bool.and_eq_true]
    exact ⟨Size.wfB_complete h.1, Size.wfB_complete h.2⟩

/-- The executable strict comparison is sound. -/
theorem sizeLtB_sound : ∀ (fuel : Nat) (Ψ : SizeCtx) (a b : Size),
    sizeLtB fuel Ψ a b = true → SizeLt Ψ a b
  | 0, _, _, _, h => by simp [sizeLtB] at h
  | fuel + 1, Ψ, a, b, h => by
    unfold sizeLtB at h
    simp only [Bool.or_eq_true] at h
    rcases h with (h | h) | h
    · split at h
      · exact .inf_inf (by simpa using h)
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, hnm⟩, hi⟩ := h
        exact .var_var (by simpa using hi) hnm
      · simp at h
    · split at h
      · rename_i i n
        split at h
        · rename_i bnd hl
          have hm := lookup_mem_gen hl
          simp only [Bool.or_eq_true] at h
          rcases h with h | h
          · exact .bound hm (sizeLtB_sound fuel Ψ _ _ h)
          · split at h
            · exact .var_inf hm (sizeLtB_sound fuel Ψ _ _ h)
            · simp at h
        · simp at h
      · rename_i a₁ a₂
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · exact .meet_l (sizeLtB_sound fuel Ψ _ _ h₁) (Size.wfB_sound h₂)
        · exact .meet_r (sizeLtB_sound fuel Ψ _ _ h₁) (Size.wfB_sound h₂)
      · simp at h
    · split at h
      · simp only [Bool.and_eq_true] at h
        exact .lt_meet (sizeLtB_sound fuel Ψ _ _ h.1) (sizeLtB_sound fuel Ψ _ _ h.2)
      · simp at h

theorem sizeLeB_sound {fuel : Nat} {Ψ : SizeCtx} {a b : Size} (h : sizeLeB fuel Ψ a b = true) :
    SizeLe Ψ a b :=
  sizeLtB_sound fuel Ψ a (b.shift 1) h

theorem SConstr.check_sound {fuel : Nat} {φ : FlexSubst} {c : SConstr}
    (h : c.check fuel φ = true) : c.Holds φ := by
  unfold SConstr.check at h
  unfold SConstr.Holds
  split
  · rename_i hs
    simp only [hs, if_true] at h
    exact sizeLtB_sound _ _ _ _ h
  · rename_i hs
    simp only [hs, if_false] at h
    exact sizeLeB_sound h

/-- The coherence post-check is sound. -/
theorem checkCoherent_sound {fuel : Nat} {φ : FlexSubst} {C : List SConstr}
    (h : checkCoherent fuel φ C = true) : Coherent φ C := by
  intro c hc
  exact SConstr.check_sound (List.all_eq_true.mp h c hc)

/-- The scoping post-check is sound. -/
theorem checkScope_sound {φ : FlexSubst} {Φ : List FlexVar} (h : checkScope φ Φ = true) :
    ScopeOK φ Φ := by
  intro v hv
  have := List.all_eq_true.mp h v hv
  split at this
  · rename_i b hb
    exact ⟨b, hb, Size.wfB_sound this⟩
  · simp at this

end NishtAbel2024V5

/-! ## Solutions/V5/InfErase.lean -/

/-! # V5 inference: size erasure and kinding -/

namespace NishtAbel2024V5

/-- All size expressions of a type are well formed: free size variables in `Ψ`, bound size
variables below the binder depth. -/
inductive SizesWf (Ψ : SizeCtx) : Nat → Ty → Prop where
  | unit (m : Nat) : SizesWf Ψ m .unit
  | prod {m : Nat} {A B : Ty} : SizesWf Ψ m A → SizesWf Ψ m B → SizesWf Ψ m (.prod A B)
  | arr {m : Nat} {A B : Ty} : SizesWf Ψ m A → SizesWf Ψ m B → SizesWf Ψ m (.arr A B)
  | var (m k : Nat) : SizesWf Ψ m (.var k)
  | fvar (m X : Nat) : SizesWf Ψ m (.fvar X)
  | lam {m : Nat} {ι : SKind} {F : Ty} : SizesWf Ψ m F → SizesWf Ψ m (.lam ι F)
  | app {m : Nat} {F G : Ty} {ι : SKind} :
      SizesWf Ψ m F → SizesWf Ψ m G → SizesWf Ψ m (.app F G ι)
  | mu {m : Nat} {a : Size} {S : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ S, SizesWf Ψ m T) → SizesWf Ψ m (.mu a S)
  | nu {m : Nat} {a : Size} {R : List Ty} :
      SizeWfAt Ψ m a → (∀ T ∈ R, SizesWf Ψ m T) → SizesWf Ψ m (.nu a R)
  | allT {m : Nat} {κ : Kind} {B : Ty} : SizesWf Ψ m B → SizesWf Ψ m (.allT κ B)
  | exT {m : Nat} {κ : Kind} {B : Ty} : SizesWf Ψ m B → SizesWf Ψ m (.exT κ B)
  | allS {m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → SizesWf Ψ (m + 1) B → SizesWf Ψ m (.allS a B)
  | exS {m : Nat} {a : Size} {B : Ty} :
      SizeWfAt Ψ m a → SizesWf Ψ (m + 1) B → SizesWf Ψ m (.exS a B)

theorem Ty.mem_eraseSzList {S : List Ty} {T : Ty} (h : T ∈ S) : T.eraseSz ∈ Ty.eraseSzList S := by
  induction S with
  | nil => simp at h
  | cons A S ih =>
    simp only [Ty.eraseSzList, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (ih h)

theorem Ty.mem_eraseSzList_inv {S : List Ty} {T₀ : Ty} (h : T₀ ∈ Ty.eraseSzList S) :
    ∃ T ∈ S, T.eraseSz = T₀ := by
  induction S with
  | nil => simp [Ty.eraseSzList] at h
  | cons A S ih =>
    simp only [Ty.eraseSzList, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨A, by simp, rfl⟩
    · obtain ⟨T, hT, he⟩ := ih h
      exact ⟨T, by simp [hT], he⟩

/-- Kinding of the size erasure, with well-formed sizes, gives kinding. -/
theorem kinding_of_erase {Δ : KCtx} {Δb : BCtx} {m : Nat} {A₀ : Ty} {κ : Kind}
    (h : Kinding [] Δ Δb m A₀ κ) :
    ∀ {Ψ : SizeCtx} {A : Ty}, A.eraseSz = A₀ → SizesWf Ψ m A → Kinding Ψ Δ Δb m A κ := by
  induction h with
  | unit =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    exact .unit
  | prod _ _ ihA ihB =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | prod h₁ h₂ => exact .prod (ihA rfl h₁) (ihB rfl h₂)
  | arr _ _ ihA ihB =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | arr h₁ h₂ => exact .arr (ihA rfl h₁) (ihB rfl h₂)
  | var hk hπ =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    subst he
    exact .var hk hπ
  | fvar hX hπ =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    subst he
    exact .fvar hX hπ
  | lam hι _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | lam h₁ => exact .lam hι (ih rfl h₁)
  | app _ _ hι ihF ihG =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    cases hw with
    | app h₁ h₂ => exact .app (ihF rfl h₁) (ihG rfl h₂) hι
  | mu hπ _ _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨_, rfl⟩ := he
    cases hw with
    | mu ha hS =>
      refine .mu hπ ha fun T hT => ?_
      exact ih _ (Ty.mem_eraseSzList hT) rfl (hS T hT)
  | nu hπ _ _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨_, rfl⟩ := he
    cases hw with
    | nu ha hR =>
      refine .nu hπ ha fun T hT => ?_
      exact ih _ (Ty.mem_eraseSzList hT) rfl (hR T hT)
  | allT _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | allT h₁ => exact .allT (ih rfl h₁)
  | exT _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨rfl, rfl⟩ := he
    cases hw with
    | exT h₁ => exact .exT (ih rfl h₁)
  | allS _ _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨_, rfl⟩ := he
    cases hw with
    | allS ha h₁ => exact .allS ha (ih rfl h₁)
  | exS _ _ ih =>
    intro Ψ A he hw
    cases A <;> simp [Ty.eraseSz] at he
    obtain ⟨_, rfl⟩ := he
    cases hw with
    | exS ha h₁ => exact .exS ha (ih rfl h₁)
  | sub _ hs ih =>
    intro Ψ A he hw
    exact .sub (ih he hw) hs

/-- Kinding of an annotated type gives kinding of its size erasure. -/
theorem Kinding.erase {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) : Kinding [] Δ Δb m A.eraseSz κ := by
  induction h with
  | unit => exact .unit
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var hk hπ => exact .var hk hπ
  | fvar hX hπ => exact .fvar hX hπ
  | lam hι _ ih => exact .lam hι ih
  | app _ _ hι ihF ihG => exact .app ihF ihG hι
  | mu hπ _ _ ih =>
    refine .mu hπ trivial fun T hT => ?_
    obtain ⟨T', hT', rfl⟩ := Ty.mem_eraseSzList_inv hT
    exact ih T' hT'
  | nu hπ _ _ ih =>
    refine .nu hπ trivial fun T hT => ?_
    obtain ⟨T', hT', rfl⟩ := Ty.mem_eraseSzList_inv hT
    exact ih T' hT'
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS _ _ ih => exact .allS trivial ih
  | exS _ _ ih => exact .exS trivial ih
  | sub _ hs ih => exact .sub ih hs

/-- Kinding gives well-formed sizes. -/
theorem Kinding.sizesWf {Ψ : SizeCtx} {Δ : KCtx} {Δb : BCtx} {m : Nat} {A : Ty} {κ : Kind}
    (h : Kinding Ψ Δ Δb m A κ) : SizesWf Ψ m A := by
  induction h with
  | unit => exact .unit _
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var => exact .var _ _
  | fvar => exact .fvar _ _
  | lam _ _ ih => exact .lam ih
  | app _ _ _ ihF ihG => exact .app ihF ihG
  | mu _ ha _ ih => exact .mu ha ih
  | nu _ ha _ ih => exact .nu ha ih
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS ha _ ih => exact .allS ha ih
  | exS ha _ ih => exact .exS ha ih
  | sub _ _ ih => exact ih

/-- From size-erased kinding. -/
theorem EKinding.kinding {Δ : KCtx} {Δb : BCtx} {A : Ty} {κ : Kind} (h : EKinding Δ Δb A κ)
    {Ψ : SizeCtx} (hw : SizesWf Ψ 0 A) : Kinding Ψ Δ Δb 0 A κ :=
  kinding_of_erase h rfl hw

/-! ## Erasure ignores sizes -/

mutual
theorem Ty.eraseSz_substSize (σ : List (Nat × Size)) :
    ∀ A : Ty, (A.substSize σ).eraseSz = A.eraseSz
  | .unit => rfl
  | .prod A B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ A, Ty.eraseSz_substSize σ B]
  | .arr A B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ A, Ty.eraseSz_substSize σ B]
  | .var _ => rfl
  | .fvar _ => rfl
  | .lam ι F => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ F]
  | .app F G ι => by
    simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ F, Ty.eraseSz_substSize σ G]
  | .mu a S => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSzList_substSizeList σ S]
  | .nu a R => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSzList_substSizeList σ R]
  | .allT κ B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ B]
  | .exT κ B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ B]
  | .allS a B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ B]
  | .exS a B => by simp [Ty.substSize, Ty.eraseSz, Ty.eraseSz_substSize σ B]
theorem Ty.eraseSzList_substSizeList (σ : List (Nat × Size)) :
    ∀ S : List Ty, Ty.eraseSzList (Ty.substSizeList σ S) = Ty.eraseSzList S
  | [] => rfl
  | A :: S => by
    simp [Ty.substSizeList, Ty.eraseSzList, Ty.eraseSz_substSize σ A,
      Ty.eraseSzList_substSizeList σ S]
end

/-! ## Well-formed sizes under substitution -/

theorem SizesWf.substSize {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) {Ψ' : SizeCtx}
    {σ : List (Nat × Size)} (hσ : ∀ i ∈ Ψ.dom, SizeWf Ψ' ((Size.var i 0).subst σ)) :
    SizesWf Ψ' m (A.substSize σ) := by
  induction h with
  | unit => exact .unit _
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var => exact .var _ _
  | fvar => exact .fvar _ _
  | lam _ ih => exact .lam ih
  | app _ _ ihF ihG => exact .app ihF ihG
  | mu ha _ ih =>
    simp only [Ty.substSize]
    refine .mu (SizeWfAt.subst hσ ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substSizeList hT'
    exact ih B hB
  | nu ha _ ih =>
    simp only [Ty.substSize]
    refine .nu (SizeWfAt.subst hσ ha) fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substSizeList hT'
    exact ih B hB
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS ha _ ih => exact .allS (SizeWfAt.subst hσ ha) ih
  | exS ha _ ih => exact .exS (SizeWfAt.subst hσ ha) ih

end NishtAbel2024V5

/-! ## Solutions/V5/InfCompare.lean -/

/-! # V5 inference: comparison of types under a coherent substitution gives subtyping -/

namespace NishtAbel2024V5

/-! ## Well-formed sizes: weakening and type substitution -/

theorem SizesWf.weaken {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) :
    ∀ {m' : Nat}, m ≤ m' → SizesWf Ψ m' A := by
  induction h with
  | unit => intros; exact .unit _
  | prod _ _ ihA ihB => intro m' hm; exact .prod (ihA hm) (ihB hm)
  | arr _ _ ihA ihB => intro m' hm; exact .arr (ihA hm) (ihB hm)
  | var => intros; exact .var _ _
  | fvar => intros; exact .fvar _ _
  | lam _ ih => intro m' hm; exact .lam (ih hm)
  | app _ _ ihF ihG => intro m' hm; exact .app (ihF hm) (ihG hm)
  | mu ha _ ih => intro m' hm; exact .mu (ha.weaken (fun _ h => h) hm) fun T hT => ih T hT hm
  | nu ha _ ih => intro m' hm; exact .nu (ha.weaken (fun _ h => h) hm) fun T hT => ih T hT hm
  | allT _ ih => intro m' hm; exact .allT (ih hm)
  | exT _ ih => intro m' hm; exact .exT (ih hm)
  | allS ha _ ih => intro m' hm; exact .allS (ha.weaken (fun _ h => h) hm) (ih (by omega))
  | exS ha _ ih => intro m' hm; exact .exS (ha.weaken (fun _ h => h) hm) (ih (by omega))

theorem SizesWf.substTy {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) :
    ∀ {k : Nat} {G : Ty}, SizesWf Ψ 0 G → SizesWf Ψ m (A.substTy k G) := by
  induction h with
  | unit => intros; exact .unit _
  | prod _ _ ihA ihB => intro k G hG; exact .prod (ihA hG) (ihB hG)
  | arr _ _ ihA ihB => intro k G hG; exact .arr (ihA hG) (ihB hG)
  | var m X =>
    intro k G hG
    simp only [Ty.substTy]
    split
    · exact hG.weaken (Nat.zero_le _)
    · split
      · exact .var _ _
      · exact .var _ _
  | fvar => intros; exact .fvar _ _
  | lam _ ih => intro k G hG; exact .lam (ih hG)
  | app _ _ ihF ihG => intro k G hG; exact .app (ihF hG) (ihG hG)
  | mu ha _ ih =>
    intro k G hG
    simp only [Ty.substTy]
    refine .mu ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB hG
  | nu ha _ ih =>
    intro k G hG
    simp only [Ty.substTy]
    refine .nu ha fun T' hT' => ?_
    obtain ⟨B, hB, rfl⟩ := Ty.mem_substTyList hT'
    exact ih B hB hG
  | allT _ ih => intro k G hG; exact .allT (ih hG)
  | exT _ ih => intro k G hG; exact .exT (ih hG)
  | allS ha _ ih => intro k G hG; exact .allS ha (ih hG)
  | exS ha _ ih => intro k G hG; exact .exS ha (ih hG)

theorem SizesWf.open_fvar {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) (X : Nat) :
    SizesWf Ψ m (A.substTy 0 (.fvar X)) :=
  h.substTy (.fvar 0 X)

/-! ## Constraints of comparisons -/

theorem Coherent.left {φ : FlexSubst} {C₁ C₂ : List SConstr} (h : Coherent φ (C₁ ++ C₂)) :
    Coherent φ C₁ := fun c hc => h c (List.mem_append_left _ hc)

theorem Coherent.right {φ : FlexSubst} {C₁ C₂ : List SConstr} (h : Coherent φ (C₁ ++ C₂)) :
    Coherent φ C₂ := fun c hc => h c (List.mem_append_right _ hc)

theorem Coherent.tail {φ : FlexSubst} {c : SConstr} {C : List SConstr} (h : Coherent φ (c :: C)) :
    Coherent φ C := fun c' hc => h c' (List.mem_cons_of_mem _ hc)

theorem Coherent.head {φ : FlexSubst} {c : SConstr} {C : List SConstr} (h : Coherent φ (c :: C)) :
    c.Holds φ := h c (List.mem_cons_self)

theorem compareList_length {Ψ : SizeCtx} {Δ : KCtx} {X : Nat} {S S' : List Ty}
    {C : List SConstr} (h : CompareList Ψ Δ X S S' C) : S.length = S'.length := by
  induction S generalizing S' C with
  | nil => cases h; rfl
  | cons T S ih =>
    cases h with
    | cons _ h' => simp [ih h']

theorem Ty.substSizeList_length' (σ : List (Nat × Size)) (S : List Ty) :
    (Ty.substSizeList σ S).length = S.length := Ty.substSizeList_length σ S

theorem Ty.substSizeList_getElem?' (σ : List (Nat × Size)) (S : List Ty) (d : Nat) :
    (Ty.substSizeList σ S)[d]? = (S[d]?).map (Ty.substSize σ) := Ty.substSizeList_getElem? σ S d

/-! ## Soundness of comparison -/

theorem mem_substSizeList_of_getElem? {σ : List (Nat × Size)} {S : List Ty} {c : Nat} {T : Ty}
    (h : (Ty.substSizeList σ S)[c]? = some T) : T ∈ Ty.substSizeList σ S :=
  List.mem_of_getElem? h

/-- The statement for one comparison. -/
def CompareOK (φ : FlexSubst) (Ψ : SizeCtx) (Δ : KCtx) (A B : Ty) (κ : Kind) : Prop :=
  SizesWf (Ψ.substBounds φ) 0 (A.substSize φ) → SizesWf (Ψ.substBounds φ) 0 (B.substSize φ) →
    SubTy (Ψ.substBounds φ) Δ (A.substSize φ) (B.substSize φ) κ

theorem SizeCtx.substBounds_dom (φ : FlexSubst) (Ψ : SizeCtx) :
    (Ψ.substBounds φ).dom = Ψ.dom := by
  simp [SizeCtx.substBounds, SizeCtx.dom]

theorem functors_sub {φ : FlexSubst} {Ψ : SizeCtx} {Δ : KCtx} {X : Nat} {S S' : List Ty}
    (hS : ∀ T ∈ Ty.substSizeList φ S, SizesWf (Ψ.substBounds φ) 0 T)
    (hS' : ∀ T ∈ Ty.substSizeList φ S', SizesWf (Ψ.substBounds φ) 0 T)
    (ih : ∀ (c : Nat) (U U' : Ty), S[c]? = some U → S'[c]? = some U' →
      CompareOK φ Ψ (Δ ++ [(X, .mix, .star)]) (U.substTy 0 (.fvar X)) (U'.substTy 0 (.fvar X))
        .star) :
    ∀ (c : Nat) (T T' : Ty), (Ty.substSizeList φ S)[c]? = some T →
      (Ty.substSizeList φ S')[c]? = some T' →
      SubTy (Ψ.substBounds φ) (Δ ++ [(X, .mix, .star)]) (T.substTy 0 (.fvar X))
        (T'.substTy 0 (.fvar X)) .star := by
  intro c T T' hT hT'
  have hTm := mem_substSizeList_of_getElem? hT
  have hTm' := mem_substSizeList_of_getElem? hT'
  rw [Ty.substSizeList_getElem?] at hT hT'
  obtain ⟨U, hU, rfl⟩ := Option.map_eq_some_iff.mp hT
  obtain ⟨U', hU', rfl⟩ := Option.map_eq_some_iff.mp hT'
  have := ih c U U' hU hU' (by rw [Ty.substSize_substTy]; exact (hS _ hTm).open_fvar X)
    (by rw [Ty.substSize_substTy]; exact (hS' _ hTm').open_fvar X)
  simpa [Ty.substSize_substTy, Ty.substSize] using this

theorem positive_sub {φ : FlexSubst} {Ψ : SizeCtx} {Δ : KCtx} {S' : List Ty}
    (hS' : ∀ T ∈ Ty.substSizeList φ S', SizesWf (Ψ.substBounds φ) 0 T)
    (hpos : ∀ T' ∈ S', EKinding Δ [(.pos, .star)] T' .star) :
    ∀ T' ∈ Ty.substSizeList φ S', Kinding (Ψ.substBounds φ) Δ [(.pos, .star)] 0 T' .star := by
  intro T' hT'
  obtain ⟨U, hU, rfl⟩ := Ty.mem_substSizeList hT'
  exact kinding_of_erase (hpos U hU) (Ty.eraseSz_substSize φ U) (hS' _ hT')

theorem compare_sound {φ : FlexSubst} {Ψ : SizeCtx} {Δ : KCtx} {A B : Ty} {κ : Kind}
    {C : List SConstr} (h : Compare Ψ Δ A B κ C) (hc : Coherent φ C) :
    CompareOK φ Ψ Δ A B κ := by
  refine Compare.rec
    (motive_1 := fun Δ A B κ C _ => Coherent φ C → CompareOK φ Ψ Δ A B κ)
    (motive_2 := fun Δ X S S' C _ => Coherent φ C →
      S.length = S'.length ∧ ∀ (c : Nat) (T T' : Ty), S[c]? = some T → S'[c]? = some T' →
        CompareOK φ Ψ Δ (T.substTy 0 (.fvar X)) (T'.substTy 0 (.fvar X)) .star)
    ?refl ?beta_l ?beta_r ?prod ?arr ?app_pos ?app_neg ?app_mix ?app_top ?lam ?allT ?exT
    ?mu_pos ?mu_eqv ?nu_pos ?nu_eqv ?nil ?cons h hc
  case refl =>
    intro Δ A κ hk _ hA _
    refine .refl (kinding_of_erase hk ?_ hA)
    exact Ty.eraseSz_substSize φ A
  case beta_l =>
    intro Δ F G B ι κ C hk _ ih hcoh hA hB
    have hA' := hA
    simp only [Ty.substSize] at hA ⊢
    cases hA with
    | app hlam hG =>
      cases hlam with
      | lam hF =>
        have hk' : KindingC (Ψ.substBounds φ) Δ
            (.app (.lam ι (F.substSize φ)) (G.substSize φ) ι) κ := by
          refine kinding_of_erase hk ?_ (.app (.lam hF) hG)
          simp [Ty.eraseSz, Ty.eraseSz_substSize]
        refine .beta_l hk' ?_
        have := ih hcoh (by rw [Ty.substSize_substTy]; exact hF.substTy hG) hB
        rwa [Ty.substSize_substTy] at this
  case beta_r =>
    intro Δ F G A ι κ C hk _ ih hcoh hA hB
    simp only [Ty.substSize] at hB ⊢
    cases hB with
    | app hlam hG =>
      cases hlam with
      | lam hF =>
        have hk' : KindingC (Ψ.substBounds φ) Δ
            (.app (.lam ι (F.substSize φ)) (G.substSize φ) ι) κ := by
          refine kinding_of_erase hk ?_ (.app (.lam hF) hG)
          simp [Ty.eraseSz, Ty.eraseSz_substSize]
        refine .beta_r hk' ?_
        have := ih hcoh hA (by rw [Ty.substSize_substTy]; exact hF.substTy hG)
        rwa [Ty.substSize_substTy] at this
  case prod =>
    intro Δ A A' B B' C₁ C₂ _ _ ih₁ ih₂ hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | prod hA hB =>
      cases hR with
      | prod hA' hB' => exact .prod (ih₁ hcoh.left hA hA') (ih₂ hcoh.right hB hB')
  case arr =>
    intro Δ A A' B B' C₁ C₂ _ _ ih₁ ih₂ hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | arr hA hB =>
      cases hR with
      | arr hA' hB' => exact .arr (ih₁ hcoh.left hA' hA) (ih₂ hcoh.right hB hB')
  case app_pos =>
    intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ _ _ hkG hkG' hι ihF ihG hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | app hF hG =>
      cases hR with
      | app hF' hG' =>
        refine .app (ihF hcoh.left hF hF') (fun _ => ihG hcoh.right hG hG')
          (fun h => absurd h (by simp [Pol.le])) (kinding_of_erase hkG ?_ hG)
          (kinding_of_erase hkG' ?_ hG') hι
        · exact Ty.eraseSz_substSize φ G
        · exact Ty.eraseSz_substSize φ G'
  case app_neg =>
    intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ _ _ hkG hkG' hι ihF ihG hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | app hF hG =>
      cases hR with
      | app hF' hG' =>
        refine .app (ihF hcoh.left hF hF') (fun h => absurd h (by simp [Pol.le]))
          (fun _ => ihG hcoh.right hG' hG) (kinding_of_erase hkG ?_ hG)
          (kinding_of_erase hkG' ?_ hG') hι
        · exact Ty.eraseSz_substSize φ G
        · exact Ty.eraseSz_substSize φ G'
  case app_mix =>
    intro Δ F F' G G' ι κ₁ κ₂ C₁ C₂ C₃ _ _ _ hkG hkG' hι ihF ihG ihG' hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | app hF hG =>
      cases hR with
      | app hF' hG' =>
        refine .app (ihF hcoh.left.left hF hF') (fun _ => ihG hcoh.left.right hG hG')
          (fun _ => ihG' hcoh.right hG' hG) (kinding_of_erase hkG ?_ hG)
          (kinding_of_erase hkG' ?_ hG') hι
        · exact Ty.eraseSz_substSize φ G
        · exact Ty.eraseSz_substSize φ G'
  case app_top =>
    intro Δ F F' G G' ι κ₁ κ₂ C₁ _ hkG hkG' hι ihF hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | app hF hG =>
      cases hR with
      | app hF' hG' =>
        refine .app (ihF hcoh hF hF') (fun h => absurd h (by simp [Pol.le]))
          (fun h => absurd h (by simp [Pol.le])) (kinding_of_erase hkG ?_ hG)
          (kinding_of_erase hkG' ?_ hG') hι
        · exact Ty.eraseSz_substSize φ G
        · exact Ty.eraseSz_substSize φ G'
  case lam =>
    intro Δ F F' ι ι' π κ₁ κ₂ X C hX _ hk hk' ih hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | lam hF =>
      cases hR with
      | lam hF' =>
        refine .lam hX ?_ (kinding_of_erase hk ?_ (.lam hF)) (kinding_of_erase hk' ?_ (.lam hF'))
        · have := ih hcoh (by rw [Ty.substSize_substTy]; exact hF.open_fvar X)
            (by rw [Ty.substSize_substTy]; exact hF'.open_fvar X)
          simpa [Ty.substSize_substTy, Ty.substSize] using this
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
  case allT =>
    intro Δ κ B B' X C hX _ hk hk' ih hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | allT hB =>
      cases hR with
      | allT hB' =>
        refine .allT (SubKind.refl κ) hX ?_ (kinding_of_erase hk ?_ (.allT hB))
          (kinding_of_erase hk' ?_ (.allT hB'))
        · have := ih hcoh (by rw [Ty.substSize_substTy]; exact hB.open_fvar X)
            (by rw [Ty.substSize_substTy]; exact hB'.open_fvar X)
          simpa [Ty.substSize_substTy, Ty.substSize] using this
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
  case exT =>
    intro Δ κ B B' X C hX _ hk hk' ih hcoh hL hR
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | exT hB =>
      cases hR with
      | exT hB' =>
        refine .exT (SubKind.refl κ) hX ?_ (kinding_of_erase hk ?_ (.exT hB))
          (kinding_of_erase hk' ?_ (.exT hB'))
        · have := ih hcoh (by rw [Ty.substSize_substTy]; exact hB.open_fvar X)
            (by rw [Ty.substSize_substTy]; exact hB'.open_fvar X)
          simpa [Ty.substSize_substTy, Ty.substSize] using this
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
        · simp [Ty.eraseSz, Ty.eraseSz_substSize]
  case mu_pos =>
    intro Δ a b S S' X C hX hlist hpos hk hk' ihlist hcoh hL hR
    have hhead := hcoh.head
    simp only [SConstr.Holds, Bool.false_eq_true, if_false, if_true] at hhead
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | mu ha hS =>
      cases hR with
      | mu hb hS' =>
        obtain ⟨hlen, hfun⟩ := ihlist hcoh.tail
        refine .mu_pos (Or.inr hhead) (by simp [Ty.substSizeList_length, hlen]) hX
          (functors_sub hS hS' hfun) (positive_sub hS' hpos)
          (kinding_of_erase hk ?_ (.mu ha hS)) (kinding_of_erase hk' ?_ (.mu hb hS'))
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
  case mu_eqv =>
    intro Δ a b S S' X C₁ C₂ hX hlist₁ hlist₂ hk hk' ih₁ ih₂ hcoh hL hR
    have hhead := hcoh.head
    simp only [SConstr.Holds, Bool.false_eq_true, if_false, if_true] at hhead
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | mu ha hS =>
      cases hR with
      | mu hb hS' =>
        obtain ⟨hlen, hfun₁⟩ := ih₁ hcoh.tail.left
        obtain ⟨_, hfun₂⟩ := ih₂ hcoh.tail.right
        refine .mu_eqv (Or.inr hhead) (by simp [Ty.substSizeList_length, hlen]) hX
          (functors_sub hS hS' hfun₁) ?_
          (kinding_of_erase hk ?_ (.mu ha hS)) (kinding_of_erase hk' ?_ (.mu hb hS'))
        · intro c T T' hT hT'
          exact functors_sub hS' hS hfun₂ c T' T hT' hT
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
  case nu_pos =>
    intro Δ a b R R' X C hX hlist hpos hk hk' ihlist hcoh hL hR
    have hhead := hcoh.head
    simp only [SConstr.Holds, Bool.false_eq_true, if_false, if_true] at hhead
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | nu ha hS =>
      cases hR with
      | nu hb hS' =>
        obtain ⟨hlen, hfun⟩ := ihlist hcoh.tail
        refine .nu_pos (Or.inr hhead) (by simp [Ty.substSizeList_length, hlen]) hX
          (functors_sub hS hS' hfun) (positive_sub hS' hpos)
          (kinding_of_erase hk ?_ (.nu ha hS)) (kinding_of_erase hk' ?_ (.nu hb hS'))
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
  case nu_eqv =>
    intro Δ a b R R' X C₁ C₂ hX hlist₁ hlist₂ hk hk' ih₁ ih₂ hcoh hL hR
    have hhead := hcoh.head
    simp only [SConstr.Holds, Bool.false_eq_true, if_false, if_true] at hhead
    simp only [Ty.substSize] at hL hR ⊢
    cases hL with
    | nu ha hS =>
      cases hR with
      | nu hb hS' =>
        obtain ⟨hlen, hfun₁⟩ := ih₁ hcoh.tail.left
        obtain ⟨_, hfun₂⟩ := ih₂ hcoh.tail.right
        refine .nu_eqv (Or.inr hhead) (by simp [Ty.substSizeList_length, hlen]) hX
          (functors_sub hS hS' hfun₁) ?_
          (kinding_of_erase hk ?_ (.nu ha hS)) (kinding_of_erase hk' ?_ (.nu hb hS'))
        · intro c T T' hT hT'
          exact functors_sub hS' hS hfun₂ c T' T hT' hT
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
        · simp [Ty.eraseSz, Ty.eraseSzList_substSizeList]
  case nil =>
    intro Δ X _
    exact ⟨rfl, fun c T T' h _ => by simp at h⟩
  case cons =>
    intro Δ X T T' S S' C₁ C₂ _ _ ihT ihS hcoh
    obtain ⟨hlen, hS⟩ := ihS hcoh.right
    refine ⟨by simp [hlen], ?_⟩
    intro c U U' hU hU'
    cases c with
    | zero =>
      simp at hU hU'
      subst hU; subst hU'
      exact ihT hcoh.left
    | succ c => exact hS c U U' (by simpa using hU) (by simpa using hU')

end NishtAbel2024V5

/-! ## Solutions/V5/InfPat.lean -/

/-! # V5 inference: rigid variables of (co)patterns (Theorems 8 and 9) -/

namespace NishtAbel2024V5

/-! ## Theorems 8 and 9 -/

/-- Theorem 8: pattern inference yields pattern typing. -/
theorem inferPat_sound {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') : PatTy Ψ Θ p A Γ Ψ' Θ' := by
  induction h with
  | var => exact .var _ _ _ _
  | unit => exact .unit _ _
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | cons hc _ hj _ ih => exact .cons hc hj ih
  | pack hX _ ih => exact .packT hX ih

/-- Theorem 9: copattern-spine inference yields spine typing. -/
theorem inferSpine_sound {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    SpineTy Ψ Θ qs A Γ Ψ' Θ' C := by
  induction h with
  | nil => exact .nil _ _ _
  | pat hp _ ih => exact .pat (inferPat_sound hp) ih
  | proj hd _ hj _ ih => exact .proj hd hj ih
  | inst hX _ ih => exact .instT hX ih

/-! ## Flexible substitutions -/

/-- The domain of a flexible substitution consists of flexible names. -/
def FlexDom (φ : FlexSubst) : Prop := ∀ p ∈ φ, FlexName p.1

theorem FlexDom.lookup_rigid {φ : FlexSubst} (hφ : FlexDom φ) {i : Nat} (hi : RigidName i) :
    φ.lookup i = none := by
  cases hl : φ.lookup i with
  | none => rfl
  | some b =>
    have := hφ _ (lookup_mem_gen hl)
    simp [FlexName] at this
    simp [RigidName] at hi
    omega

theorem FlexDom.subst_rigid {φ : FlexSubst} (hφ : FlexDom φ) {i : Nat} (hi : RigidName i)
    (n : Nat) : (Size.var i n).subst φ = .var i n := by
  simp [Size.subst, hφ.lookup_rigid hi]

/-- Substituting into the types of a term context. -/
def TermCtx.substSize (φ : FlexSubst) (Γ : TermCtx) : TermCtx :=
  Γ.map fun p => (p.1, p.2.substSize φ)

@[simp] theorem TermCtx.substSize_append (φ : FlexSubst) (Γ₁ Γ₂ : TermCtx) :
    (Γ₁ ++ Γ₂).substSize φ = Γ₁.substSize φ ++ Γ₂.substSize φ := by
  simp [TermCtx.substSize]

theorem TermCtx.lookup_substSize (φ : FlexSubst) :
    ∀ (Γ : TermCtx) (x : Nat), (Γ.substSize φ).lookup x = (Γ.lookup x).map (Ty.substSize φ)
  | [], _ => rfl
  | (y, B) :: Γ, x => by
    by_cases h : x = y
    · subst h; simp [TermCtx.substSize, List.lookup]
    · have hb : (x == y) = false := by simpa using h
      have := TermCtx.lookup_substSize φ Γ x
      simp only [TermCtx.substSize] at this
      simp only [TermCtx.substSize, List.map_cons, List.lookup, hb]
      exact this

@[simp] theorem SizeCtx.substBounds_append (φ : FlexSubst) (Ψ₁ Ψ₂ : SizeCtx) :
    (Ψ₁ ++ Ψ₂).substBounds φ = Ψ₁.substBounds φ ++ Ψ₂.substBounds φ := by
  simp [SizeCtx.substBounds]

@[simp] theorem SizeCtx.substBounds_cons (φ : FlexSubst) (p : Nat × Size) (Ψ : SizeCtx) :
    SizeCtx.substBounds φ (p :: Ψ) = (p.1, p.2.subst φ) :: Ψ.substBounds φ := rfl

@[simp] theorem SizeCtx.substBounds_nil (φ : FlexSubst) : SizeCtx.substBounds φ [] = [] := rfl

theorem Ty.substSizeList_getElem?_some {σ : List (Nat × Size)} {S : List Ty} {c : Nat} {T : Ty}
    (h : S[c]? = some T) : (Ty.substSizeList σ S)[c]? = some (T.substSize σ) := by
  rw [Ty.substSizeList_getElem?, h]; rfl

/-- Pattern inference under a flexible substitution yields pattern typing. -/
theorem inferPat_subst {φ : FlexSubst} (hφ : FlexDom φ) {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat}
    {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx} (h : InferPat Ψ Θ p A Γ Ψ' Θ') :
    PatTy (Ψ.substBounds φ) Θ p (A.substSize φ) (Γ.substSize φ) (Ψ'.substBounds φ) Θ' := by
  induction h with
  | var Ψ Θ x A => exact .var _ _ _ _
  | unit Ψ Θ => exact .unit _ _
  | pair _ _ ih₁ ih₂ =>
    simp only [Ty.substSize, TermCtx.substSize_append, SizeCtx.substBounds_append]
    exact .pair ih₁ (by simpa using ih₂)
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hrig hj _ ih =>
    simp only [Ty.substSize, SizeCtx.substBounds_cons]
    refine .cons (Ty.substSizeList_getElem?_some hc)
      (by rwa [SizeCtx.substBounds_dom]) ?_
    have := ih
    rw [SizeCtx.substBounds_append, Ty.substSize_substTy] at this
    simpa [SizeCtx.substBounds, Ty.substSize, hφ.subst_rigid hrig] using this
  | @pack Ψ Ψ' Θ Θ' X κ p B Γ hX _ ih =>
    simp only [Ty.substSize]
    refine .packT hX ?_
    have := ih
    rw [Ty.substSize_substTy] at this
    simpa [Ty.substSize] using this

/-- Spine inference under a flexible substitution yields spine typing. -/
theorem inferSpine_subst {φ : FlexSubst} (hφ : FlexDom φ) {Ψ : SizeCtx} {Θ : TyCtx}
    {qs : List Copat} {A : Ty} {Γ : TermCtx} {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty}
    (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    SpineTy (Ψ.substBounds φ) Θ qs (A.substSize φ) (Γ.substSize φ) (Ψ'.substBounds φ) Θ'
      (C.substSize φ) := by
  induction h with
  | nil => exact .nil _ _ _
  | pat hp _ ih =>
    simp only [Ty.substSize, TermCtx.substSize_append, SizeCtx.substBounds_append]
    exact .pat (inferPat_subst hφ hp) (by simpa using ih)
  | @proj Ψ Ψ' Θ Θ' d j qs a R Rd C Γ hd hrig hj _ ih =>
    simp only [Ty.substSize, SizeCtx.substBounds_cons]
    refine .proj (Ty.substSizeList_getElem?_some hd) (by rwa [SizeCtx.substBounds_dom]) ?_
    have := ih
    rw [SizeCtx.substBounds_append, Ty.substSize_substTy] at this
    simpa [SizeCtx.substBounds, Ty.substSize, hφ.subst_rigid hrig] using this
  | @inst Ψ Ψ' Θ Θ' X κ qs B C Γ hX _ ih =>
    simp only [Ty.substSize]
    refine .instT hX ?_
    have := ih
    rw [Ty.substSize_substTy] at this
    simpa [Ty.substSize] using this

/-! ## Kinding of the outputs of spine typing -/

theorem patTy_kinding {Ψ : SizeCtx} {Θ : TyCtx} {p : Pat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} (h : PatTy Ψ Θ p A Γ Ψ' Θ') :
    KindingC Ψ Θ.toK A .star → TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ := by
  induction h with
  | var Ψ Θ x A =>
    intro hA q hq
    simp at hq; subst hq; simpa using hA
  | unit => intro _ q hq; simp at hq
  | @pair Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p q A B Γ₁ Γ₂ _ _ ih₁ ih₂ =>
    intro hAB
    obtain ⟨_, hA, hB⟩ := Kinding.inv_prod hAB
    have hΓ₁ := ih₁ hA
    have hΓ₂ := ih₂ (by rw [TyCtx.toK_append]; exact KindingC.mono_append hB)
    exact TermCtxWf.merge hΓ₁ hΓ₂
  | @cons Ψ Ψ' Θ Θ' c j p a S Sc Γ hc hj _ ih =>
    intro hA
    have hA' : KindingC (Ψ ++ [(j, a)]) Θ.toK (.mu a S) .star := hA.mono_append_sz
    have := ih (hA'.unfold_mu (TyCtx.toK_allMix Θ) (b := .var j 0) hc (sizeWf_fresh_var _ _ _))
    simpa using this
  | @packT Ψ Ψ' Θ Θ' X κ p B Γ hX _ ih =>
    intro hA
    have := ih (KindingC.open_fresh_ty (Kinding.inv_exT hA).2 hX)
    simpa using this
  | @packS Ψ Ψ' Θ Θ' j p a B Γ hj _ ih =>
    intro hA
    obtain ⟨_, _, hB⟩ := Kinding.inv_exS hA
    have := ih (KindingC.open_fresh_sz hB j a)
    simpa using this

theorem spineTy_kinding {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : SpineTy Ψ Θ qs A Γ Ψ' Θ' C) :
    KindingC Ψ Θ.toK A .star →
      TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ ∧ KindingC (Ψ ++ Ψ') (Θ ++ Θ').toK C .star := by
  induction h with
  | nil Ψ Θ A => intro hA; exact ⟨fun _ h => by simp at h, by simpa using hA⟩
  | @pat Ψ Ψ₁ Ψ₂ Θ Θ₁ Θ₂ p qs A B C Γ₁ Γ₂ hp _ ih =>
    intro hAB
    obtain ⟨_, hA, hB⟩ := Kinding.inv_arr hAB
    rw [(TyCtx.toK_allMix Θ).inv] at hA
    have hA' : KindingC Ψ Θ.toK A .star := by simpa using hA
    have hΓ₁ := patTy_kinding hp hA'
    obtain ⟨hΓ₂, hC⟩ := ih (by rw [TyCtx.toK_append]; exact KindingC.mono_append hB)
    exact ⟨TermCtxWf.merge hΓ₁ hΓ₂, by simpa using hC⟩
  | @proj Ψ Ψ' Θ Θ' d j qs a R Rd C Γ hd hj _ ih =>
    intro hA
    have hA' : KindingC (Ψ ++ [(j, a)]) Θ.toK (.nu a R) .star := hA.mono_append_sz
    obtain ⟨hΓ, hC⟩ := ih (hA'.unfold_nu (TyCtx.toK_allMix Θ) (b := .var j 0) hd
      (sizeWf_fresh_var _ _ _))
    exact ⟨by simpa using hΓ, by simpa using hC⟩
  | @instT Ψ Ψ' Θ Θ' X κ qs B C Γ hX _ ih =>
    intro hA
    obtain ⟨hΓ, hC⟩ := ih (KindingC.open_fresh_ty (Kinding.inv_allT hA).2 hX)
    exact ⟨by simpa using hΓ, by simpa using hC⟩
  | @instS Ψ Ψ' Θ Θ' j qs a B C Γ hj _ ih =>
    intro hA
    obtain ⟨_, _, hB⟩ := Kinding.inv_allS hA
    obtain ⟨hΓ, hC⟩ := ih (KindingC.open_fresh_sz hB j a)
    exact ⟨by simpa using hΓ, by simpa using hC⟩

end NishtAbel2024V5

/-! ## Solutions/V5/InfAux.lean -/

/-! # V5 inference: auxiliary facts about encodings, scopes and composed substitutions -/

namespace NishtAbel2024V5

/-! ## Well-formed sizes in larger contexts -/

theorem SizesWf.mono {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A) {Ψ' : SizeCtx}
    (hΨ : ∀ i ∈ Ψ.dom, i ∈ Ψ'.dom) : SizesWf Ψ' m A := by
  induction h with
  | unit => exact .unit _
  | prod _ _ ihA ihB => exact .prod ihA ihB
  | arr _ _ ihA ihB => exact .arr ihA ihB
  | var => exact .var _ _
  | fvar => exact .fvar _ _
  | lam _ ih => exact .lam ih
  | app _ _ ihF ihG => exact .app ihF ihG
  | mu ha _ ih => exact .mu (ha.weaken hΨ le_rfl) ih
  | nu ha _ ih => exact .nu (ha.weaken hΨ le_rfl) ih
  | allT _ ih => exact .allT ih
  | exT _ ih => exact .exT ih
  | allS ha _ ih => exact .allS (ha.weaken hΨ le_rfl) ih
  | exS ha _ ih => exact .exS (ha.weaken hΨ le_rfl) ih

/-! ## Encodings -/

theorem dom_append_right' {Ψ Ψ' : SizeCtx} : ∀ i ∈ Ψ'.dom, i ∈ (Ψ ++ Ψ').dom := by
  intro i hi
  simp only [SizeCtx.dom, List.map_append, List.mem_append]
  exact Or.inr hi

/-- The outputs of an encoding: same size erasure, sizes from the generated context, generated
names admissible, all bounds `∞`. -/
theorem encode_facts {πs : Pol} {ok : Nat → Prop} {π : Pol} {Δ : KCtx} {Δb : BCtx} {G G' : Ty}
    {Ψ : SizeCtx} (h : Encode πs ok π Δ Δb G Ψ G') :
    G'.eraseSz = G.eraseSz ∧ SizesWf Ψ 0 G' ∧ (∀ i ∈ Ψ.dom, ok i) ∧ (∀ p ∈ Ψ, p.2 = .inf 0) := by
  refine Encode.rec
    (motive_1 := fun _ _ _ G Ψ G' _ =>
      G'.eraseSz = G.eraseSz ∧ SizesWf Ψ 0 G' ∧ (∀ i ∈ Ψ.dom, ok i) ∧ (∀ p ∈ Ψ, p.2 = .inf 0))
    (motive_2 := fun _ _ _ S Ψ S' _ =>
      Ty.eraseSzList S' = Ty.eraseSzList S ∧ (∀ T ∈ S', SizesWf Ψ 0 T) ∧ (∀ i ∈ Ψ.dom, ok i) ∧
        (∀ p ∈ Ψ, p.2 = .inf 0))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · intros; exact ⟨rfl, .unit _, by simp [SizeCtx.dom], by simp⟩
  · intro π Δ Δb A B A' B' Ψ₁ Ψ₂ _ _ _ ih₁ ih₂
    refine ⟨by simp [Ty.eraseSz, ih₁.1, ih₂.1],
      .prod (ih₁.2.1.mono dom_append_left) (ih₂.2.1.mono dom_append_right'), ?_, ?_⟩
    · intro i hi
      simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁.2.2.1 i hi
      · exact ih₂.2.2.1 i hi
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih₁.2.2.2 p hp
      · exact ih₂.2.2.2 p hp
  · intro π Δ Δb A B A' B' Ψ₁ Ψ₂ _ _ _ ih₁ ih₂
    refine ⟨by simp [Ty.eraseSz, ih₁.1, ih₂.1],
      .arr (ih₁.2.1.mono dom_append_left) (ih₂.2.1.mono dom_append_right'), ?_, ?_⟩
    · intro i hi
      simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁.2.2.1 i hi
      · exact ih₂.2.2.1 i hi
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih₁.2.2.2 p hp
      · exact ih₂.2.2.2 p hp
  · intros; exact ⟨rfl, .var _ _, by simp [SizeCtx.dom], by simp⟩
  · intros; exact ⟨rfl, .fvar _ _, by simp [SizeCtx.dom], by simp⟩
  · intro π Δ Δb ι F F' Ψ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .lam ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intro π π' Δ Δb F G F' G' ι κ₁ κ₂ Ψ₁ Ψ₂ _ _ _ _ ih₁ ih₂
    refine ⟨by simp [Ty.eraseSz, ih₁.1, ih₂.1],
      .app (ih₁.2.1.mono dom_append_left) (ih₂.2.1.mono dom_append_right'), ?_, ?_⟩
    · intro i hi
      simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁.2.2.1 i hi
      · exact ih₂.2.2.1 i hi
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih₁.2.2.2 p hp
      · exact ih₂.2.2.2 p hp
  · intro π Δ Δb S S' Ψ i _ hok _ _ ih
    refine ⟨by simp [Ty.eraseSz, ih.1], .mu (by simp [SizeWfAt, SizeCtx.dom]) fun T hT =>
      (ih.2.1 T hT).mono (fun j hj => by simp [SizeCtx.dom] at hj ⊢; exact Or.inr hj), ?_, ?_⟩
    · intro j hj
      simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact hok
      · exact ih.2.2.1 j hj
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact ih.2.2.2 p hp
  · intro π Δ Δb S S' Ψ _ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .mu trivial ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intro π Δ Δb R R' Ψ i _ hok _ _ ih
    refine ⟨by simp [Ty.eraseSz, ih.1], .nu (by simp [SizeWfAt, SizeCtx.dom]) fun T hT =>
      (ih.2.1 T hT).mono (fun j hj => by simp [SizeCtx.dom] at hj ⊢; exact Or.inr hj), ?_, ?_⟩
    · intro j hj
      simp only [SizeCtx.dom, List.map_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact hok
      · exact ih.2.2.1 j hj
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · exact ih.2.2.2 p hp
  · intro π Δ Δb R R' Ψ _ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .nu trivial ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intro π Δ Δb κ B B' Ψ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .allT ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intro π Δ Δb κ B B' Ψ _ ih
    exact ⟨by simp [Ty.eraseSz, ih.1], .exT ih.2.1, ih.2.2.1, ih.2.2.2⟩
  · intros; exact ⟨rfl, fun _ h => by simp at h, by simp [SizeCtx.dom], by simp⟩
  · intro π Δ Δb T T' S S' Ψ₁ Ψ₂ _ _ _ ih₁ ih₂
    refine ⟨by simp [Ty.eraseSzList, ih₁.1, ih₂.1], ?_, ?_, ?_⟩
    · intro U hU
      rcases List.mem_cons.mp hU with rfl | hU
      · exact ih₁.2.1.mono dom_append_left
      · exact (ih₂.2.1 U hU).mono dom_append_right'
    · intro i hi
      simp only [SizeCtx.dom, List.map_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁.2.2.1 i hi
      · exact ih₂.2.2.1 i hi
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact ih₁.2.2.2 p hp
      · exact ih₂.2.2.2 p hp

/-! ## Scopes -/

theorem ScopeOK.left {φ : FlexSubst} {Φ₁ Φ₂ : List FlexVar} (h : ScopeOK φ (Φ₁ ++ Φ₂)) :
    ScopeOK φ Φ₁ := fun v hv => h v (List.mem_append_left _ hv)

theorem ScopeOK.right {φ : FlexSubst} {Φ₁ Φ₂ : List FlexVar} (h : ScopeOK φ (Φ₁ ++ Φ₂)) :
    ScopeOK φ Φ₂ := fun v hv => h v (List.mem_append_right _ hv)

theorem ScopeOK.tail {φ : FlexSubst} {v : FlexVar} {Φ : List FlexVar} (h : ScopeOK φ (v :: Φ)) :
    ScopeOK φ Φ := fun w hw => h w (List.mem_cons_of_mem _ hw)

theorem ScopeOK.var {φ : FlexSubst} {Φ : List FlexVar} (h : ScopeOK φ Φ) {v : FlexVar}
    (hv : v ∈ Φ) : SizeWf v.scope ((Size.var v.name 0).subst φ) := by
  obtain ⟨b, hb, hw⟩ := h v hv
  simp [Size.subst, hb, Size.shift_zero, hw]

theorem SizeWf.substBounds {Ψ : SizeCtx} {a : Size} (h : SizeWf Ψ a) (φ : FlexSubst) :
    SizeWf (Ψ.substBounds φ) a :=
  h.weaken (fun i hi => by rwa [SizeCtx.substBounds_dom]) le_rfl

theorem ScopeOK.encFlex {φ : FlexSubst} {Ψ ΨG : SizeCtx} (h : ScopeOK φ (encFlex Ψ ΨG)) :
    ∀ i ∈ ΨG.dom, SizeWf (Ψ.substBounds φ) ((Size.var i 0).subst φ) := by
  intro i hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  have := h.var (v := ⟨p.1, .mix, Ψ⟩) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  exact this.substBounds φ

theorem ScopeOK.callFlex {φ : FlexSubst} {Ψ : SizeCtx} {g : FunDecl} {as : List Nat}
    (h : ScopeOK φ (callFlex Ψ g as)) (hlen : as.length = g.sizeParams.length) :
    ∀ k ∈ as, SizeWf (Ψ.substBounds φ) ((Size.var k 0).subst φ) := by
  intro k hk
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hk
  have hn' : n < g.sizeParams.length := hlen ▸ hn
  have hmem : (g.sizeParams[n], as[n]) ∈ g.sizeParams.zip as := by
    rw [List.mem_iff_getElem]
    exact ⟨n, by simp [hn, hn'], by simp⟩
  have := h.var (v := ⟨as[n], paramPol g.ty (g.sizeParams[n]).1, Ψ⟩)
    (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  exact this.substBounds φ

/-! ## Composition of size substitutions -/

/-- Substituting after substituting: for sizes whose variables are all substituted. -/
theorem Size.subst_comp (σ φ : List (Nat × Size)) :
    ∀ a : Size, (∀ i ∈ a.fvars, (σ.lookup i).isSome) →
      (a.subst σ).subst φ = a.subst (σ.map fun p => (p.1, p.2.subst φ))
  | .inf _, _ => rfl
  | .bvar _ _, _ => rfl
  | .var i n, h => by
    have hi := h i (by simp [Size.fvars])
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hi
    have hb' : (σ.map fun p => (p.1, p.2.subst φ)).lookup i = some (b.subst φ) := by
      clear h hi
      induction σ with
      | nil => simp [List.lookup] at hb
      | cons q σ ih =>
        obtain ⟨y, c⟩ := q
        by_cases hiy : i = y
        · subst hiy; simp [List.lookup] at hb ⊢; rw [hb]
        · have hbe : (i == y) = false := by simpa using hiy
          simp only [List.lookup, hbe] at hb
          simp only [List.map_cons, List.lookup, hbe]
          exact ih hb
    simp only [Size.subst, hb, hb']
    exact Size.subst_shift b n
  | .meet a b, h => by
    simp only [Size.subst]
    rw [Size.subst_comp σ φ a (fun i hi => h i (by simp [Size.fvars, hi])),
      Size.subst_comp σ φ b (fun i hi => h i (by simp [Size.fvars, hi]))]

theorem SizeWfAt.fvars_dom {Ψ : SizeCtx} {m : Nat} :
    ∀ {a : Size}, SizeWfAt Ψ m a → ∀ i ∈ a.fvars, i ∈ Ψ.dom
  | .inf _, _, i, hi => by simp [Size.fvars] at hi
  | .var j _, h, i, hi => by simp [Size.fvars] at hi; subst hi; exact h
  | .bvar _ _, _, i, hi => by simp [Size.fvars] at hi
  | .meet _ _, h, i, hi => by
    simp only [Size.fvars, List.mem_append] at hi
    rcases hi with hi | hi
    · exact SizeWfAt.fvars_dom h.1 i hi
    · exact SizeWfAt.fvars_dom h.2 i hi

theorem Ty.substSize_comp {Ψ : SizeCtx} {m : Nat} {A : Ty} (h : SizesWf Ψ m A)
    (σ φ : List (Nat × Size)) (hσ : ∀ i ∈ Ψ.dom, (σ.lookup i).isSome) :
    (A.substSize σ).substSize φ = A.substSize (σ.map fun p => (p.1, p.2.subst φ)) := by
  induction h with
  | unit => rfl
  | prod _ _ ihA ihB => simp only [Ty.substSize, ihA, ihB]
  | arr _ _ ihA ihB => simp only [Ty.substSize, ihA, ihB]
  | var => rfl
  | fvar => rfl
  | lam _ ih => simp only [Ty.substSize, ih]
  | app _ _ ihF ihG => simp only [Ty.substSize, ihF, ihG]
  | @mu m a S ha hS ih =>
    simp only [Ty.substSize]
    rw [Size.subst_comp σ φ a (fun i hi => hσ i (SizeWfAt.fvars_dom ha i hi))]
    congr 1
    clear ha
    induction S with
    | nil => rfl
    | cons T S ihS =>
      simp only [Ty.substSizeList]
      rw [ih T (by simp), ihS (fun T' hT' => hS T' (by simp [hT']))
        (fun T' hT' => ih T' (by simp [hT']))]
  | @nu m a R ha hS ih =>
    simp only [Ty.substSize]
    rw [Size.subst_comp σ φ a (fun i hi => hσ i (SizeWfAt.fvars_dom ha i hi))]
    congr 1
    clear ha
    induction R with
    | nil => rfl
    | cons T R ihR =>
      simp only [Ty.substSizeList]
      rw [ih T (by simp), ihR (fun T' hT' => hS T' (by simp [hT']))
        (fun T' hT' => ih T' (by simp [hT']))]
  | allT _ ih => simp only [Ty.substSize, ih]
  | exT _ ih => simp only [Ty.substSize, ih]
  | allS ha _ ih =>
    simp only [Ty.substSize, ih]
    rw [Size.subst_comp σ φ _ (fun i hi => hσ i (SizeWfAt.fvars_dom ha i hi))]
  | exS ha _ ih =>
    simp only [Ty.substSize, ih]
    rw [Size.subst_comp σ φ _ (fun i hi => hσ i (SizeWfAt.fvars_dom ha i hi))]

theorem zip_map_snd (l : List Nat) (bs : List Size) (f : Size → Size) :
    (l.zip bs).map (fun p => (p.1, f p.2)) = l.zip (bs.map f) := by
  induction l generalizing bs with
  | nil => simp
  | cons x l ih =>
    cases bs with
    | nil => simp
    | cons b bs => simp [ih]

theorem zip_lookup_isSome (l : List Nat) (bs : List Size) (hlen : l.length ≤ bs.length) :
    ∀ i ∈ l, ((l.zip bs).lookup i).isSome := by
  induction l generalizing bs with
  | nil => intro i hi; simp at hi
  | cons x l ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      intro i hi
      by_cases hix : i = x
      · subst hix; simp
      · have hb : (i == x) = false := by simpa using hix
        simp only [List.zip_cons_cons, List.lookup, hb]
        exact ih bs (by simpa using hlen) i (by simpa [hix] using hi)

theorem SizeCtxWf.dom_nodup {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : Ψ.dom.Nodup := by
  induction h with
  | nil => simp [SizeCtx.dom]
  | @snoc Ψ i a _ hi _ ih =>
    simp only [SizeCtx.dom, List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro x hx y hy
    simp at hy; subst hy
    exact fun h => hi (h ▸ hx)

theorem SizeCtxWf.bound_wf {Ψ : SizeCtx} (h : SizeCtxWf Ψ) : ∀ p ∈ Ψ, SizeWf Ψ p.2 := by
  induction h with
  | nil => intro p hp; simp at hp
  | snoc _ _ ha ih => exact CtxBoundsWf.extend ih ha

theorem lookup_zip_getElem' : ∀ (l : List Nat) (as : List Size), l.Nodup → l.length = as.length →
    ∀ k (hk : k < l.length) (ha : k < as.length), (l.zip as).lookup (l[k]'hk) = some (as[k]'ha)
  | [], _, _, _, k, hk, _ => by simp at hk
  | _ :: _, [], _, h, _, _, _ => by simp at h
  | x :: l, a :: as, hnd, hlen, 0, _, _ => by simp
  | x :: l, a :: as, hnd, hlen, k + 1, hk, ha => by
    have hk' : k < l.length := by simp at hk; omega
    have ha' : k < as.length := by simp at ha; omega
    have hne : l[k]'hk' ≠ x := by
      intro h
      have := (List.nodup_cons.mp hnd).1
      exact this (h ▸ List.getElem_mem hk')
    have hb : (l[k]'hk' == x) = false := beq_eq_false_iff_ne.mpr hne
    have := lookup_zip_getElem' l as (List.nodup_cons.mp hnd).2 (by simpa using hlen) k hk' ha'
    simp only [List.zip_cons_cons, List.getElem_cons_succ, List.lookup_cons, hb]
    exact this

end NishtAbel2024V5

/-! ## Solutions/V5/InfSound.lean -/

/-! # V5 inference: Theorem 13 — coherent substitutions give typing derivations -/

namespace NishtAbel2024V5

/-- Well-formed signatures. -/
def DeclsWf (D : List FunDecl) : Prop :=
  ∀ g ∈ D, SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star

/-- Recorded calls into the block are admitted by the declarative environment. -/
def CallsOK (Ωd : TypingEnv) (φ : FlexSubst) (K : List CallRec) : Prop :=
  ∀ k ∈ K, Ωd.localOK (k.ctx.substBounds φ) k.callee (k.args.map (Size.subst φ))

theorem CallsOK.left {Ωd : TypingEnv} {φ : FlexSubst} {K₁ K₂ : List CallRec}
    (h : CallsOK Ωd φ (K₁ ++ K₂)) : CallsOK Ωd φ K₁ := fun k hk => h k (List.mem_append_left _ hk)

theorem CallsOK.right {Ωd : TypingEnv} {φ : FlexSubst} {K₁ K₂ : List CallRec}
    (h : CallsOK Ωd φ (K₁ ++ K₂)) : CallsOK Ωd φ K₂ :=
  fun k hk => h k (List.mem_append_right _ hk)

/-! ## Calls -/

theorem callBounds_mem {Ψ : SizeCtx} {g : FunDecl} {as : List Size} {k : Nat}
    (hk : k < g.sizeParams.length) (ha : k < as.length) :
    (⟨Ψ, as[k], (g.sizeParams[k]).2.subst (g.sizeParams.dom.zip as), true, false⟩ : SConstr) ∈
      callBounds Ψ g as := by
  unfold callBounds
  apply List.mem_map.mpr
  refine ⟨(g.sizeParams[k], as[k]), ?_, rfl⟩
  rw [List.mem_iff_getElem]
  exact ⟨k, by simp [hk, ha], by simp⟩

/-- The facts about an inferred call `g a⃗` under a coherent substitution. -/
theorem call_facts {φ : FlexSubst} {Ψ : SizeCtx} {Θ : TyCtx} {g : FunDecl} {as : List Nat}
    (hg : SizeCtxWf g.sizeParams ∧ KindingC g.sizeParams [] g.ty .star)
    (hlen : as.length = g.sizeParams.length) (hsc : ScopeOK φ (callFlex Ψ g as))
    (hcoh : Coherent φ (callBounds Ψ g (as.map fun k => .var k 0))) :
    let bs := (as.map fun k => Size.var k 0).map (Size.subst φ)
    (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0))).substSize φ =
        g.ty.substSize (g.sizeParams.dom.zip bs) ∧
      SizeSubstWf (Ψ.substBounds φ) bs g.sizeParams ∧
      KindingC (Ψ.substBounds φ) Θ.toK (g.ty.substSize (g.sizeParams.dom.zip bs)) .star := by
  intro bs
  obtain ⟨hwf, hk⟩ := hg
  have hdl : g.sizeParams.dom.length = g.sizeParams.length := by simp [SizeCtx.dom]
  have hlen' : (as.map fun k => Size.var k 0).length = g.sizeParams.length := by simp [hlen]
  have hsome : ∀ i ∈ g.sizeParams.dom,
      ((g.sizeParams.dom.zip (as.map fun k => Size.var k 0)).lookup i).isSome :=
    zip_lookup_isSome _ _ (by rw [hdl, hlen'])
  have hcomp : ∀ (σs : List Size), ((g.sizeParams.dom.zip (as.map fun k => Size.var k 0)).map
      fun p => (p.1, p.2.subst φ)) = g.sizeParams.dom.zip ((as.map fun k => Size.var k 0).map
        (Size.subst φ)) := fun _ => zip_map_snd _ _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [Ty.substSize_comp hk.sizesWf _ φ hsome, hcomp []]
  · refine ⟨by simp [bs, hlen], ?_⟩
    intro k hk' ha
    have hka : k < (as.map fun k => Size.var k 0).length := by simpa [hlen] using hk'
    have hc := hcoh _ (callBounds_mem (Ψ := Ψ) hk' hka)
    simp only [SConstr.Holds, if_true, Bool.false_eq_true, if_false] at hc
    have hbw : SizeWf g.sizeParams (g.sizeParams[k]).2 := hwf.bound_wf _ (List.getElem_mem hk')
    rw [Size.subst_comp _ φ _ (fun i hi => hsome i (SizeWfAt.fvars_dom hbw i hi)), hcomp []] at hc
    simpa [bs] using hc
  · have hσ : ∀ i ∈ g.sizeParams.dom, SizeWf (Ψ.substBounds φ)
        ((Size.var i 0).subst (g.sizeParams.dom.zip bs)) := by
      intro i hi
      obtain ⟨k, hk', rfl⟩ := List.getElem_of_mem hi
      have hkl : k < g.sizeParams.length := by simpa [SizeCtx.dom] using hk'
      have hkb : k < bs.length := by simp [bs, hlen, hkl]
      have hlk := lookup_zip_getElem' g.sizeParams.dom bs hwf.dom_nodup (by simp [bs, hdl, hlen]) k
        hk' hkb
      simp only [Size.subst, hlk, Size.shift_zero]
      have hka : k < as.length := by rw [hlen]; exact hkl
      have hmem : as[k] ∈ as := List.getElem_mem hka
      have := hsc.callFlex hlen as[k] hmem
      simpa [bs] using this
    have : KindingC (Ψ.substBounds φ) [] (g.ty.substSize (g.sizeParams.dom.zip bs)) .star :=
      Kinding.substSize hk hσ
    exact this.mono (fun _ h => h) (fun _ _ h => by simp at h)

/-! ## Theorem 13 -/

theorem inferSpine_rigid {Ψ : SizeCtx} {Θ : TyCtx} {qs : List Copat} {A : Ty} {Γ : TermCtx}
    {Ψ' : SizeCtx} {Θ' : TyCtx} {C : Ty} (h : InferSpine Ψ Θ qs A Γ Ψ' Θ' C) :
    ∀ i ∈ Ψ'.dom, RigidName i := by
  have hp : ∀ {Ψ Θ p A Γ Ψ' Θ'}, InferPat Ψ Θ p A Γ Ψ' Θ' → ∀ i ∈ Ψ'.dom, RigidName i := by
    intro Ψ Θ p A Γ Ψ' Θ' h
    induction h with
    | var => intro i hi; simp [SizeCtx.dom] at hi
    | unit => intro i hi; simp [SizeCtx.dom] at hi
    | pair _ _ ih₁ ih₂ =>
      intro i hi
      simp only [SizeCtx.dom_append, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih₁ i hi
      · exact ih₂ i hi
    | cons _ hr _ _ ih =>
      intro i hi
      simp only [SizeCtx.dom_cons, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact hr
      · exact ih i hi
    | pack _ _ ih => exact ih
  induction h with
  | nil => intro i hi; simp [SizeCtx.dom] at hi
  | pat hpat _ ih =>
    intro i hi
    simp only [SizeCtx.dom_append, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hp hpat i hi
    · exact ih i hi
  | proj _ hr _ _ ih =>
    intro i hi
    simp only [SizeCtx.dom_cons, List.mem_cons] at hi
    rcases hi with rfl | hi
    · exact hr
    · exact ih i hi
  | inst _ _ ih => exact ih

theorem TermCtxWf.substSize_lookup {Ψ : SizeCtx} {Θ : TyCtx} {Γ : TermCtx} {φ : FlexSubst}
    (h : TermCtxWf Ψ Θ (Γ.substSize φ)) {x : Nat} {A : Ty} (hx : Γ.lookup x = some A) :
    KindingC Ψ Θ.toK (A.substSize φ) .star := by
  have hx' : (Γ.substSize φ).lookup x = some (A.substSize φ) := by
    rw [TermCtx.lookup_substSize, hx]; rfl
  exact h _ (lookup_mem_ctx hx')

theorem TermCtxWf.prepend {Ψ Ψ' : SizeCtx} {Θ Θ' : TyCtx} {Γ Γ' : TermCtx}
    (hΓ' : TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') Γ') (hΓ : TermCtxWf Ψ Θ Γ) :
    TermCtxWf (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hΓ' p hp
  · rw [TyCtx.toK_append]
    exact (hΓ p hp).mono_append

/-- Encoded type arguments are well-kinded after the substitution. -/
theorem encoded_kinding {φ : FlexSubst} {Ψ : SizeCtx} {Θ : TyCtx} {G G' : Ty} {κ : Kind}
    {ΨG : SizeCtx} (hk : EKinding Θ.toK [] G κ)
    (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G') (hsc : ScopeOK φ (encFlex Ψ ΨG)) :
    KindingC (Ψ.substBounds φ) Θ.toK (G'.substSize φ) κ := by
  obtain ⟨herase, hsw, _, _⟩ := encode_facts henc
  refine kinding_of_erase hk ?_ (hsw.substSize hsc.encFlex)
  rw [Ty.eraseSz_substSize, herase]

/-- **Theorem 13** (soundness of coherent substitutions): a coherent, well-scoped flexible
substitution turns inference derivations into declarative typing derivations, provided the
recorded calls are admitted. -/
theorem inference_sound {Ω : InfEnv} {Ωd : TypingEnv} (hsig : Ωd.sig = Ω.sig)
    (hblock : Ωd.block = Ω.block) (hsigwf : DeclsWf Ω.sig) (hblockwf : DeclsWf Ω.block)
    {φ : FlexSubst} (hφ : FlexDom φ) :
    (∀ {Ψ Θ Γ t A Φ C T K}, InferTm Ω Ψ Θ Γ t A Φ C T K →
      Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star ∧
        ExprTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) t (A.substSize φ)) ∧
    (∀ {Ψ Θ Γ A t Φ C T K}, CheckTm Ω Ψ Θ Γ A t Φ C T K →
      Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ExprTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) t (A.substSize φ)) ∧
    (∀ {Ψ Θ Γ A cl Φ C T K}, CheckClause Ω Ψ Θ Γ A cl Φ C T K →
      Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) cl (A.substSize φ)) := by
  let P₁ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (t : Tm) (A : Ty) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec) (_ : InferTm Ω Ψ Θ Γ t A Φ C T K) =>
    Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star ∧
        ExprTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) t (A.substSize φ)
  let P₂ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (t : Tm) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec) (_ : CheckTm Ω Ψ Θ Γ A t Φ C T K) =>
    Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ExprTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) t (A.substSize φ)
  let P₃ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (D : List Clause)
      (Φ : List FlexVar) (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClauses Ω Ψ Θ Γ A D Φ C T K) =>
    Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ∀ cl ∈ D, ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) cl (A.substSize φ)
  let P₄ := fun (Ψ : SizeCtx) (Θ : TyCtx) (Γ : TermCtx) (A : Ty) (cl : Clause) (Φ : List FlexVar)
      (C : List SConstr) (T : List Nat) (K : List CallRec)
      (_ : CheckClause Ω Ψ Θ Γ A cl Φ C T K) =>
    Coherent φ C → ScopeOK φ Φ → CallsOK Ωd φ K →
      TermCtxWf (Ψ.substBounds φ) Θ (Γ.substSize φ) →
      KindingC (Ψ.substBounds φ) Θ.toK (A.substSize φ) .star →
        ClauseTy Ωd (Ψ.substBounds φ) Θ (Γ.substSize φ) cl (A.substSize φ)
  have sVar : ∀ {Ψ Θ Γ x A} (hx : Γ.lookup x = some A), P₁ Ψ Θ Γ (.var x) A [] [] [] []
      (.var hx) := by
    intro Ψ Θ Γ x A hx _ _ _ hΓ
    refine ⟨hΓ.substSize_lookup hx, .var ?_⟩
    rw [TermCtx.lookup_substSize, hx]; rfl
  have sApp : ∀ {Ψ Θ Γ r s A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hr : InferTm Ω Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁) (hs : CheckTm Ω Ψ Θ Γ A s Φ₂ C₂ T₂ K₂),
      P₁ Ψ Θ Γ r (.arr A B) Φ₁ C₁ T₁ K₁ hr → P₂ Ψ Θ Γ A s Φ₂ C₂ T₂ K₂ hs →
      P₁ Ψ Θ Γ (.app r (.term s)) B (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
        (.app hr hs) := by
    intro Ψ Θ Γ r s A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂ _ _ ihr ihs hcoh hsc hK hΓ
    obtain ⟨hkAB, hr⟩ := ihr hcoh.left hsc.left hK.left hΓ
    simp only [Ty.substSize] at hkAB hr
    obtain ⟨_, hA, hB⟩ := Kinding.inv_arr hkAB
    rw [(TyCtx.toK_allMix Θ).inv, BCtx.inv_nil] at hA
    exact ⟨hB, .app hr (ihs hcoh.right hsc.right hK.right hΓ hA)⟩
  have sProj : ∀ {Ψ Θ Γ r a R d j Rd Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.nu a R) Φ C T K)
      (hd : R[d]? = some Rd) (hj : FlexName j),
      P₁ Ψ Θ Γ r (.nu a R) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r (.proj d)) (Rd.substTy 0 (.nu (.var j 0) R))
        (⟨j, .neg, Ψ⟩ :: Φ) (⟨Ψ, .var j 0, a, true, true⟩ :: C)
        ((if Rd.hasBVar 0 then [] else [j]) ++ T) K (.proj hr hd hj) := by
    intro Ψ Θ Γ r a R d j Rd Φ C T K _ hd _ ihr hcoh hsc hK hΓ
    obtain ⟨hkR, hr⟩ := ihr hcoh.tail hsc.tail hK hΓ
    simp only [Ty.substSize] at hkR hr
    have hhead : SizeLt (Ψ.substBounds φ) ((Size.var j 0).subst φ) (a.subst φ).up := by
      simpa [SConstr.Holds] using hcoh.head
    have hd' := Ty.substSizeList_getElem?_some (σ := φ) hd
    have hkRd := hkR.unfold_nu (TyCtx.toK_allMix Θ) hd' hhead.wf.1
    rw [Ty.substSize_substTy]
    exact ⟨hkRd, .proj hr hd' hhead⟩
  have sInst : ∀ {Ψ Θ Γ r κ B G G' ΨG Φ C T K} (hr : InferTm Ω Ψ Θ Γ r (.allT κ B) Φ C T K)
      (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G'),
      P₁ Ψ Θ Γ r (.allT κ B) Φ C T K hr →
      P₁ Ψ Θ Γ (.app r .inst) (B.substTy 0 G') (encFlex Ψ ΨG ++ Φ) C T K
        (.inst hr hG hkG henc) := by
    intro Ψ Θ Γ r κ B G G' ΨG Φ C T K _ _ hkG henc ihr hcoh hsc hK hΓ
    obtain ⟨hkAll, hr⟩ := ihr hcoh hsc.right hK hΓ
    simp only [Ty.substSize] at hkAll hr
    have hkG' := encoded_kinding hkG henc hsc.left
    have hkB := Kinding.open_ty (Kinding.inv_allT hkAll).2 (TyCtx.toK_allMix Θ) hkG'
    rw [Ty.substSize_substTy]
    exact ⟨hkB, .instT hr hkG'⟩
  have sGlobal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.sig) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) [] []
        (.global hg hlen hflex) := by
    intro Ψ Θ Γ g as hg hlen _ hcoh hsc _ _
    obtain ⟨heq, hsub, hk⟩ := call_facts (Θ := Θ) (hsigwf g hg) hlen hsc hcoh
    rw [heq]
    exact ⟨hk, .globalFun (hsig ▸ hg) (hsigwf g hg).1 (hsigwf g hg).2 hsub hk⟩
  have sLocal : ∀ {Ψ Θ Γ g as} (hg : g ∈ Ω.block) (hlen : as.length = g.sizeParams.length)
      (hflex : ∀ k ∈ as, FlexName k),
      P₁ Ψ Θ Γ (.fn g.name) (g.ty.substSize (g.sizeParams.dom.zip (as.map fun k => .var k 0)))
        (callFlex Ψ g as) (callBounds Ψ g (as.map fun k => .var k 0)) []
        [⟨Ψ, g.name, as.map fun k => .var k 0⟩] (.local hg hlen hflex) := by
    intro Ψ Θ Γ g as hg hlen _ hcoh hsc hK _
    obtain ⟨heq, hsub, hk⟩ := call_facts (Θ := Θ) (hblockwf g hg) hlen hsc hcoh
    have hloc := hK ⟨Ψ, g.name, as.map fun k => .var k 0⟩ (by simp)
    rw [heq]
    exact ⟨hk, .localFun (hblock ▸ hg) (hblockwf g hg).1 (hblockwf g hg).2 hsub hk hloc⟩
  have sUnit : ∀ {Ψ Θ Γ}, P₂ Ψ Θ Γ .unit .unit [] [] [] [] .unit := by
    intro Ψ Θ Γ _ _ _ _ _
    exact .unit _ _ _
  have sPair : ∀ {Ψ Θ Γ t u A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (ht : CheckTm Ω Ψ Θ Γ A t Φ₁ C₁ T₁ K₁) (hu : CheckTm Ω Ψ Θ Γ B u Φ₂ C₂ T₂ K₂),
      P₂ Ψ Θ Γ A t Φ₁ C₁ T₁ K₁ ht → P₂ Ψ Θ Γ B u Φ₂ C₂ T₂ K₂ hu →
      P₂ Ψ Θ Γ (.prod A B) (.pair t u) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂)
        (.pair ht hu) := by
    intro Ψ Θ Γ t u A B Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂ _ _ iht ihu hcoh hsc hK hΓ hk
    simp only [Ty.substSize] at hk ⊢
    obtain ⟨_, hA, hB⟩ := Kinding.inv_prod hk
    exact .pair (iht hcoh.left hsc.left hK.left hΓ hA) (ihu hcoh.right hsc.right hK.right hΓ hB)
  have sCons : ∀ {Ψ Θ Γ c j t a S Sc Φ C T K} (hc : S[c]? = some Sc) (hj : FlexName j)
      (ht : CheckTm Ω Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K),
      P₂ Ψ Θ Γ (Sc.substTy 0 (.mu (.var j 0) S)) t Φ C T K ht →
      P₂ Ψ Θ Γ (.mu a S) (.cons c t) (⟨j, .pos, Ψ⟩ :: Φ)
        (⟨Ψ, .var j 0, a, true, true⟩ :: C) ((if Sc.hasBVar 0 then [] else [j]) ++ T) K
        (.cons hc hj ht) := by
    intro Ψ Θ Γ c j t a S Sc Φ C T K hc _ _ iht hcoh hsc hK hΓ hk
    simp only [Ty.substSize] at hk ⊢
    have hhead : SizeLt (Ψ.substBounds φ) ((Size.var j 0).subst φ) (a.subst φ).up := by
      simpa [SConstr.Holds] using hcoh.head
    have hc' := Ty.substSizeList_getElem?_some (σ := φ) hc
    have hkSc := hk.unfold_mu (TyCtx.toK_allMix Θ) hc' hhead.wf.1
    have hkSc' : KindingC (Ψ.substBounds φ) Θ.toK
        ((Sc.substTy 0 (.mu (.var j 0) S)).substSize φ) .star := by
      simpa [Ty.substSize_substTy, Ty.substSize] using hkSc
    have ht := iht hcoh.tail hsc.tail hK hΓ hkSc'
    rw [Ty.substSize_substTy] at ht
    exact .cons hc' hhead hk (by simpa [Ty.substSize] using ht)
  have sPack : ∀ {Ψ Θ Γ t κ B G G' ΨG Φ C T K} (hG : Unsized G) (hkG : EKinding Θ.toK [] G κ)
      (henc : Encode .mix FlexName .mix Θ.toK [] G ΨG G')
      (ht : CheckTm Ω Ψ Θ Γ (B.substTy 0 G') t Φ C T K),
      P₂ Ψ Θ Γ (B.substTy 0 G') t Φ C T K ht →
      P₂ Ψ Θ Γ (.exT κ B) (.pack t) (encFlex Ψ ΨG ++ Φ) C T K (.pack hG hkG henc ht) := by
    intro Ψ Θ Γ t κ B G G' ΨG Φ C T K _ hkG henc _ iht hcoh hsc hK hΓ hk
    simp only [Ty.substSize] at hk ⊢
    have hkG' := encoded_kinding hkG henc hsc.left
    have hkB := Kinding.open_ty (Kinding.inv_exT hk).2 (TyCtx.toK_allMix Θ) hkG'
    rw [← Ty.substSize_substTy] at hkB
    have ht := iht hcoh hsc.right hK hΓ hkB
    rw [Ty.substSize_substTy] at ht
    exact .packT hk hkG' ht
  have sLam : ∀ {Ψ Θ Γ A D Φ C T K} (hD : CheckClauses Ω Ψ Θ Γ A D Φ C T K),
      P₃ Ψ Θ Γ A D Φ C T K hD → P₂ Ψ Θ Γ A (.lam D) Φ C T K (.lam hD) := by
    intro Ψ Θ Γ A D Φ C T K _ ih hcoh hsc hK hΓ hk
    exact .lam hk (ih hcoh hsc hK hΓ hk)
  have sSub : ∀ {Ψ Θ Γ r A B Φ C₁ C₂ T K} (hr : InferTm Ω Ψ Θ Γ r A Φ C₁ T K)
      (hcmp : Compare Ψ Θ.toK A B .star C₂),
      P₁ Ψ Θ Γ r A Φ C₁ T K hr → P₂ Ψ Θ Γ B r Φ (C₁ ++ C₂) T K (.sub hr hcmp) := by
    intro Ψ Θ Γ r A B Φ C₁ C₂ T K _ hcmp ihr hcoh hsc hK hΓ hkB
    obtain ⟨hkA, hr⟩ := ihr hcoh.left hsc hK hΓ
    have hsub := compare_sound hcmp hcoh.right hkA.sizesWf hkB.sizesWf
    exact .sub hr hsub hkB
  have sNil : ∀ {Ψ Θ Γ A}, P₃ Ψ Θ Γ A [] [] [] [] [] .nil := by
    intro Ψ Θ Γ A _ _ _ _ _ cl hcl
    simp at hcl
  have sConsCl : ∀ {Ψ Θ Γ A cl D Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂}
      (hcl : CheckClause Ω Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁)
      (hD : CheckClauses Ω Ψ Θ Γ A D Φ₂ C₂ T₂ K₂),
      P₄ Ψ Θ Γ A cl Φ₁ C₁ T₁ K₁ hcl → P₃ Ψ Θ Γ A D Φ₂ C₂ T₂ K₂ hD →
      P₃ Ψ Θ Γ A (cl :: D) (Φ₁ ++ Φ₂) (C₁ ++ C₂) (T₁ ++ T₂) (K₁ ++ K₂) (.cons hcl hD) := by
    intro Ψ Θ Γ A cl D Φ₁ Φ₂ C₁ C₂ T₁ T₂ K₁ K₂ _ _ ih₁ ih₂ hcoh hsc hK hΓ hk cl' hcl'
    rcases List.mem_cons.mp hcl' with rfl | hcl'
    · exact ih₁ hcoh.left hsc.left hK.left hΓ hk
    · exact ih₂ hcoh.right hsc.right hK.right hΓ hk cl' hcl'
  have sClause : ∀ {Ψ Ψ' Θ Θ' Γ Γ' A C qs t Φ Cs T K}
      (hsp : InferSpine Ψ Θ qs A Γ' Ψ' Θ' C)
      (ht : CheckTm Ω (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K),
      P₂ (Ψ ++ Ψ') (Θ ++ Θ') (Γ' ++ Γ) C t Φ Cs T K ht →
      P₄ Ψ Θ Γ A (.mk qs t) Φ Cs T K (.mk hsp ht) := by
    intro Ψ Ψ' Θ Θ' Γ Γ' A C qs t Φ Cs T K hsp _ iht hcoh hsc hK hΓ hkA
    have hsp' := inferSpine_subst hφ hsp
    obtain ⟨hΓ', hkC⟩ := spineTy_kinding hsp' hkA
    have ht := iht hcoh hsc hK
      (by simpa [SizeCtx.substBounds_append, TermCtx.substSize_append] using hΓ'.prepend hΓ)
      (by simpa [SizeCtx.substBounds_append] using hkC)
    simp only [SizeCtx.substBounds_append, TermCtx.substSize_append] at ht
    exact .mk hsp' ht
  exact ⟨fun h => @InferTm.rec Ω P₁ P₂ P₃ P₄ sVar sApp sProj sInst sGlobal sLocal sUnit sPair
      sCons sPack sLam sSub sNil sConsCl sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckTm.rec Ω P₁ P₂ P₃ P₄ sVar sApp sProj sInst sGlobal sLocal sUnit sPair
      sCons sPack sLam sSub sNil sConsCl sClause _ _ _ _ _ _ _ _ _ h,
    fun h => @CheckClause.rec Ω P₁ P₂ P₃ P₄ sVar sApp sProj sInst sGlobal sLocal sUnit sPair
      sCons sPack sLam sSub sNil sConsCl sClause _ _ _ _ _ _ _ _ _ h⟩

end NishtAbel2024V5


