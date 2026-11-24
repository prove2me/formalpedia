-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SigmaSplitSymmInl
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SigmaSplitSymmInl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:59.489219+00:00
-- url     : https://prove2.me/theorems/c271ec96-2eed-41c9-a85b-749bbb4473e9
-- title:
--   Sigma Split Symm Inl
-- statement:
--   Definitions and structural lemmas for Sigma Split Symm Inl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SigmaSplitSymmInl.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.InnerAutomorphism
section Inner
variable {A : Type*} (R : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
def innerAut (u : Aˣ) : A ≃ₐ[R] A where
  toFun x := (u : A) * x * ((u⁻¹ : Aˣ) : A)
  invFun x := ((u⁻¹ : Aˣ) : A) * x * (u : A)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one]
@[simp] theorem innerAut_apply (u : Aˣ) (x : A) :
    innerAut R u x = (u : A) * x * ((u⁻¹ : Aˣ) : A) := rfl
end Inner
section Bounded
variable {K n : Type*} [NormedField K]
def EntriesBounded (M : Matrix n n K) (c : ℝ) : Prop :=
  ∀ i j, ‖M i j‖ ≤ c
end Bounded
section DropLast
variable (K : Type*) [Semiring K] (d : ℕ)
def dropLast : (Fin (d + 1) → K) →ₗ[K] (Fin d → K) where
  toFun x i := x i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
@[simp] theorem dropLast_apply (x : Fin (d + 1) → K) (i : Fin d) :
    dropLast K d x i = x i.castSucc := rfl
end DropLast
section Split
variable {ι : Type*} [DecidableEq ι] (F : ι → Type*)
def sigmaSplit (j : ι) : (Σ i, F i) ≃ F j ⊕ (Σ i : {i // i ≠ j}, F i.1) where
  toFun p := if h : p.1 = j then Sum.inl (h ▸ p.2) else Sum.inr ⟨⟨p.1, h⟩, p.2⟩
  invFun s := Sum.elim (fun x => ⟨j, x⟩) (fun q => ⟨q.1.1, q.2⟩) s
  left_inv := by
    rintro ⟨i, x⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  right_inv := by
    rintro (x | ⟨⟨i, hi⟩, x⟩)
    · simp
    · simp [show ¬ i = j from hi]
end Split
end GlobalTheory.InnerAutomorphism


