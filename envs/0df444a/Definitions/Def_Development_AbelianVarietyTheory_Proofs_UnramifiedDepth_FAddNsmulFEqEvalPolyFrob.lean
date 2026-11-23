-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FAddNsmulFEqEvalPolyFrob
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FAddNsmulFEqEvalPolyFrob
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:48.08116+00:00
-- url     : https://prove2.me/theorems/c852f120-a806-4027-ad82-e8029e0f5ae0
-- title:
--   FAdd Nsmul FEq Eval Poly Frob
-- statement:
--   Definitions and structural lemmas for FAdd Nsmul FEq Eval Poly Frob, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FAddNsmulFEqEvalPolyFrob.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_PSerFrobStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
def btPolySub (p : ℕ) (g : ℕ) (W : Type) [CommRing W] :
    Subalgebra W (MvPolynomial (Fin g) W) where
  carrier := {q | ∀ m : Fin g →₀ ℕ, (∃ i, ¬ p ∣ m i) →
    MvPolynomial.coeff m q ∈ Ideal.span {(p : W)}}
  add_mem' := by
    intro a b ha hb m hm
    rw [MvPolynomial.coeff_add]
    exact Ideal.add_mem _ (ha m hm) (hb m hm)
  mul_mem' := by
    intro a b ha hb m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    by_cases h1 : p ∣ x.1 i
    · refine Ideal.mul_mem_left _ _ (hb _ ⟨i, fun h2 => hi ?_⟩)
      rw [← hx', Finsupp.add_apply]
      exact dvd_add h1 h2
    · exact Ideal.mul_mem_right _ _ (ha _ ⟨i, h1⟩)
  algebraMap_mem' := by
    intro r m hm
    obtain ⟨i, hi⟩ := hm
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C, if_neg]
    · exact Ideal.zero_mem _
    · rintro rfl
      exact hi (by simp)
end GlobalTheory


