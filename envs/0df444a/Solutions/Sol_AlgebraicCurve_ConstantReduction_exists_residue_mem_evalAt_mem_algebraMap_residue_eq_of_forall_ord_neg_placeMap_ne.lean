-- Prove2me | solution 1 for AlgebraicCurve.ConstantReduction.exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/57075a24-6dd2-5093-94e0-facbe7a76fa6

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_FinitePlaceLift
import Theorems.Thm_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem solution
    {L : Type} [Field L] {A : ValuationSubring L}
    {F : Type} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : ConstantReduction A F Fbar)
    (P : Place L F) (hP : P.IsRational)
    (f : F) (hf : f ∈ R.integers) (hfP : f ∈ P.toValuationSubring)
    (hpole : ∀ P' : Place L F, P'.ord f < 0 → R.placeMap P' ≠ R.placeMap P) :
    ∃ (hm : R.residue ⟨f, hf⟩ ∈ (R.placeMap P).toValuationSubring) (h : P.evalAt f ∈ A),
      algebraMap (ResidueField ↥A) (R.placeMap P).ResidueField (IsLocalRing.residue ↥A ⟨P.evalAt f, h⟩) =
        IsLocalRing.residue ↥(R.placeMap P).toValuationSubring ⟨R.residue ⟨f, hf⟩, hm⟩ := by

  have hfib : ∀ w : Place L F, R.placeMap w = R.placeMap P → f ∈ w.toValuationSubring := by
    intro w hw
    by_contra hmem
    have hf0 : f ≠ 0 := fun h0 => hmem (h0 ▸ zero_mem _)
    have hneg : w.ord f < 0 := by
      by_contra hle
      exact hmem (w.mem_toValuationSubring_of_ord_nonneg_alt hf0 (not_lt.mp hle))
    exact hpole w hneg hw
  exact AlgebraicCurve.ConstantReduction.isPointwise_of_hasPrincipalDivisors R P hP f hf hfib

end S_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne
end P2MW
export P2MW.S_AlgebraicCurve_ConstantReduction_exists_residue_mem_evalAt_mem_algebraMap_residue_eq_of_forall_ord_neg_placeMap_ne (solution)
