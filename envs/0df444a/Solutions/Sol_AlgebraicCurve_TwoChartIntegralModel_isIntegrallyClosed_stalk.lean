-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/34ec2d0c-3c8e-5cfa-82df-e41449979be9

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

open AlgebraicCurve.TwoChartIntegralModel in

theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    IsIntegrallyClosed ↑((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk x) := by

  have hSpec : ∀ (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
      (y : ↥(Spec (CommRingCat.of A))), IsIntegrallyClosed ↑((Spec (CommRingCat.of A)).presheaf.stalk y) := by
    intro A _ _ _ y
    haveI : IsIntegrallyClosed (Localization.AtPrime y.asIdeal) :=
      isIntegrallyClosed_of_isLocalization (R := A) (Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl
        y.asIdeal.primeCompl_le_nonZeroDivisors
    exact .of_equiv (Spec.stalkIso (CommRingCat.of A) y).commRingCatIsoToRingEquiv.symm
  haveI := isIntegrallyClosed_chartAlg R F ({j} : Set F)
  haveI := isIntegrallyClosed_chartAlg R F ({j⁻¹} : Set F)
  rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · haveI := hSpec (chartAlgFin R F j) a
    exact .of_equiv (asIso ((ιFin R F j).stalkMap a)).commRingCatIsoToRingEquiv.symm
  · haveI := hSpec (chartAlgInf R F j) a
    exact .of_equiv (asIso ((ιInf R F j).stalkMap a)).commRingCatIsoToRingEquiv.symm

end S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk (solution)
