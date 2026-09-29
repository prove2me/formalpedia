-- Prove2me | solution 1 for AlgebraicCurve.instIsCurveOverRatFunc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2e277df9-23df-5248-a593-e0806acb6186

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_ofHeightOneSpectrum_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors"
p2m_open "AlgebraicCurve"

scoped instance instHasPrincipalDivisorsRatFuncLaneB (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) :=
  RationalFunctionField.hasPrincipalDivisors K
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve"

section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ResidueField deg FiniteResidue ofHeightOneSpectrum FiniteResidue.finite"
p2m_open "AlgebraicCurve.Place"

section DegPos

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem finiteResidue_of_deg_pos (h : 0 < v.deg) : v.FiniteResidue :=
  ⟨Module.finite_of_finrank_pos h⟩
end DegPos
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "exists_irreducible_span deg_ofHeightOneSpectrum placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty deg_placeInfty hasPrincipalDivisors"
p2m_open "AlgebraicCurve.RationalFunctionField"
variable (K : Type*) [Field K]

scoped instance instFiniteResidueOfHeightOneSpectrum (w : HeightOneSpectrum K[X]) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).FiniteResidue := by
  obtain ⟨p, hp, hw⟩ := exists_irreducible_span K w
  refine Place.finiteResidue_of_deg_pos _ ?_
  rw [deg_ofHeightOneSpectrum K hw]
  exact hp.natDegree_pos

scoped instance instFiniteResiduePlaceInfty [DecidableEq (RatFunc K)] :
    (placeInfty K).FiniteResidue :=
  Place.finiteResidue_of_deg_pos _ (by rw [deg_placeInfty K]; exact one_pos)

variable {K} in

scoped instance instFiniteResidue (v : Place K (RatFunc K)) : v.FiniteResidue := by
  classical
  rcases eq_ofHeightOneSpectrum_or_eq_placeInfty v with ⟨w, rfl⟩ | rfl
  · exact instFiniteResidueOfHeightOneSpectrum K w
  · exact instFiniteResiduePlaceInfty K

end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"

namespace Place
p2m_export "AlgebraicCurve.Place" "ResidueField deg FiniteResidue ofHeightOneSpectrum FiniteResidue.finite"
p2m_open "AlgebraicCurve.Place"

section Restrict

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')
end Restrict
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end Place
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"

section

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors"
p2m_open "AlgebraicCurve"

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def KaehlerRankOne : Prop :=
  Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

variable {K F}
namespace IsCurveOver p2m_export "AlgebraicCurve.IsCurveOver" "hasPrincipalDivisors instFiniteResidue finiteResidue kaehler_free_rank_one" end IsCurveOver
p2m_open_scoped "AlgebraicCurve.IsCurveOver" in

theorem IsCurveOver.of_finiteResidue_of_kaehlerRankOne
    [HasPrincipalDivisors K F] [∀ v : Place K F, v.FiniteResidue]
    (hΩ : KaehlerRankOne K F) : IsCurveOver K F where
  finiteResidue v := Place.FiniteResidue.finite (v := v)
  kaehler_free_rank_one := hΩ

namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "exists_irreducible_span deg_ofHeightOneSpectrum placeInfty eq_ofHeightOneSpectrum_or_eq_placeInfty deg_placeInfty hasPrincipalDivisors"
p2m_open "AlgebraicCurve.RationalFunctionField"

variable (K : Type*) [Field K]

theorem isCurveOver_of_kaehlerRankOne (hΩ : KaehlerRankOne K (RatFunc K)) :
    IsCurveOver K (RatFunc K) :=
  IsCurveOver.of_finiteResidue_of_kaehlerRankOne hΩ
end RationalFunctionField
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
variable (K F)
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
section AxiomAudit
end AxiomAudit
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"

section

set_option autoImplicit false

noncomputable section

p2m_open "IntermediateField AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve Polynomial TensorProduct Module"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Place.FiniteResidue HasPrincipalDivisors Place.ofHeightOneSpectrum Place.FiniteResidue.finite RationalFunctionField.hasPrincipalDivisors"
p2m_open "AlgebraicCurve"

variable (K : Type*) [Field K]

def kaehlerPolynomialBasis : Basis Unit K[X] Ω[K[X]⁄K] :=
  (Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

scoped instance instFormallyEtalePolynomialRatFunc : Algebra.FormallyEtale K[X] (RatFunc K) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])

def kaehlerRatFuncBasis : Basis Unit (RatFunc K) Ω[(RatFunc K)⁄K] :=
  ((kaehlerPolynomialBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem kaehlerRankOne_ratFunc : KaehlerRankOne K (RatFunc K) :=
  ⟨Module.Free.of_basis (kaehlerRatFuncBasis K),
    (Module.finrank_eq_card_basis (kaehlerRatFuncBasis K)).trans (by simp)⟩

scoped instance instIsCurveOverRatFunc : IsCurveOver K (RatFunc K) :=
  RationalFunctionField.isCurveOver_of_kaehlerRankOne K (kaehlerRankOne_ratFunc K)

variable {F : Type*} [Field F] [Algebra K F]
variable {K}
variable (K F)
variable {K F}
end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
namespace ModularCurve
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve"
variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
end ModularCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
section Gates
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.ModularCurve"
variable (K : Type*) [Field K]
end Gates
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"
end
p2m_reactivate "P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc.AlgebraicCurve.RationalFunctionField"

theorem solution (K : Type*) [Field K] : AlgebraicCurve.IsCurveOver K (RatFunc K) :=
  AlgebraicCurve.instIsCurveOverRatFunc K

end
end
end
end S_AlgebraicCurve_instIsCurveOverRatFunc
end P2MW
export P2MW.S_AlgebraicCurve_instIsCurveOverRatFunc (solution)
