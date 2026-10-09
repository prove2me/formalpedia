-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GenericInfinityComparison_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GenericInfinityComparison_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T23:07:20.12832+00:00
-- url     : https://prove2.me/theorems/b5be01c5-fcd6-438b-8731-e97cd742d7cf
-- title:
--   FLT.Assumptions.MazurProof.N13GenericInfinityComparison source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GenericInfinityComparison

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GenericInfinityComparison
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityIdealApproximation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalizationAdicPatch_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
Uncompiled source candidate; all Lean and axiom checks NOT RUN.

Actual two-branch equality now yields the required approximation predicates
on the generic ordinary infinity chart. The vertical scalars are cancelled
only after localizing them. Combined with the actual principal open D(t),
this proves generic infinity-ideal equality.
-/

namespace MazurProof.N13GenericInfinityComparison

noncomputable section
open N13InfinityBranchJets N13InfinityIdealApproximation
open scoped nonZeroDivisors
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def verticalScalars : Submonoid B := (nonZeroDivisors R₂).map (algebraMap R₂ B)
abbrev GenericInfinity := Localization verticalScalars
def genericT : GenericInfinity := algebraMap B GenericInfinity N13IntegralInfinityChart.tClass
abbrev GenericOverlap := Localization.Away genericT

theorem approximations_of_branch_eq
    (I J : Ideal B)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (z : GenericInfinity) (hz : z ∈ Ideal.map (algebraMap B GenericInfinity) I) (n : ℕ) :
    ∃ w : GenericInfinity,
      z - genericT ^ n * w ∈ Ideal.map (algebraMap B GenericInfinity) J := by
  obtain ⟨⟨x, s⟩, hsz⟩ :=
    (IsLocalization.mem_map_algebraMap_iff verticalScalars GenericInfinity).mp hz
  obtain ⟨c, hc, y, hy⟩ := scaled_approximations_of_branch_eq I J hp hm x x.property n
  let sc : verticalScalars :=
    ⟨algebraMap R₂ B c, ⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc, rfl⟩⟩
  have hunit : IsUnit
      (algebraMap B GenericInfinity (algebraMap R₂ B c) *
        algebraMap B GenericInfinity (s : B)) :=
    (IsLocalization.map_units GenericInfinity sc).mul
      (IsLocalization.map_units GenericInfinity s)
  let u : GenericInfinityˣ := hunit.unit
  have hu : (u : GenericInfinity) =
      algebraMap B GenericInfinity (algebraMap R₂ B c) *
        algebraMap B GenericInfinity (s : B) := hunit.unit_spec
  let Jg := Ideal.map (algebraMap B GenericInfinity) J
  have hscaled : (u : GenericInfinity) * z - genericT ^ n * algebraMap B GenericInfinity y ∈ Jg := by
    have hmap := Ideal.mem_map_of_mem (algebraMap B GenericInfinity) hy
    convert hmap using 1
    simp only [genericT, map_sub, map_mul, map_pow, hu]
    rw [← hsz]
    ring
  refine ⟨(↑(u⁻¹) : GenericInfinity) * algebraMap B GenericInfinity y, ?_⟩
  have hmul := Jg.mul_mem_left (↑(u⁻¹) : GenericInfinity) hscaled
  have heq : (↑(u⁻¹) : GenericInfinity) *
      ((u : GenericInfinity) * z - genericT ^ n * algebraMap B GenericInfinity y) =
      z - genericT ^ n * ((↑(u⁻¹) : GenericInfinity) * algebraMap B GenericInfinity y) := by
    calc
      _ = ((↑(u⁻¹) : GenericInfinity) * (u : GenericInfinity)) * z -
          genericT ^ n * ((↑(u⁻¹) : GenericInfinity) * algebraMap B GenericInfinity y) := by ring
      _ = _ := by rw [Units.inv_mul, one_mul]
  rwa [heq] at hmul

/-- For the actual generic ordinary infinity chart, equality on D(t) and
equality under BOTH actual generic Hensel-branch maps imply ideal equality.
The formerly missing approximation hypotheses are proved above. -/
theorem generic_ideal_eq_of_overlap_and_branches
    (I J : Ideal B)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (hAway :
      Ideal.map (algebraMap GenericInfinity GenericOverlap)
          (Ideal.map (algebraMap B GenericInfinity) I) =
        Ideal.map (algebraMap GenericInfinity GenericOverlap)
          (Ideal.map (algebraMap B GenericInfinity) J)) :
    Ideal.map (algebraMap B GenericInfinity) I = Ideal.map (algebraMap B GenericInfinity) J := by
  apply N13LocalizationAdicPatch.ideal_eq_of_localization_eq_of_approximations genericT _ _ hAway
  · intro z hz n
    exact approximations_of_branch_eq I J hp hm z hz n
  · intro z hz n
    exact approximations_of_branch_eq J I hp.symm hm.symm z hz n

/-- Actual integral infinity-ideal equality follows as well when both
ideals are invertible and have nonzero reductions. Vertical denominators
are cancelled using the proved reduction-saturation theorem. -/
theorem integral_ideal_eq_of_overlap_and_branches
    (I J : Ideal B)
    (hI : IsUnit (I : N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
    (hJ : IsUnit (J : N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
    (hIr : Ideal.map N13IntegralInfinityReduction.reduceCoordinate I ≠ ⊥)
    (hJr : Ideal.map N13IntegralInfinityReduction.reduceCoordinate J ≠ ⊥)
    (hp : Ideal.map N13InfinityChartMarking.positiveExpansion I =
      Ideal.map N13InfinityChartMarking.positiveExpansion J)
    (hm : Ideal.map N13InfinityChartMarking.negativeExpansion I =
      Ideal.map N13InfinityChartMarking.negativeExpansion J)
    (hAway :
      Ideal.map (algebraMap GenericInfinity GenericOverlap)
          (Ideal.map (algebraMap B GenericInfinity) I) =
        Ideal.map (algebraMap GenericInfinity GenericOverlap)
          (Ideal.map (algebraMap B GenericInfinity) J)) : I = J := by
  have hg := generic_ideal_eq_of_overlap_and_branches I J hp hm hAway
  have descend (U V : Ideal B)
      (hV : IsUnit (V : N13IntegralInfinityPointSpread.InfinityFractionalIdeal))
      (hVr : Ideal.map N13IntegralInfinityReduction.reduceCoordinate V ≠ ⊥)
      (hmap : Ideal.map (algebraMap B GenericInfinity) U =
        Ideal.map (algebraMap B GenericInfinity) V) : U ≤ V := by
    intro x hx
    have hm := Ideal.mem_map_of_mem (algebraMap B GenericInfinity) hx
    rw [hmap, IsLocalization.algebraMap_mem_map_algebraMap_iff verticalScalars] at hm
    obtain ⟨q, hq, hqx⟩ := hm
    obtain ⟨r, hr, hqr⟩ := hq
    rw [← hqr] at hqx
    exact N13InvertibleReductionSaturation.twoAdic_scalar_saturated_of_reduction_ne_bot
      (K := N13IntegralInfinityPointSpread.FunctionField)
      N13IntegralInfinityReduction.reduceCoordinate
      N13InvertibleReductionSaturation.infinity_two_ne_zero
      N13IntegralInfinityReduction.ker_reduceCoordinate V hV hVr
      r (mem_nonZeroDivisors_iff_ne_zero.mp hr) x hqx
  exact le_antisymm (descend I J hJ hJr hg) (descend J I hI hIr hg.symm)

end
end MazurProof.N13GenericInfinityComparison


