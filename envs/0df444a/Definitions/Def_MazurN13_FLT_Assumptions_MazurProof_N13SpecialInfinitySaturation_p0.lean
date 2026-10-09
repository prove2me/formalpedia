-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinitySaturation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialInfinitySaturation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:39:55.183628+00:00
-- url     : https://prove2.me/theorems/478df780-261a-4919-8a98-85f139688621
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialInfinitySaturation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialInfinitySaturation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialInfinitySaturation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FiniteAffineTwoChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialGraphDivisorCharts_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialVerticalDivisorCharts_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartSpecialRestriction_p0

set_option autoImplicit false




/-!
# Saturated infinity ideals on the special N13 overlap

The special infinity and affine charts meet on the principal open where
`t` is invertible.  If `t` is already a unit modulo an infinity ideal, then
extension to the overlap and contraction loses no information.  This is the
infinity-chart counterpart of `N13SpecialAffineSaturation`.

Finite affine closures acquire this property from the reflected monic
equation used in their construction.  Canonical divisors of finite special
graphs acquire it point by point: a root at `x=0` contributes the unit ideal,
and a root at `x=1` contributes the relation `t=1`.
-/

open Polynomial
open scoped Sym2

namespace MazurProof.N13SpecialInfinitySaturation

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The special infinity coordinate ring. -/
abbrev InfinityCurve :=
  N13SpecialCurveOverlap.CoordinateRing

/-- The common special overlap ring. -/
abbrev InfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap

/-- The infinity coordinate is a unit in the quotient by `I`. -/
def TUnitMod (I : Ideal InfinityCurve) : Prop :=
  ∃ q : InfinityCurve,
    1 - N13SpecialInfinityChart.tClass * q ∈ I

/-- The unit ideal trivially makes the infinity coordinate invertible in
the quotient. -/
theorem top_tUnitMod :
    TUnitMod (⊤ : Ideal InfinityCurve) := by
  exact ⟨0, by simp⟩

/-- The property that `t` is invertible modulo an ideal is preserved by
ideal products. -/
theorem mul_tUnitMod
    {I J : Ideal InfinityCurve}
    (hI : TUnitMod I)
    (hJ : TUnitMod J) :
    TUnitMod (I * J) := by
  obtain ⟨q, hq⟩ := hI
  obtain ⟨r, hr⟩ := hJ
  refine
    ⟨q + r -
        N13SpecialInfinityChart.tClass * q * r, ?_⟩
  have hprod := Ideal.mul_mem_mul hq hr
  convert hprod using 1
  ring

/-- Multiplication by `t` can be cancelled modulo an ideal in which `t`
is already a unit. -/
theorem mem_of_t_mul_mem
    {I : Ideal InfinityCurve}
    (ht : TUnitMod I)
    {z : InfinityCurve}
    (hz : N13SpecialInfinityChart.tClass * z ∈ I) :
    z ∈ I := by
  obtain ⟨q, hq⟩ := ht
  have h₁ := Ideal.mul_mem_right z I hq
  have h₂ := Ideal.mul_mem_left I q hz
  have hsum := Ideal.add_mem I h₁ h₂
  convert hsum using 1
  ring

/-- Every power of `t` can be cancelled modulo a `t`-saturated ideal. -/
theorem mem_of_t_pow_mul_mem
    {I : Ideal InfinityCurve}
    (ht : TUnitMod I)
    (n : ℕ)
    {z : InfinityCurve}
    (hz : N13SpecialInfinityChart.tClass ^ n * z ∈ I) :
    z ∈ I := by
  induction n with
  | zero =>
      simpa using hz
  | succ n ih =>
      apply ih
      apply mem_of_t_mul_mem ht
      convert hz using 1
      all_goals simp only [pow_succ]
      all_goals ring

/-- Localizing a `t`-saturated infinity ideal and contracting returns the
original ideal. -/
theorem infinityOverlapContracted_of_tUnitMod
    {I : Ideal InfinityCurve}
    (ht : TUnitMod I) :
    Ideal.comap
        (algebraMap InfinityCurve InfinityOverlap)
        (Ideal.map
          (algebraMap InfinityCurve InfinityOverlap) I) =
      I := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap InfinityCurve InfinityOverlap z ∈
        Ideal.map
          (algebraMap InfinityCurve InfinityOverlap) I at hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers N13SpecialInfinityChart.tClass)] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    obtain ⟨n, rfl⟩ := hm
    exact mem_of_t_pow_mul_mem ht n hmz
  · exact Ideal.le_comap_map

/-- Reduction preserves an explicit inverse relation for the infinity
coordinate. -/
theorem map_reduceCoordinate_tUnitMod
    {I : Ideal N13FiniteAffineTwoChart.InfinityCurve}
    (ht :
      ∃ q : N13FiniteAffineTwoChart.InfinityCurve,
        1 - N13IntegralInfinityChart.tClass * q ∈ I) :
    TUnitMod
      (Ideal.map
        N13IntegralInfinityReduction.reduceCoordinate I) := by
  obtain ⟨q, hq⟩ := ht
  refine
    ⟨N13IntegralInfinityReduction.reduceCoordinate q, ?_⟩
  have hmap :=
    Ideal.mem_map_of_mem
      N13IntegralInfinityReduction.reduceCoordinate hq
  simpa only [map_sub, map_one, map_mul,
    N13IntegralInfinityReduction.reduce_tClass] using hmap

/-- Compatible special chart pairs with the same affine ideal and
`t`-saturated infinity ideals are equal. -/
theorem chartPair_eq_of_affineIdeal_eq
    (L M : N13TwoChartSpecialRestriction.ChartPair)
    (hL : TUnitMod L.infinityIdeal)
    (hM : TUnitMod M.infinityIdeal)
    (haffine : L.affineIdeal = M.affineIdeal) :
    L = M := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · exact haffine
  · have hoverlap :
        Ideal.map
            (algebraMap InfinityCurve InfinityOverlap)
            L.infinityIdeal =
          Ideal.map
            (algebraMap InfinityCurve InfinityOverlap)
            M.infinityIdeal := by
      rw [← L.overlap_eq, ← M.overlap_eq, haffine]
    rw [← infinityOverlapContracted_of_tUnitMod hL,
      ← infinityOverlapContracted_of_tUnitMod hM, hoverlap]

/-- A finite special point contribution makes `t` invertible: a point at
`x=0` contributes the unit ideal, while a point at `x=1` contributes
`t=1`. -/
theorem rootInfinityFactor_tUnitMod
    (a z : N13SpecialDivisorCharts.K) :
    TUnitMod
      (if a = 0 then
        (⊤ : Ideal InfinityCurve)
      else
        N13SpecialDivisorCharts.infinityPointIdeal 1 z) := by
  by_cases ha : a = 0
  · simp only [ha, if_true]
    exact top_tUnitMod
  · simp only [ha, if_false]
    refine ⟨1, ?_⟩
    have hgen :
        N13SpecialInfinityChart.tClass -
            algebraMap N13SpecialDivisorCharts.K[X] InfinityCurve
              (C (1 : N13SpecialDivisorCharts.K)) ∈
          N13SpecialDivisorCharts.infinityPointIdeal 1 z :=
      Ideal.subset_span (by simp)
    have hneg :=
      (N13SpecialDivisorCharts.infinityPointIdeal 1 z).neg_mem hgen
    convert hneg using 1
    simp

/-- The canonical infinity ideal of a quadratic affine special graph makes
`t` invertible modulo the ideal. -/
theorem graphDivisor_infinity_tUnitMod
    (D : N13GoodCoordinateRingTwo.SemiMumford)
    (hdeg : D.u.natDegree = 2) :
    TUnitMod
      (N13SpecialDivisorCharts.ofDivisor
        (N13SpecialGraphDivisor.graphDivisor D hdeg)).infinityIdeal := by
  rw [
    N13SpecialGraphDivisorCharts.ofDivisor_graphDivisor_infinityIdeal]
  let z := N13SpecialGraphDivisor.rootPair D hdeg
  change
    TUnitMod
      (N13SpecialGraphDivisorCharts.rootInfinityIdeal D z)
  induction z using Sym2.ind with
  | _ a b =>
      rw [N13SpecialGraphDivisorCharts.rootInfinityIdeal_mk]
      exact
        mul_tUnitMod
          (rootInfinityFactor_tUnitMod a (D.v.eval a))
          (rootInfinityFactor_tUnitMod b (D.v.eval b))

/-- The canonical two-sheet divisor above a finite base coordinate makes
`t` invertible on the infinity chart: it is absent at `x=0` and satisfies
`t=1` at `x=1`. -/
theorem canonicalDivisor_infinity_tUnitMod
    (a : N13SpecialDivisorCharts.K) :
    TUnitMod
      (N13SpecialDivisorCharts.ofDivisor
        (N13AbelFiberTwoModel.canonicalDivisor
          (Sum.inl a))).infinityIdeal := by
  rw [N13SpecialVerticalDivisorCharts.canonicalDivisor_infinityIdeal]
  rcases
      N13GoodModelTwo.fixedTwo_eq_zero_or_one
        a (ZMod.pow_card a) with rfl | rfl
  · simp only [if_true]
    exact top_tUnitMod
  · simp only [if_false, one_ne_zero]
    refine ⟨1, ?_⟩
    have hgen :
        N13SpecialInfinityChart.tClass -
            algebraMap N13SpecialDivisorCharts.K[X] InfinityCurve
              (C (1 : N13SpecialDivisorCharts.K)) ∈
          Ideal.span
            ({N13SpecialInfinityChart.tClass -
                algebraMap N13SpecialDivisorCharts.K[X] InfinityCurve
                  (C (1 : N13SpecialDivisorCharts.K))} :
              Set InfinityCurve) :=
      Ideal.subset_span (by simp)
    have hneg :=
      (Ideal.span
        ({N13SpecialInfinityChart.tClass -
            algebraMap N13SpecialDivisorCharts.K[X] InfinityCurve
              (C (1 : N13SpecialDivisorCharts.K))} :
          Set InfinityCurve)).neg_mem hgen
    convert hneg using 1
    simp

end

end MazurProof.N13SpecialInfinitySaturation


