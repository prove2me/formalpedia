-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityChartMarking_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityChartMarking_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T22:37:03.403199+00:00
-- url     : https://prove2.me/theorems/bce89c4f-e9a4-4f54-90cd-5815444cdfdc
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityChartMarking source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityChartMarking

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityChartMarking
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13EffectiveGraphData_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinitySplit_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicInfinityCompatibility_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InverseInfinityWitnessClass_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
New source candidate for FLT-C13-B00-EXIST r2. Lean checks: NOT RUN.

Tie the infinity marking to the actual ordinary infinity ideal by extending
that ideal into the two generic formal branch rings. This reads the chart
ideal itself, not the separately stored integer. The two infinity sections
and their tensor products are certified here.
-/

namespace MazurProof.N13InfinityChartMarking

noncomputable section
open Polynomial

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev B := N13IntegralInfinityPointSpread.InfinityCurve
abbrev P := N13FormalInfinityChart.Power
abbrev QP := N13TwoAdicInfinityCompatibility.RationalPower
abbrev Line := N13TwoChartPicardRealization.Line

def positiveIntegralExpansion : B →+* P :=
  N13FormalInfinitySplit.evalBranchZero.comp N13IntegralInfinityChart.toFormalInfinity

def negativeIntegralExpansion : B →+* P :=
  N13FormalInfinitySplit.evalBranchOne.comp N13IntegralInfinityChart.toFormalInfinity

def positiveExpansion : B →+* QP :=
  N13TwoAdicInfinityCompatibility.powerMap.comp positiveIntegralExpansion

def negativeExpansion : B →+* QP :=
  N13TwoAdicInfinityCompatibility.powerMap.comp negativeIntegralExpansion

/-- The actual completed generic infinity ideal, with both sheet orders. -/
def HasInfinityMultiplicities (L : Line) (p m : ℕ) : Prop :=
  Ideal.map positiveExpansion L.infinityIdeal =
      Ideal.span ({PowerSeries.X ^ p} : Set QP) ∧
  Ideal.map negativeExpansion L.infinityIdeal =
      Ideal.span ({PowerSeries.X ^ m} : Set QP)

/-- A literal infinity-ideal condition on the positive marking of Data. -/
def HasGeometricMark (R : N13TwoChartPicardRealization.Data) : Prop :=
  ∃ p m : ℕ, HasInfinityMultiplicities R.charts p m ∧
    R.infinityOrder = (p : ℤ) - 2

theorem hasInfinityMultiplicities_tensor
    (L M : Line) (p m q n : ℕ)
    (hL : HasInfinityMultiplicities L p m)
    (hM : HasInfinityMultiplicities M q n) :
    HasInfinityMultiplicities (N13TwoChartLineTensor.tensor L M) (p + q) (m + n) := by
  constructor
  · change Ideal.map positiveExpansion (L.infinityIdeal * M.infinityIdeal) = _
    rw [Ideal.map_mul, hL.1, hM.1, Ideal.span_singleton_mul_span_singleton, ← pow_add]
  · change Ideal.map negativeExpansion (L.infinityIdeal * M.infinityIdeal) = _
    rw [Ideal.map_mul, hL.2, hM.2, Ideal.span_singleton_mul_span_singleton, ← pow_add]

private theorem span_pair_unit_right {R : Type*} [CommRing R] (x y : R) (hy : IsUnit y) :
    Ideal.span ({x, y} : Set R) = ⊤ := by
  rcases hy with ⟨u, rfl⟩
  rw [Ideal.eq_top_iff_one]
  have hu : (u : R) ∈ Ideal.span ({x, (u : R)} : Set R) :=
    Ideal.subset_span (by simp)
  have hh := Ideal.mul_mem_left (Ideal.span ({x, (u : R)} : Set R)) (↑(u⁻¹) : R) hu
  simpa using hh

private theorem plus_ideal :
    N13TwoChartLineTensor.infinityPlusLine.infinityIdeal =
      Ideal.span ({N13IntegralInfinityChart.tClass, N13IntegralInfinityChart.vClass} : Set B) := by
  simp [N13TwoChartLineTensor.infinityPlusLine,
    N13TwoChartLineTensor.infinityPlusPoint, N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.pointIdeal, GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass, N13IntegralInfinityPointSpread.pointU,
    N13IntegralInfinityPointSpread.pointV, N13IntegralInfinityPointSpread.yClass]

private theorem minus_ideal :
    N13TwoChartLineTensor.infinityMinusLine.infinityIdeal =
      Ideal.span ({N13IntegralInfinityChart.tClass, N13IntegralInfinityChart.vClass + 1} : Set B) := by
  simp [N13TwoChartLineTensor.infinityMinusLine,
    N13TwoChartLineTensor.infinityMinusPoint, N13IntegralInfinityPointSpread.pointLine,
    N13IntegralInfinityPointSpread.pointIdeal, GeneralizedGraphIdealCore.graphIdeal,
    GeneralizedGraphIdealCore.ySubClass, N13IntegralInfinityPointSpread.pointU,
    N13IntegralInfinityPointSpread.pointV, N13IntegralInfinityPointSpread.yClass]

private theorem positiveIntegralExpansion_t :
    positiveIntegralExpansion N13IntegralInfinityChart.tClass = PowerSeries.X := by
  simp [positiveIntegralExpansion]

private theorem negativeIntegralExpansion_t :
    negativeIntegralExpansion N13IntegralInfinityChart.tClass = PowerSeries.X := by
  simp [negativeIntegralExpansion]

private theorem positiveIntegralExpansion_v :
    positiveIntegralExpansion N13IntegralInfinityChart.vClass = N13FormalInfinityBranches.branchZero := by
  simp [positiveIntegralExpansion]

private theorem negativeIntegralExpansion_v :
    negativeIntegralExpansion N13IntegralInfinityChart.vClass = N13FormalInfinityBranches.branchOne := by
  simp [negativeIntegralExpansion]

private theorem integral_plus_on_plus :
    Ideal.map positiveIntegralExpansion N13TwoChartLineTensor.infinityPlusLine.infinityIdeal =
      Ideal.span ({PowerSeries.X} : Set P) := by
  rw [plus_ideal, Ideal.map_span, Set.image_pair,
    positiveIntegralExpansion_t, positiveIntegralExpansion_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  exact PowerSeries.X_dvd_iff.mpr N13FormalInfinityBranches.branchZero_constantCoeff

private theorem integral_plus_on_minus :
    Ideal.map negativeIntegralExpansion N13TwoChartLineTensor.infinityPlusLine.infinityIdeal = ⊤ := by
  rw [plus_ideal, Ideal.map_span, Set.image_pair,
    negativeIntegralExpansion_t, negativeIntegralExpansion_v]
  apply span_pair_unit_right
  rw [PowerSeries.isUnit_iff_constantCoeff, N13FormalInfinityBranches.branchOne_constantCoeff]
  exact isUnit_neg_one

private theorem integral_minus_on_plus :
    Ideal.map positiveIntegralExpansion N13TwoChartLineTensor.infinityMinusLine.infinityIdeal = ⊤ := by
  rw [minus_ideal, Ideal.map_span, Set.image_pair,
    positiveIntegralExpansion_t, map_add, map_one, positiveIntegralExpansion_v]
  apply span_pair_unit_right
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simpa [N13FormalInfinityBranches.branchZero_constantCoeff] using (isUnit_one : IsUnit (1 : N13FormalInfinityChart.R₂))

private theorem integral_minus_on_minus :
    Ideal.map negativeIntegralExpansion N13TwoChartLineTensor.infinityMinusLine.infinityIdeal =
      Ideal.span ({PowerSeries.X} : Set P) := by
  rw [minus_ideal, Ideal.map_span, Set.image_pair,
    negativeIntegralExpansion_t, map_add, map_one, negativeIntegralExpansion_v]
  apply Ideal.span_pair_eq_span_left_iff_dvd.mpr
  apply PowerSeries.X_dvd_iff.mpr
  simp [N13FormalInfinityBranches.branchOne_constantCoeff]

private theorem generic_map_of_integral
    (f : B →+* P) (I : Ideal B) (n : ℕ)
    (h : Ideal.map f I = Ideal.span ({PowerSeries.X ^ n} : Set P)) :
    Ideal.map (N13TwoAdicInfinityCompatibility.powerMap.comp f) I =
      Ideal.span ({PowerSeries.X ^ n} : Set QP) := by
  rw [← Ideal.map_map, h, Ideal.map_span, Set.image_singleton]
  simp [N13TwoAdicInfinityCompatibility.powerMap]

theorem infinityPlusLine_marked :
    HasInfinityMultiplicities N13TwoChartLineTensor.infinityPlusLine 1 0 := by
  constructor
  · exact generic_map_of_integral positiveIntegralExpansion _ 1
      (by simpa only [pow_one] using integral_plus_on_plus)
  · exact generic_map_of_integral negativeIntegralExpansion _ 0
      (by simpa only [pow_zero, Ideal.span_singleton_one] using integral_plus_on_minus)

theorem infinityMinusLine_marked :
    HasInfinityMultiplicities N13TwoChartLineTensor.infinityMinusLine 0 1 := by
  constructor
  · exact generic_map_of_integral positiveIntegralExpansion _ 0
      (by simpa only [pow_zero, Ideal.span_singleton_one] using integral_minus_on_plus)
  · exact generic_map_of_integral negativeIntegralExpansion _ 1
      (by simpa only [pow_one] using integral_minus_on_minus)

private theorem map_top_of_t_unit_mod
    (f : B →+* P) (hf : f N13IntegralInfinityChart.tClass = PowerSeries.X)
    (I : Ideal B) (hI : ∃ a : B, 1 - N13IntegralInfinityChart.tClass * a ∈ I) :
    Ideal.map f I = ⊤ := by
  obtain ⟨a, ha⟩ := hI
  have hm : f (1 - N13IntegralInfinityChart.tClass * a) ∈ Ideal.map f I :=
    Ideal.mem_map_of_mem f ha
  have hu : IsUnit (f (1 - N13IntegralInfinityChart.tClass * a)) := by
    rw [map_sub, map_one, map_mul, hf, PowerSeries.isUnit_iff_constantCoeff]
    simpa using (isUnit_one : IsUnit (1 : N13FormalInfinityChart.R₂))
  rcases hu with ⟨u, hu⟩
  rw [← hu] at hm
  rw [Ideal.eq_top_iff_one]
  have hh := Ideal.mul_mem_left (Ideal.map f I) (↑(u⁻¹) : P) hm
  simpa using hh

/-- Finite affine support supplies an actual unit modulo the infinity
closure. Hence both generic formal infinity ideals are the unit ideal. -/
theorem finiteClosure_marked
    (I : Ideal N13FiniteAffineTwoChart.AffineCurve)
    (hI : IsUnit (I : N13FiniteAffineTwoChart.AffineFractionalIdeal))
    (hfinite : Module.Finite N13FiniteAffineTwoChart.R₂
      (N13FiniteAffineTwoChart.AffineCurve ⧸ I)) :
    HasInfinityMultiplicities
      (N13FiniteAffineTwoChart.twoChartLineOfInfinityClosure I hI hfinite) 0 0 := by
  have ht := N13FiniteAffineTwoChart.infinityClosure_tUnitMod_of_finite I hfinite
  constructor
  · apply generic_map_of_integral positiveIntegralExpansion _ 0
    have h0 : Ideal.map positiveIntegralExpansion
        (N13FiniteAffineTwoChart.twoChartLineOfInfinityClosure I hI hfinite).infinityIdeal = ⊤ :=
      map_top_of_t_unit_mod positiveIntegralExpansion positiveIntegralExpansion_t
        (N13FiniteAffineTwoChart.infinityClosure I) ht
    simpa only [pow_zero, Ideal.span_singleton_one] using h0
  · apply generic_map_of_integral negativeIntegralExpansion _ 0
    have h0 : Ideal.map negativeIntegralExpansion
        (N13FiniteAffineTwoChart.twoChartLineOfInfinityClosure I hI hfinite).infinityIdeal = ⊤ :=
      map_top_of_t_unit_mod negativeIntegralExpansion negativeIntegralExpansion_t
        (N13FiniteAffineTwoChart.infinityClosure I) ht
    simpa only [pow_zero, Ideal.span_singleton_one] using h0

theorem integralPointLine_marked
    (p : N13IntegralAffinePointSpread.IntegralPoint) :
    HasInfinityMultiplicities (N13FiniteAffineTwoChart.integralPointTwoChartLine p) 0 0 :=
  finiteClosure_marked _ _ _

theorem finiteQuadraticLine_marked
    (D : N13Mumford.SemiMumford N13TwoChartPicardRealization.Q₂)
    (hd : D.u.natDegree = 2)
    (hfinite : Module.Finite N13FiniteAffineTwoChart.R₂
      (N13FiniteAffineTwoChart.AffineCurve ⧸ N13FiniteAffineTwoChart.finiteAffineIdeal D)) :
    HasInfinityMultiplicities
      (N13FiniteAffineTwoChart.finiteQuadraticTwoChartLine D hd hfinite) 0 0 :=
  finiteClosure_marked _ _ _

private theorem positiveExpansion_base (p : N13IntegralInfinityChart.Base) :
    positiveExpansion (N13IntegralInfinityPointSpread.xClassHom p) =
      N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p) := by
  simp [positiveExpansion, positiveIntegralExpansion,
    N13IntegralInfinityPointSpread.xClassHom, N13IntegralInfinityChart.toFormalInfinity,
    N13FormalInfinitySplit.evalBranchZero]

private theorem negativeExpansion_base (p : N13IntegralInfinityChart.Base) :
    negativeExpansion (N13IntegralInfinityPointSpread.xClassHom p) =
      N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p) := by
  simp [negativeExpansion, negativeIntegralExpansion,
    N13IntegralInfinityPointSpread.xClassHom, N13IntegralInfinityChart.toFormalInfinity,
    N13FormalInfinitySplit.evalBranchOne]

private theorem generic_base_constantCoeff (p : N13IntegralInfinityChart.Base) :
    PowerSeries.constantCoeff
      (N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p)) =
      N13TwoAdicInfinityCompatibility.coeffMap (p.coeff 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial n a =>
    cases n <;> simp [N13IntegralInfinityChart.baseToPower,
      N13TwoAdicInfinityCompatibility.powerMap]

private theorem map_top_of_polynomial_mem
    (f : B →+* QP)
    (hf : ∀ p : N13IntegralInfinityChart.Base,
      f (N13IntegralInfinityPointSpread.xClassHom p) =
        N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p))
    (I : Ideal B) (p : N13IntegralInfinityChart.Base)
    (hp : N13IntegralInfinityPointSpread.xClassHom p ∈ I)
    (hp0 : N13TwoAdicInfinityCompatibility.coeffMap (p.coeff 0) ≠ 0) :
    Ideal.map f I = ⊤ := by
  have hm := Ideal.mem_map_of_mem f hp
  have hu : IsUnit (f (N13IntegralInfinityPointSpread.xClassHom p)) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hf, generic_base_constantCoeff]
    exact isUnit_iff_ne_zero.mpr hp0
  rcases hu with ⟨u, hu⟩
  rw [← hu] at hm
  rw [Ideal.eq_top_iff_one]
  have hh := Ideal.mul_mem_left (Ideal.map f I) (↑(u⁻¹) : QP) hm
  simpa using hh

/-- A horizontal polynomial with nonzero generic constant term is enough
to certify that the actual infinity ideal has no generic infinity support.
This applies equally to horizontal and vertical reciprocal graph charts. -/
theorem marked_of_polynomial_mem
    (L : Line) (p : N13IntegralInfinityChart.Base)
    (hp : N13IntegralInfinityPointSpread.xClassHom p ∈ L.infinityIdeal)
    (hp0 : N13TwoAdicInfinityCompatibility.coeffMap (p.coeff 0) ≠ 0) :
    HasInfinityMultiplicities L 0 0 := by
  constructor
  · simpa only [pow_zero, Ideal.span_singleton_one] using
      map_top_of_polynomial_mem positiveExpansion positiveExpansion_base L.infinityIdeal p hp hp0
  · simpa only [pow_zero, Ideal.span_singleton_one] using
      map_top_of_polynomial_mem negativeExpansion negativeExpansion_base L.infinityIdeal p hp hp0

theorem infinityGraphLine_marked
    (D : N13IntegralInfinityGraphTwoChart.GraphData)
    (hu : D.u.natDegree ≤ 2) (hv : D.v.natDegree ≤ 3) (hw : D.w.natDegree ≤ 4)
    (hne : D.u ≠ 0)
    (h0 : N13TwoAdicInfinityCompatibility.coeffMap (D.u.coeff 0) ≠ 0) :
    HasInfinityMultiplicities
      (N13IntegralInfinityGraphTwoChart.twoChartLine D hu hv hw hne) 0 0 := by
  apply marked_of_polynomial_mem _ D.u _ h0
  exact GeneralizedGraphIdealCore.xClass_mem_graphIdeal _ _ _ _

theorem infinityVerticalGraphLine_marked
    (u : Polynomial N13IrreducibleQuadraticSpread.R₂)
    (E : N13IntegralInfinityVerticalGraphJacobian.VerticalGraph)
    (hu : u.Monic) (huDegree : u.natDegree = 2) (hmDegree : E.m.natDegree = 2)
    (huMem : N13IntegralInfinityReduction.integralBaseClass u ∈ E.ideal)
    (h0 : N13TwoAdicInfinityCompatibility.coeffMap (u.coeff 0) ≠ 0) :
    HasInfinityMultiplicities
      (N13IntegralInfinityVerticalGraphTwoChart.twoChartLine u E hu huDegree hmDegree huMem) 0 0 := by
  exact marked_of_polynomial_mem _ u huMem h0

/-- The nonzero-constant premise of the reciprocal chart marking follows
from the actual reciprocal equation already carried by that construction. -/
theorem reciprocal_constant_nonzero
    (D : N13Mumford.Mumford N13TwoChartPicardRealization.Q₂)
    (a b : N13IrreducibleQuadraticSpread.R₂)
    (h0 : D.u.coeff 0 ≠ 0)
    (hm : (X ^ 2 + C (a : N13TwoChartPicardRealization.Q₂) * X +
        C (b : N13TwoChartPicardRealization.Q₂)) =
      X ^ 2 + C (D.u.coeff 1 / D.u.coeff 0) * X + C ((D.u.coeff 0)⁻¹)) :
    N13TwoAdicInfinityCompatibility.coeffMap
      ((N13ReciprocalQuadraticReflection.integralReciprocal a b).coeff 0) ≠ 0 := by
  have hb : (b : N13TwoChartPicardRealization.Q₂) = (D.u.coeff 0)⁻¹ := by
    simpa using congrArg (fun p => p.coeff 0) hm
  have hc : (N13ReciprocalQuadraticReflection.integralReciprocal a b).coeff 0 = b := by
    simp [N13ReciprocalQuadraticReflection.integralReciprocal]
  rw [hc]
  change (b : N13TwoChartPicardRealization.Q₂) ≠ 0
  rw [hb]
  exact inv_ne_zero h0

private theorem point_map_top_of_nonzero_t
    (f : B →+* QP)
    (hf : ∀ p : N13IntegralInfinityChart.Base,
      f (N13IntegralInfinityPointSpread.xClassHom p) =
        N13TwoAdicInfinityCompatibility.powerMap (N13IntegralInfinityChart.baseToPower p))
    (p : N13IntegralInfinityPointSpread.IntegralInfinityPoint) (hp : p.1.1 ≠ 0) :
    Ideal.map f (N13IntegralInfinityPointSpread.pointIdeal p) = ⊤ := by
  have hm : f (N13IntegralInfinityPointSpread.xClassHom
      (N13IntegralInfinityPointSpread.pointU p)) ∈
      Ideal.map f (N13IntegralInfinityPointSpread.pointIdeal p) := by
    apply Ideal.mem_map_of_mem
    exact GeneralizedGraphIdealCore.xClass_mem_graphIdeal _ _ _ _
  have hc : PowerSeries.constantCoeff
      (f (N13IntegralInfinityPointSpread.xClassHom
        (N13IntegralInfinityPointSpread.pointU p))) =
      -N13TwoAdicInfinityCompatibility.coeffMap p.1.1 := by
    rw [hf]
    simp [N13IntegralInfinityPointSpread.pointU, N13IntegralInfinityChart.baseToPower,
      N13TwoAdicInfinityCompatibility.powerMap]
  have hn : N13TwoAdicInfinityCompatibility.coeffMap p.1.1 ≠ 0 := by
    intro hz
    apply hp
    apply N13TwoAdicInfinityCompatibility.coeffMap_injective
    simpa using hz
  have hu : IsUnit (f (N13IntegralInfinityPointSpread.xClassHom
      (N13IntegralInfinityPointSpread.pointU p))) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hc]
    exact isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hn)
  rcases hu with ⟨u, hu⟩
  rw [← hu] at hm
  rw [Ideal.eq_top_iff_one]
  have hh := Ideal.mul_mem_left
    (Ideal.map f (N13IntegralInfinityPointSpread.pointIdeal p)) (↑(u⁻¹) : QP) hm
  simpa using hh

/-- A point with nonzero generic t-coordinate is absent from both generic
infinity points even if it specializes onto one of them. -/
theorem infinityChartPointLine_marked
    (p : N13IntegralInfinityPointSpread.IntegralInfinityPoint) (hp : p.1.1 ≠ 0) :
    HasInfinityMultiplicities (N13IntegralInfinityPointSpread.pointLine p) 0 0 := by
  constructor
  · have h0 : Ideal.map positiveExpansion
        (N13IntegralInfinityPointSpread.pointLine p).infinityIdeal = ⊤ :=
      point_map_top_of_nonzero_t positiveExpansion positiveExpansion_base p hp
    simpa only [pow_zero, Ideal.span_singleton_one] using h0
  · have h0 : Ideal.map negativeExpansion
        (N13IntegralInfinityPointSpread.pointLine p).infinityIdeal = ⊤ :=
      point_map_top_of_nonzero_t negativeExpansion negativeExpansion_base p hp
    simpa only [pow_zero, Ideal.span_singleton_one] using h0

theorem affinePointLine_marked
    (x y : N13TwoChartPicardRealization.Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) :
    HasInfinityMultiplicities (N13QuadraticTwoChartSpread.pointLine x y h) 0 0 := by
  rw [N13QuadraticTwoChartSpread.pointLine]
  split
  · exact integralPointLine_marked _
  · apply infinityChartPointLine_marked
    rename_i hnorm
    exact N13LocalDlogRegimes.inverseIntegralPart_ne_zero x
      (lt_of_not_ge fun h0 => hnorm ((Padic.norm_le_one_iff_val_nonneg x).mpr h0))

theorem pairLine_marked
    (x y z w : N13TwoChartPicardRealization.Q₂)
    (h : N13GoodModelTwo.AffineEquation x y)
    (k : N13GoodModelTwo.AffineEquation z w) :
    HasInfinityMultiplicities (N13QuadraticTwoChartSpread.pairLine x y z w h k) 0 0 :=
  hasInfinityMultiplicities_tensor _ _ 0 0 0 0
    (affinePointLine_marked x y h) (affinePointLine_marked z w k)

theorem anchoredPointData_geometricMark_of_marked
    (x y : N13TwoChartPicardRealization.Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) (b : Bool)
    (hp : HasInfinityMultiplicities (N13QuadraticTwoChartSpread.pointLine x y h) 0 0) :
    HasGeometricMark (N13EffectiveGraphData.anchoredPointData x y h b) := by
  cases b
  · refine ⟨0, 1, ?_, by first | rfl | simp [N13EffectiveGraphData.anchoredPointData, N13EffectiveGraphData.pointPairData]⟩
    exact hasInfinityMultiplicities_tensor _ _ 0 0 0 1 hp infinityMinusLine_marked
  · refine ⟨1, 0, ?_, by first | rfl | simp [N13EffectiveGraphData.anchoredPointData, N13EffectiveGraphData.pointPairData]⟩
    exact hasInfinityMultiplicities_tensor _ _ 0 0 1 0 hp infinityPlusLine_marked

theorem anchoredPointData_geometricMark
    (x y : N13TwoChartPicardRealization.Q₂)
    (h : N13GoodModelTwo.AffineEquation x y) (b : Bool) :
    HasGeometricMark (N13EffectiveGraphData.anchoredPointData x y h b) :=
  anchoredPointData_geometricMark_of_marked x y h b (affinePointLine_marked x y h)

theorem inverseInfinityData_geometricMark :
    HasGeometricMark N13InverseInfinityWitness.inverseInfinityData := by
  refine ⟨0, 0, ?_, by decide⟩
  exact pairLine_marked _ _ _ _ _ _

theorem infinityPairData_geometricMark (b c : Bool) :
    HasGeometricMark (N13EffectiveGraphData.infinityPairData b c) := by
  cases b <;> cases c
  · refine ⟨0, 2, ?_, by decide⟩
    exact hasInfinityMultiplicities_tensor _ _ 0 1 0 1
      infinityMinusLine_marked infinityMinusLine_marked
  · refine ⟨1, 1, ?_, by decide⟩
    exact hasInfinityMultiplicities_tensor _ _ 0 1 1 0
      infinityMinusLine_marked infinityPlusLine_marked
  · refine ⟨1, 1, ?_, by decide⟩
    exact hasInfinityMultiplicities_tensor _ _ 1 0 0 1
      infinityPlusLine_marked infinityMinusLine_marked
  · refine ⟨2, 0, ?_, by decide⟩
    exact hasInfinityMultiplicities_tensor _ _ 1 0 1 0
      infinityPlusLine_marked infinityPlusLine_marked

end
end MazurProof.N13InfinityChartMarking


