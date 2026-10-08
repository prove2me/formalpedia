-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFormalTransitionJet_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordFormalTransitionJet_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:32:33.421914+00:00
-- url     : https://prove2.me/theorems/b2e96d13-2f10-4fc2-b0aa-88668a309780
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordFormalTransitionJet source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordFormalTransitionJet

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordFormalTransitionJet
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFormalTransition_p0

set_option autoImplicit false




/-!
# First-order coordinates of the N13 formal Mumford transition

The transition of a two-disk Mumford graph is a quotient of two formal
polynomial units.  Multiplying its displacement from the identity by the
fixed base unit cancels the denominator exactly, leaving the finite Laurent
polynomial attached to `u - uBase`.

Its coefficients in degrees `-1` and `0` recover the two disk coordinates
up to the single quadratic term `x₀ * (x₁ + 1)`.  Thus the actual weighted
transition jet agrees with the Abel-chart coordinates modulo the square of
their coordinate ideal, without expanding an inverse power series.
-/

open Polynomial

namespace MazurProof.N13MumfordFormalTransitionJet

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13MumfordFormalTransition.R₂

abbrev Laurent : Type :=
  N13MumfordFormalTransition.Laurent

abbrev FormalCurve : Type :=
  N13MumfordFormalTransition.FormalCurve

abbrev Overlap : Type :=
  N13MumfordFormalTransition.Overlap

abbrev DiskPair : Type :=
  N13TwoAdicAbelChartData.DiskPair

/-- The fixed base transition written in overlap coordinates. -/
def baseOverlap : Overlap :=
  N13FormalCurveOverlap.toOverlap
    (N13MumfordFormalTransition.baseFormalPolyUnit : FormalCurve)

/-- Restore the fixed base denominator in an arbitrary near-identity
transition displacement. -/
def weightedDeviationOfTransition
    (g : N13FormalLineBundleCech.NearIdentityTransition) : Overlap :=
  N13FormalLineBundleCech.mulOverlap g.deviation baseOverlap

/-- Multiplication is additive in its left argument, hence also preserves
subtraction there. -/
theorem mulOverlap_sub_left
    (x y z : Overlap) :
    N13FormalLineBundleCech.mulOverlap (x - y) z =
      N13FormalLineBundleCech.mulOverlap x z -
        N13FormalLineBundleCech.mulOverlap y z := by
  rw [N13FormalLineBundleCech.mulOverlap_comm (x - y) z,
    N13FormalLineBundleCech.mulOverlap_comm x z,
    N13FormalLineBundleCech.mulOverlap_comm y z]
  exact
    (N13FormalLineBundleCech.leftMul z).map_sub x y

/-- The actual transition attached to a two-disk divisor. -/
def diskTransition (P : DiskPair) :
    N13FormalLineBundleCech.NearIdentityTransition :=
  N13MumfordFormalTransition.nearIdentityTransition
    (N13TwoAdicAbelChartRecover.NearBaseMumford.ofDiskPair P)

/-- Multiply the transition displacement back by the fixed base
trivialization.  This removes the inverse power series exactly. -/
def weightedDeviation (P : DiskPair) : Overlap :=
  weightedDeviationOfTransition (diskTransition P)

/-- After restoring one fixed base factor, the nonlinear error in transition
squaring is one raw displacement times one weighted displacement. -/
theorem square_weightedDeviation
    (g : N13FormalLineBundleCech.NearIdentityTransition) :
    weightedDeviationOfTransition g.square -
          (weightedDeviationOfTransition g +
            weightedDeviationOfTransition g) =
      N13FormalLineBundleCech.mulOverlap
        g.deviation (weightedDeviationOfTransition g) := by
  have h :=
    congrArg
      (fun z : Overlap =>
        N13FormalLineBundleCech.mulOverlap z baseOverlap)
      g.square_deviation
  simpa only [weightedDeviationOfTransition,
    N13FormalLineBundleCech.NearIdentityTransition.deviation,
    mulOverlap_sub_left,
    N13FormalLineBundleCech.mulOverlap_add_left,
    N13FormalLineBundleCech.mulOverlap_assoc] using h

/-- The inverse fixed base transition in overlap coordinates. -/
def baseInverseOverlap : Overlap :=
  N13FormalCurveOverlap.toOverlap
    ((N13MumfordFormalTransition.baseFormalPolyUnit⁻¹ :
      FormalCurveˣ) : FormalCurve)

/-- Restoring the base denominator and then multiplying by its inverse
recovers the raw transition displacement. -/
theorem weightedDeviation_mul_baseInverse (P : DiskPair) :
    N13FormalLineBundleCech.mulOverlap
        (weightedDeviation P) baseInverseOverlap =
      (diskTransition P).deviation := by
  rw [weightedDeviation, weightedDeviationOfTransition, baseOverlap,
    baseInverseOverlap,
    N13FormalLineBundleCech.mulOverlap_assoc,
    ← N13FormalCurveOverlap.toOverlap_mul]
  simp

theorem weightedDeviation_eq (P : DiskPair) :
    weightedDeviation P =
      (N13FormalCurveOverlap.polyAtTInv
        (P.u - N13AbelChartBase.baseSmoothMumford.u), 0) := by
  apply N13FormalCurveOverlap.ofOverlap_injective
  rw [weightedDeviation, weightedDeviationOfTransition, baseOverlap,
    N13FormalCurveOverlap.ofOverlap_mul]
  simp only [diskTransition,
    N13FormalLineBundleCech.NearIdentityTransition.deviation,
    N13MumfordFormalTransition.nearIdentityTransition_transition,
    map_sub, N13FormalCurveOverlap.ofOverlap_toOverlap,
    N13FormalCurveOverlap.ofOverlap_oneOverlap]
  simp only [N13MumfordFormalTransition.transitionUnit,
    N13TwoAdicAbelChartRecover.NearBaseMumford.ofDiskPair_u]
  change
    (((N13MumfordFormalTransition.formalPolyUnit
          P.u P.u_monic : FormalCurve) *
          ((N13MumfordFormalTransition.baseFormalPolyUnit⁻¹ :
            FormalCurveˣ) : FormalCurve) - 1) *
        (N13MumfordFormalTransition.baseFormalPolyUnit :
          FormalCurve)) =
      N13FormalCurveOverlap.ofOverlap
        (N13FormalCurveOverlap.polyAtTInv P.u -
            N13FormalCurveOverlap.polyAtTInv
              N13AbelChartBase.baseSmoothMumford.u,
          0)
  calc
    _ =
        (N13MumfordFormalTransition.formalPolyUnit
            P.u P.u_monic : FormalCurve) -
          (N13MumfordFormalTransition.baseFormalPolyUnit :
            FormalCurve) := by
      rw [sub_mul, mul_assoc]
      simp
    _ =
        algebraMap Laurent FormalCurve
          (N13FormalCurveOverlap.polyAtTInv P.u -
            N13FormalCurveOverlap.polyAtTInv
              N13AbelChartBase.baseSmoothMumford.u) := by
      rw [N13MumfordFormalTransition.coe_formalPolyUnit]
      change
        _ -
            (N13MumfordFormalTransition.formalPolyUnit
              N13AbelChartBase.baseSmoothMumford.u
              N13AbelChartBase.baseSmoothMumford.u_monic :
              FormalCurve) =
          _
      rw [N13MumfordFormalTransition.coe_formalPolyUnit]
      rw [map_sub]
    _ =
        N13FormalCurveOverlap.ofOverlap
          (N13FormalCurveOverlap.polyAtTInv P.u -
              N13FormalCurveOverlap.polyAtTInv
                N13AbelChartBase.baseSmoothMumford.u,
            0) := by
      simp [N13FormalCurveOverlap.ofOverlap]

theorem u_sub_base (P : DiskPair) :
    P.u - N13AbelChartBase.baseSmoothMumford.u =
      C (-(P.x₀ + (P.x₁ + 1))) * X +
        C (P.x₀ * P.x₁) := by
  simp [N13TwoAdicAbelChartData.DiskPair.u,
    N13FormalAbelLinearization.uBase]
  ring

@[simp] theorem weightedDeviation_coeff_negOne (P : DiskPair) :
    (weightedDeviation P).1.coeff (-1) =
      -(P.x₀ + (P.x₁ + 1)) := by
  rw [weightedDeviation_eq, u_sub_base]
  simp [N13FormalCurveOverlap.polyAtTInv,
    N13FormalCurveOverlap.tPow,
    HahnSeries.algebraMap_apply',
    HahnSeries.coeff_mul_single]

@[simp] theorem weightedDeviation_coeff_zero (P : DiskPair) :
    (weightedDeviation P).1.coeff 0 =
      P.x₀ * P.x₁ := by
  rw [weightedDeviation_eq, u_sub_base]
  simp [N13FormalCurveOverlap.polyAtTInv,
    N13FormalCurveOverlap.tPow,
    HahnSeries.algebraMap_apply',
    HahnSeries.coeff_mul_single]

@[simp] theorem weightedDeviation_snd (P : DiskPair) :
    (weightedDeviation P).2 = 0 := by
  rw [weightedDeviation_eq]

/-- The two coefficients which recover the disk coordinates to first
order. -/
def firstJet (z : Overlap) : Fin 2 → R₂ :=
  ![-z.1.coeff 0,
    -z.1.coeff (-1) + z.1.coeff 0]

/-- Multiplying a coefficientwise ideal-valued Laurent series by an
arbitrary Laurent series preserves coefficientwise ideal membership. -/
theorem coeff_mul_mem_leftIdeal
    (I : Ideal R₂) (f g : Laurent)
    (hf : ∀ n : ℤ, f.coeff n ∈ I)
    (n : ℤ) :
    (f * g).coeff n ∈ I := by
  rw [HahnSeries.coeff_mul]
  exact Ideal.sum_mem _ fun p _ =>
    I.mul_mem_right (g.coeff p.2) (hf p.1)

/-- Products of two coefficientwise ideal-valued Laurent series have all
coefficients in the product ideal. -/
theorem coeff_mul_mem_ideal_mul
    (I J : Ideal R₂) (f g : Laurent)
    (hf : ∀ n : ℤ, f.coeff n ∈ I)
    (hg : ∀ n : ℤ, g.coeff n ∈ J)
    (n : ℤ) :
    (f * g).coeff n ∈ I * J := by
  rw [HahnSeries.coeff_mul]
  exact Ideal.sum_mem _ fun p _ =>
    Ideal.mul_mem_mul (hf p.1) (hg p.2)

/-- Every coefficient of the finite weighted displacement is generated by
the two disk coordinates. -/
theorem weightedDeviation_coeff_mem_coordIdeal
    (P : DiskPair) (n : ℤ) :
    (weightedDeviation P).1.coeff n ∈
      N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  have ha : P.x₀ ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  have hb : P.x₁ + 1 ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  by_cases hnNegOne : n = -1
  · subst n
    rw [weightedDeviation_coeff_negOne]
    exact I.neg_mem (I.add_mem ha hb)
  · by_cases hnZero : n = 0
    · subst n
      rw [weightedDeviation_coeff_zero]
      exact I.mul_mem_right P.x₁ ha
    · have hcoeff :
          (weightedDeviation P).1.coeff n = 0 := by
        have hnAddOne : n + 1 ≠ 0 := by
          omega
        rw [weightedDeviation_eq, u_sub_base]
        simp [N13FormalCurveOverlap.polyAtTInv,
          N13FormalCurveOverlap.tPow,
          HahnSeries.algebraMap_apply',
          HahnSeries.coeff_mul_single,
          hnAddOne, hnZero]
      rw [hcoeff]
      exact I.zero_mem

/-- The scalar component of the raw transition displacement is the weighted
finite displacement times the fixed inverse denominator. -/
theorem deviation_fst_eq_weighted_mul_baseInverse (P : DiskPair) :
    (diskTransition P).deviation.1 =
      (weightedDeviation P).1 * baseInverseOverlap.1 := by
  have h :=
    congrArg Prod.fst (weightedDeviation_mul_baseInverse P)
  simpa only [N13FormalLineBundleCech.mulOverlap,
    weightedDeviation_snd, zero_mul, zero_mul,
    zero_add, add_zero] using h.symm

/-- The raw transition still vanishes coefficientwise modulo the moving
coordinate ideal; no inverse-series coefficients are expanded. -/
theorem deviation_coeff_mem_coordIdeal
    (P : DiskPair) (n : ℤ) :
    (diskTransition P).deviation.1.coeff n ∈
      N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P := by
  rw [deviation_fst_eq_weighted_mul_baseInverse]
  exact
    coeff_mul_mem_leftIdeal
      (N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P)
      (weightedDeviation P).1 baseInverseOverlap.1
      (weightedDeviation_coeff_mem_coordIdeal P) n

@[simp] theorem firstJet_weightedDeviation_zero (P : DiskPair) :
    firstJet (weightedDeviation P) 0 =
      P.x₀ - P.x₀ * (P.x₁ + 1) := by
  simp [firstJet]
  ring

@[simp] theorem firstJet_weightedDeviation_one (P : DiskPair) :
    firstJet (weightedDeviation P) 1 =
      (P.x₁ + 1) + P.x₀ * (P.x₁ + 1) := by
  simp [firstJet]
  ring

theorem firstJet_weightedDeviation_sub_coord_mem_sq
    (P : DiskPair) (i : Fin 2) :
    firstJet (weightedDeviation P) i -
        N13TwoAdicAbelChartData.DiskPair.coord P i ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  have ha : P.x₀ ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  have hb : P.x₁ + 1 ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  have hab : P.x₀ * (P.x₁ + 1) ∈ I * I :=
    Ideal.mul_mem_mul ha hb
  fin_cases i
  · change
      firstJet (weightedDeviation P) 0 - P.x₀ ∈ I * I
    rw [firstJet_weightedDeviation_zero]
    convert (I * I).neg_mem hab using 1
    ring
  · change
      firstJet (weightedDeviation P) 1 - (P.x₁ + 1) ∈ I * I
    rw [firstJet_weightedDeviation_one]
    convert hab using 1
    ring

/-- Every scalar Laurent coefficient in the weighted square error is
quadratic in the disk coordinates. -/
theorem square_error_coeff_mem_coordIdeal_sq
    (P : DiskPair) (n : ℤ) :
    (N13FormalLineBundleCech.mulOverlap
        (diskTransition P).deviation
        (weightedDeviation P)).1.coeff n ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  change
    ((diskTransition P).deviation.1 *
        (weightedDeviation P).1 +
      (diskTransition P).deviation.2 *
          (weightedDeviation P).2 *
        N13FormalLineBundleCech.rhsInfinity).coeff n ∈ _
  rw [weightedDeviation_snd]
  simp only [mul_zero, zero_mul, add_zero]
  exact
    coeff_mul_mem_ideal_mul
      (N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P)
      (N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P)
      (diskTransition P).deviation.1
      (weightedDeviation P).1
      (deviation_coeff_mem_coordIdeal P)
      (weightedDeviation_coeff_mem_coordIdeal P) n

/-- The first jet of the weighted square error is quadratic. -/
theorem firstJet_square_error_mem_coordIdeal_sq
    (P : DiskPair) (i : Fin 2) :
    firstJet
        (N13FormalLineBundleCech.mulOverlap
          (diskTransition P).deviation
          (weightedDeviation P)) i ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  fin_cases i
  · exact
      (I * I).neg_mem
        (square_error_coeff_mem_coordIdeal_sq P 0)
  · exact
      (I * I).add_mem
        ((I * I).neg_mem
          (square_error_coeff_mem_coordIdeal_sq P (-1)))
        (square_error_coeff_mem_coordIdeal_sq P 0)

/-- The weighted first jet of the squared actual transition is twice the
weighted first jet, modulo the moving coordinate ideal squared. -/
theorem firstJet_square_sub_double_mem_coordIdeal_sq
    (P : DiskPair) (i : Fin 2) :
    firstJet
          (weightedDeviationOfTransition
            (diskTransition P).square) i -
        (firstJet (weightedDeviation P) i +
          firstJet (weightedDeviation P) i) ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  have h :=
    congrArg
      (fun z : Overlap => firstJet z i)
      (square_weightedDeviation (diskTransition P))
  have hjet :
      firstJet
            (weightedDeviationOfTransition
              (diskTransition P).square) i -
          (firstJet (weightedDeviation P) i +
            firstJet (weightedDeviation P) i) =
      firstJet
          (N13FormalLineBundleCech.mulOverlap
            (diskTransition P).deviation
            (weightedDeviation P)) i := by
    fin_cases i <;>
      simp [weightedDeviation, firstJet,
        HahnSeries.coeff_sub, HahnSeries.coeff_add] at h ⊢ <;>
      linear_combination h
  rw [hjet]
  exact firstJet_square_error_mem_coordIdeal_sq P i

/-- The actual squared transition has first jet equal to twice the disk
coordinate, modulo the square of the disk-coordinate ideal. -/
theorem firstJet_square_sub_double_coord_mem_sq
    (P : DiskPair) (i : Fin 2) :
    firstJet
          (weightedDeviationOfTransition
            (diskTransition P).square) i -
        (N13TwoAdicAbelChartData.DiskPair.coord P i +
          N13TwoAdicAbelChartData.DiskPair.coord P i) ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  have hsquare :=
    firstJet_square_sub_double_mem_coordIdeal_sq P i
  have hcoord :=
    firstJet_weightedDeviation_sub_coord_mem_sq P i
  have hsum : _ ∈ I * I :=
    (I * I).add_mem hsquare
      ((I * I).add_mem hcoord hcoord)
  convert hsum using 1
  ring

end

end MazurProof.N13MumfordFormalTransitionJet


