-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0024
-- name    : PNT_ZeroFree_433_0024
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:27:03.19402+00:00
-- url     : https://prove2.me/theorems/ff2fc62f-544e-4288-ad7d-1a68528699a2
-- title:
--   Zero-free region foundations: GaussSum.ThetaLocalRows [0024]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.ThetaLocalRows
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L31-L583

import Definitions.Def_PNT_ZeroFree_433_0023

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/ThetaLocalRows.lean#L31-L583
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.ThetaLocalRows
section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_fixed_kernel_eq_dualFixedTerm
    (a b k l : ℤ) (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      fixedDualPhase c y =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) (k,l) := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let y : O := dualFrequencyEquiv (k,l)
  have hnormC : ((‖eisEmbedding y‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  have hreal : Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) =
      (OscSpecial.dualAmp η (a : ℝ) (b : ℝ) (k,l) : ℂ) := by
    rw [hnormC]
    dsimp [OscSpecial.dualAmp, OscSpecial.dualScale, OscSpecial.dualQ]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase : fixedDualPhase c y =
      Complex.exp (Complex.I *
        (OscSpecial.phaseAngle (a : ℝ) (b : ℝ) (k,l) : ℂ)) := by
    have h := breveE_dual_quadratic_real_scale 1 a b k l
    have harg : fixedDualPhase c y =
        Complex.exp (-(2 * Real.pi * Complex.I *
          (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) / (4 : ℂ)) := by
      change ShortDraftTrace.breveE
        (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
          (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
          eisLam / (4 : ℂ)) = _
      simpa using h
    rw [harg]
    congr 1
    dsimp [OscSpecial.phaseAngle, OscSpecial.dualTrace]
    push_cast
    ring
  dsimp only
  rw [hreal, hphase]
  rfl

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter

noncomputable def actualVariableDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  ShortDraftTrace.breveE
    (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
      eisLam /
      ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))

noncomputable def actualFixedDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  fixedDualPhase (ActualEisensteinCoordinates.eval a b) y

private theorem dualScale_cast (η a b : ℝ) :
    (OscSpecial.dualScale η a b : ℂ) =
      (η : ℂ) * (OscSpecial.q a b : ℂ) /
        (4 * (OscSpecial.r η a b : ℂ)) := by
  dsimp [OscSpecial.dualScale]
  push_cast
  ring

theorem actual_variable_kernel_eq_dualVarTerm
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) (z : ℤ × ℤ) :
    actualVariableDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have h := (dual_gaussian_is_actual_trace_phase
    a b z.1 z.2 hc η hη).symm.trans
      (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z)
  unfold actualVariableDualKernel
  rw [dualScale_cast]
  exact h

theorem actual_fixed_kernel_eq_dualFixedTerm_point
    (a b : ℤ) (η : ℝ) (z : ℤ × ℤ) :
    actualFixedDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
  rcases z with ⟨k,l⟩
  exact actual_fixed_kernel_eq_dualFixedTerm a b k l η

theorem actual_dual_phase_error_tendsto_zero
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto
      (fun η : ℝ => η * ‖
        (∑' y : O, actualVariableDualKernel a b η y) -
        (∑' y : O, actualFixedDualKernel a b η y)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have hbase := OscSpecial.normalized_dual_phase_sum_error_tendsto_zero hq
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  have hvar :
      (∑' y : O, actualVariableDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualVariableDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualVariableDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualVariableDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_variable_kernel_eq_dualVarTerm a b hc η hη z
  have hfixed :
      (∑' y : O, actualFixedDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualFixedDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualFixedDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualFixedDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_fixed_kernel_eq_dualFixedTerm_point a b η z
  rw [hvar, hfixed]

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actualFixedAbelLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' y : O, actualFixedDualKernel a b η y))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r))) := by
  simpa only [actualFixedDualKernel, mul_comm] using
    variableDualPhase_abel_limit a b hc

end

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_poisson_kernel
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O, actualVariableDualKernel a b η y := by
  dsimp only
  rw [actual_oscillatory_poisson a b hc η hη]
  congr 1
  apply tsum_congr
  intro y
  unfold actualVariableDualKernel
  rw [dualScale_cast]

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actualVariableAbelLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      ((1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ))) *
        (∑' y : O, actualVariableDualKernel a b η y)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
          fixedDualPhase c (GaussianShiftedPartition.representative 2 r))))) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  exact abel_transfer
    (fun η => 1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ)))
    (fun η => ∑' y : O, actualVariableDualKernel a b η y)
    (fun η => ∑' y : O, actualFixedDualKernel a b η y)
    _ _ (OscSpecial.prefactor_tendsto hq)
    (actualFixedAbelLimit a b hc)
    (actual_dual_phase_error_tendsto_zero a b hc)

theorem actualOriginalAbelDualLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
          fixedDualPhase c (GaussianShiftedPartition.representative 2 r))))) := by
  apply (actualVariableAbelLimit a b hc).congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  rw [actual_oscillatory_poisson_kernel a b hc η hη]

end

section

theorem dual_abel_coefficient (a b : ℤ)
    (hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ)) :
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
      ((2 / (Real.sqrt 3 *
        (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)) =
      ((2 / (Real.sqrt 3 * OscSpecial.q (a : ℝ) (b : ℝ)) : ℝ) : ℂ) := by
  dsimp only
  rw [two_coordinate_norm_four]
  have hqC : (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hqC, hsC]

theorem full_dual_abel_coefficient (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) *
        ((2 / (Real.sqrt 3 *
          (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ))) =
      (((2 / (Real.sqrt 3 * ‖ConcreteTraceCRT.eisEmbedding c‖) : ℝ) : ℂ) / 2) := by
  dsimp only
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  rw [dual_abel_coefficient a b hq]
  have hqnorm := osc_q_eq_eis_norm_sq a b
  have hsqrt : Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) =
      ‖ConcreteTraceCRT.eisEmbedding
        (ActualEisensteinCoordinates.eval a b)‖ := by
    rw [hqnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hsqrt, hqnorm]
  have hn : (‖ConcreteTraceCRT.eisEmbedding
      (ActualEisensteinCoordinates.eval a b)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (norm_pos_iff.mpr
      (ConcreteTraceCRT.eisEmbedding_ne_zero hc)))
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hn, hs]

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem quadraticGammaO_eq_fourTerms (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc =
      breveGaussianFourTerms a b := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let n : ℝ := ‖eisEmbedding c‖
  let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
  let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
  let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
  let L2 : ℂ := ((2 / (Real.sqrt 3 *
    (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
  let : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    finite_quotient_span (by norm_num : (2 : O) ≠ 0)
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let S : ℂ := ∑ r : O ⧸ Ideal.span {(2 : O)},
    fixedDualPhase c (GaussianShiftedPartition.representative 2 r)
  have hEq0 := tendsto_nhds_unique
    (original_abel_gamma_limit c hc)
    (actualOriginalAbelDualLimit a b hc)
  have hEq : (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc) =
      (((Real.sqrt q / 2 : ℝ) : ℂ) *
        ((((4 / q : ℝ) : ℂ) * L2) * S)) := by
    simpa only [c, n, q, a2, b2, L2, S, mul_assoc] using hEq0
  have hC : (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) * L2)) =
      (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) := by
    simpa only [c, n, q, a2, b2, L2] using
      full_dual_abel_coefficient a b hc
  have hA : ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) ≠ 0 := by
    have hn : 0 < n := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast (ne_of_gt (div_pos (by norm_num : (0 : ℝ) < 2)
      (mul_pos hs hn)))
  have hG : quadraticGammaO c hc = S / 2 := by
    apply mul_left_cancel₀ hA
    calc
      ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc =
          ((Real.sqrt q / 2 : ℝ) : ℂ) *
            ((((4 / q : ℝ) : ℂ) * L2) * S) := hEq
      _ = (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) * S := by rw [← mul_assoc, hC]
      _ = ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * (S / 2) := by ring
  change quadraticGammaO c hc = breveGaussianFourTerms a b
  calc
    quadraticGammaO c hc = S / 2 := hG
    _ = breveGaussianFourTerms a b := fixedDualPhase_four_terms a b

end

theorem quadraticGammaO_formula (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc =
      (1 + Complex.I ^ (-b) + Complex.I ^ a + Complex.I ^ (b-a)) / 2 := by
  rw [quadraticGammaO_eq_fourTerms a b hc, breveGaussianFourTerms_formula]

end ActualEisensteinCubic

theorem theta_counter_lambda_eq : ActualEisensteinCubic.lambda =
    ActualEisensteinCoordinates.eval (-1) 1 := by
  have homega : ActualEisensteinCubic.omega = ActualEisensteinCoordinates.omega := by
    rfl
  rw [ActualEisensteinCubic.lambda, ActualEisensteinCoordinates.eval, homega]
  ring

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

private noncomputable def pSeven : ActualEisensteinCubic.O := ActualEisensteinCoordinates.eval 1 3
private noncomputable def PSeven : Ideal ActualEisensteinCubic.O := Ideal.span {pSeven}

private theorem pSeven_norm : ShortDraftLatticeCount.qNat pSeven = 7 := by
  unfold ShortDraftLatticeCount.qNat pSeven
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q] <;> decide

private theorem pSeven_ne : pSeven ≠ 0 := by
  intro h
  have hh : ActualEisensteinCoordinates.eval 1 3 = ActualEisensteinCoordinates.eval 0 0 := by
    simpa [pSeven, ActualEisensteinCoordinates.eval] using h
  have := (ActualEisensteinCoordinates.unique_coordinates hh).1
  omega

private theorem PSeven_absNorm : Ideal.absNorm PSeven = 7 := by
  simpa only [PSeven, ActualEisensteinCubic.qNat_eq_absNorm_span] using pSeven_norm

private theorem PSeven_maximal : PSeven.IsMaximal := by
  have hprime : PSeven.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [PSeven_absNorm, Nat.irreducible_iff_nat_prime]
    exact (by decide : Nat.Prime 7))
  apply hprime.isMaximal
  exact Ideal.span_singleton_eq_bot.not.mpr pSeven_ne

private theorem lambda7_norm :
    ShortDraftLatticeCount.qNat (ActualEisensteinCoordinates.eval (-1) 1) = 3 := by
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q] <;> decide

private theorem nonreal_cube_ne_conj (γ z : ℂ) (hz : z ≠ 0)
    (hIm : z.im ≠ 0)
    (hc : γ ^ 3 = -z / (‖z‖ : ℂ)) : γ ≠ star γ := by
  intro hγ
  have hstar : star (γ ^ 3) = γ ^ 3 := by
    rw [star_pow, ← hγ]
  have hn : (‖z‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hq : -(star z) / (‖z‖ : ℂ) = -z / (‖z‖ : ℂ) := by
    calc
      -(star z) / (‖z‖ : ℂ) = star (γ ^ 3) := by
        rw [hc, star_div₀]
        simp
      _ = γ ^ 3 := hstar
      _ = _ := hc
  have heq : star z = z := by
    have hh := (div_left_inj' hn).mp hq
    exact neg_injective hh
  exact hIm (Complex.conj_eq_iff_im.mp heq)

private theorem pSeven_embedding_im_ne_zero : (eisEmbedding pSeven).im ≠ 0 := by
  rw [pSeven, ActualEisensteinCubic.eisEmbedding_eval]
  have h : ((((1 : ℤ) : ℂ) + ((3 : ℤ) : ℂ) * omega3).im) = 3 * omega3.im := by
    simp
  rw [h]
  exact mul_ne_zero (by norm_num) omega3_im_ne_zero

noncomputable def thetaGammaSeven : ℂ := by
  letI : PSeven.IsMaximal := PSeven_maximal
  exact breveGamma2 PSeven
    (by
      rw [theta_counter_lambda_eq]
      intro hh
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hh
      have hnorm := congrArg ShortDraftLatticeCount.qNat hx
      rw [ShortDraftLatticeCount.qNat_mul, pSeven_norm, lambda7_norm] at hnorm
      omega)
    pSeven rfl pSeven_ne

theorem thetaGammaSeven_cube :
    thetaGammaSeven ^ 3 = -eisEmbedding pSeven / (‖eisEmbedding pSeven‖ : ℂ) := by
  unfold thetaGammaSeven
  let : PSeven.IsMaximal := PSeven_maximal
  exact ActualEisensteinCubic.breveGamma2_cube PSeven
    (by
      rw [theta_counter_lambda_eq]
      intro hh
      obtain ⟨x, hx⟩ := Ideal.mem_span_singleton.mp hh
      have hnorm := congrArg ShortDraftLatticeCount.qNat hx
      rw [ShortDraftLatticeCount.qNat_mul, pSeven_norm, lambda7_norm] at hnorm
      omega)
    pSeven rfl pSeven_ne
    (by
      rw [theta_counter_lambda_eq]
      refine ⟨-1, ?_⟩
      rw [pow_two, ActualEisensteinCoordinates.eval_mul]
      norm_num [pSeven, ActualEisensteinCoordinates.eval])

theorem thetaGammaSeven_ne_conj : thetaGammaSeven ≠ star thetaGammaSeven := by
  have hz : eisEmbedding pSeven ≠ 0 := by
    intro h
    have := pSeven_embedding_im_ne_zero
    rw [h] at this
    exact this rfl
  exact nonreal_cube_ne_conj thetaGammaSeven (eisEmbedding pSeven) hz
    pSeven_embedding_im_ne_zero thetaGammaSeven_cube

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem direct_theta_jone_inversion (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ ^ 2) (h : F) *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum χ⁻¹ (ψ.mulShift a) := by
  classical
  have hchar : χ⁻¹ * χ ^ 2 = χ := by group
  rw [hchar]
  calc
    (∑ h : Fˣ, χ (h : F) * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, χ⁻¹ (y : F) * ψ (a * (y : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro y
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
      rw [MulChar.inv_apply']
      simp
    _ = gaussSum χ⁻¹ (ψ.mulShift a) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]

theorem direct_theta_jone_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum χ⁻¹ ψ * χ ε) * χ x := by
  classical
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        (χ ^ 2) σ * gaussSum χ (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (χ⁻¹ * χ ^ 2) (h : F) *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient χ ψ hχ, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, direct_theta_jone_inversion χ ψ (ε * x)]
  have hinv : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ
    calc χ = (χ⁻¹)⁻¹ := by group
      _ = 1 := by rw [h]; simp
  rw [gaussSum_mulShift_any χ⁻¹ ψ hinv (ε * x)]
  simp only [inv_inv, map_mul]
  ring

theorem direct_theta_jone_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (σ : Fˣ) (ε : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (χ ^ 2) (σ * h) *
        ψ ((ε * 0) * ((h⁻¹ : Fˣ) : F))) = 0 := by
  rw [direct_theta_jone_local_row χ ψ hχ σ ε 0]
  simp

omit [Fintype F] [DecidableEq F] in
theorem direct_theta_jone_not_quadratic (χ : MulChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) : χ ≠ χ ^ 3 := by
  intro h
  apply hχ₂
  calc
    χ ^ 2 = χ ^ 3 * χ⁻¹ := by group
    _ = χ * χ⁻¹ := by rw [← h]
    _ = 1 := by group

end ShortDraftLocal

end

end OAI

end


