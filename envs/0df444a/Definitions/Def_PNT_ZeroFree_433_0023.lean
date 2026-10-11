-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0023
-- name    : PNT_ZeroFree_433_0023
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:22:00.328374+00:00
-- url     : https://prove2.me/theorems/c21a39aa-e406-465f-b096-7c00a275b874
-- title:
--   Zero-free region foundations: GaussSum.AbelPhaseLimit [0023]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.AbelPhaseLimit
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/AbelPhaseLimit.lean#L27-L630

import Definitions.Def_PNT_ZeroFree_433_0022

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/AbelPhaseLimit.lean#L27-L630
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.GaussSum.AbelPhaseLimit
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

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

private theorem sum_zmod_two_square (f : ZMod 2 × ZMod 2 → ℂ) :
    (∑ p : ZMod 2 × ZMod 2, f p) =
      f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
  rw [Fintype.sum_prod_type]
  have hu : (Finset.univ : Finset (ZMod 2)) = {0,1} := rfl
  simp [hu]
  ring

theorem fixedDualPhase_quotient_two_four_residues (c : O) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase c (GaussianShiftedPartition.representative 2 r)) =
      fixedDualPhase c (ActualEisensteinCoordinates.eval 0 0) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 0 1) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 1 0) +
      fixedDualPhase c (ActualEisensteinCoordinates.eval 1 1) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let e := rationalCoordEquiv 2 (by norm_num)
  let P : O ⧸ Ideal.span {(2 : O)} → ℂ :=
    fun r => fixedDualPhase c (GaussianShiftedPartition.representative 2 r)
  have hpoint (p : ZMod 2 × ZMod 2) :
      P (e p) = fixedDualPhase c
        (ActualEisensteinCoordinates.eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    dsimp only [P]
    apply fixedDualPhase_eq_of_mod_two
    rw [GaussianShiftedPartition.representative_spec]
    exact rationalCoordEquiv_apply 2 (by norm_num) p.1 p.2
  have hsum : (∑ r : O ⧸ Ideal.span {(2 : O)}, P r) =
      ∑ p : ZMod 2 × ZMod 2,
        fixedDualPhase c
          (ActualEisensteinCoordinates.eval (ZMod.cast p.1) (ZMod.cast p.2)) := by
    calc
      (∑ r : O ⧸ Ideal.span {(2 : O)}, P r) =
          ∑ p : ZMod 2 × ZMod 2, P (e p) := (e.sum_comp P).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hpoint p
  rw [show (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase c (GaussianShiftedPartition.representative 2 r)) =
      ∑ r : O ⧸ Ideal.span {(2 : O)}, P r from rfl]
  rw [hsum, sum_zmod_two_square]
  have hcast1 : (ZMod.cast (1 : ZMod 2) : ℤ) = 1 := by decide
  simp only [ZMod.cast_zero, hcast1]

theorem fixedDualPhase_coordinates (a b x y : ℤ) :
    fixedDualPhase (ActualEisensteinCoordinates.eval a b)
      (ActualEisensteinCoordinates.eval x y) =
      ShortDraftTrace.breveE
        ((-(((a : ℂ)+(b : ℂ)*omega3) *
          (((x : ℂ)+(y : ℂ)*omega3)^2))) / eisLam / 4) := by
  unfold fixedDualPhase
  rw [map_neg, map_mul, map_pow, eisEmbedding_eval, eisEmbedding_eval]

theorem fixedDualPhase_four_terms (a b : ℤ) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑ r : O ⧸ Ideal.span {(2 : O)},
      fixedDualPhase (ActualEisensteinCoordinates.eval a b)
        (GaussianShiftedPartition.representative 2 r)) / 2 =
      breveGaussianFourTerms a b := by
  let : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    finite_quotient_span (by norm_num : (2 : O) ≠ 0)
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  rw [fixedDualPhase_quotient_two_four_residues]
  rw [fixedDualPhase_coordinates a b 0 0,
    fixedDualPhase_coordinates a b 0 1,
    fixedDualPhase_coordinates a b 1 0,
    fixedDualPhase_coordinates a b 1 1]
  unfold breveGaussianFourTerms
  norm_num
  ring_nf

end ActualEisensteinCubic

namespace OscSpecial

noncomputable def dualQ (z : ℤ × ℤ) : ℝ :=
  (z.1 : ℝ) ^ 2 + (z.1 : ℝ) * (z.2 : ℝ) + (z.2 : ℝ) ^ 2

noncomputable def dualTrace (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  (a - b) * (z.1 : ℝ) ^ 2 + 2 * a * (z.1 : ℝ) * (z.2 : ℝ) +
    b * (z.2 : ℝ) ^ 2

noncomputable def phaseA (a b : ℝ) : ℝ := 3 * q a b / 16
noncomputable def phaseAngle (a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  -(Real.pi / 2) * dualTrace a b z
noncomputable def dualAmp (η a b : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z)
noncomputable def dualVarTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ))
noncomputable def dualFixedTerm (η a b : ℝ) (z : ℤ × ℤ) : ℂ :=
  (dualAmp η a b z : ℂ) *
    Complex.exp (Complex.I * (phaseAngle a b z : ℂ))

private theorem dualQ_nonneg (z : ℤ × ℤ) : 0 ≤ dualQ z := by
  unfold dualQ
  nlinarith [sq_nonneg ((z.1 : ℝ) + (z.2 : ℝ)), sq_nonneg (z.1 : ℝ),
    sq_nonneg (z.2 : ℝ)]

private theorem phaseAngle_bound (a b : ℝ) (z : ℤ × ℤ) :
    |phaseAngle a b z| ≤
      (Real.pi / 2) * phaseBoundConstant a b * dualQ z := by
  have h := quadratic_phase_abs_le a b (z.1 : ℝ) (z.2 : ℝ)
  dsimp [phaseAngle, dualTrace, dualQ]
  rw [abs_mul, abs_neg, abs_of_pos (half_pos Real.pi_pos)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left h (half_pos Real.pi_pos).le

private theorem r_eq_one_add_phaseA (η a b : ℝ) :
    r η a b = 1 + phaseA a b * η ^ 2 := by
  unfold r phaseA
  ring

private theorem phaseA_nonneg {a b : ℝ} (hq : 0 ≤ q a b) :
    0 ≤ phaseA a b := by
  unfold phaseA
  positivity

theorem dual_phase_term_error {η a b : ℝ} (_hη : 0 < η) (hq : 0 < q a b)
    (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
      dualAmp η a b z *
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
        (phaseA a b * η ^ 2) := by
  have hA : 0 ≤ phaseA a b := phaseA_nonneg hq.le
  have hamp : 0 ≤ dualAmp η a b z := (Real.exp_pos _).le
  have hphase := GaussianPhasePointwise.exp_imag_denominator_error
    (phaseAngle a b z) (phaseA a b) η hA
  rw [← r_eq_one_add_phaseA η a b] at hphase
  have hangle := phaseAngle_bound a b z
  have hangle' := mul_le_mul_of_nonneg_right hangle
    (mul_nonneg hA (sq_nonneg η))
  dsimp [dualVarTerm, dualFixedTerm]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hamp]
  nlinarith [mul_le_mul_of_nonneg_left hphase hamp,
    mul_le_mul_of_nonneg_left hangle' hamp]

noncomputable def dualRealGauss (t : ℝ) (z : ℤ × ℤ) : ℝ :=
  Real.exp (-Real.pi * t * dualQ z)

private theorem dualRealGauss_summable {t : ℝ} (ht : 0 < t) :
    Summable (dualRealGauss t) := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  have hE : Summable (fun z : ℤ × ℤ =>
      RankTwoPoisson.eisGauss t (z.1,-z.2)) :=
    (e.summable_iff).2 (RankTwoPoisson.eis_gauss_summable ht)
  convert! hE.norm using 1
  funext z
  dsimp [dualRealGauss, RankTwoPoisson.eisGauss]
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  congr 1
  dsimp [dualQ, RankTwoPoisson.eisQ]
  push_cast
  ring

private theorem dualMoment_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ × ℤ => dualQ z * dualRealGauss t z) := by
  have hmaj : Summable (fun z : ℤ × ℤ =>
      (2 / (Real.pi * t)) * dualRealGauss (t / 2) z) :=
    (dualRealGauss_summable (half_pos ht)).mul_left _
  apply hmaj.of_nonneg_of_le
  · intro z
    exact mul_nonneg (dualQ_nonneg z) (Real.exp_pos _).le
  · intro z
    have h := GaussianMoment.gaussian_moment_term_bound
      (dualQ z) (Real.pi * t) (dualQ_nonneg z) (mul_pos Real.pi_pos ht)
    convert! h using 1 <;> dsimp [dualRealGauss] <;> ring_nf

private theorem dualAmp_eq_realGauss (η a b : ℝ) (z : ℤ × ℤ) :
    dualAmp η a b z = dualRealGauss (η * q a b / (4 * r η a b)) z := rfl

private theorem dualAmp_norm_var (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualVarTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualVarTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le

private theorem dualAmp_norm_fixed (η a b : ℝ) (z : ℤ × ℤ) :
    ‖dualFixedTerm η a b z‖ = dualAmp η a b z := by
  dsimp [dualFixedTerm]
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real]
  exact abs_of_nonneg (Real.exp_pos _).le

private theorem dualAmp_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualAmp η a b) := by
  have hr : 0 < r η a b := r_pos hη hq
  have ht : 0 < η * q a b / (4 * r η a b) := by positivity
  convert! dualRealGauss_summable ht using 1
  all_goals funext z
  all_goals exact dualAmp_eq_realGauss η a b z

private theorem dualVar_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualVarTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_var η a b z))

private theorem dualFixed_summable {η a b : ℝ} (hη : 0 < η) (hq : 0 < q a b) :
    Summable (dualFixedTerm η a b) :=
  (dualAmp_summable hη hq).of_norm_bounded
    (fun z => le_of_eq (dualAmp_norm_fixed η a b z))

private theorem dualAmp_le_small {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2)
    (z : ℤ × ℤ) :
    dualAmp η a b z ≤ dualRealGauss (η * q a b / 8) z := by
  have hr : 0 < r η a b := r_pos hη hq
  have hp : 0 < η * q a b := mul_pos hη hq
  have ht : η * q a b / 8 ≤ η * q a b / (4 * r η a b) := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (by positivity : 0 < 4 * r η a b)).2
    nlinarith [mul_le_mul_of_nonneg_left hrle hp.le]
  dsimp [dualAmp, dualRealGauss]
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_right ht
    (mul_nonneg Real.pi_pos.le (dualQ_nonneg z))
  nlinarith [hm]

noncomputable def phaseErrorConstant (a b : ℝ) : ℝ :=
  (Real.pi / 2) * phaseBoundConstant a b * phaseA a b

private theorem phaseErrorConstant_nonneg {a b : ℝ} (hq : 0 < q a b) :
    0 ≤ phaseErrorConstant a b := by
  unfold phaseErrorConstant
  exact mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
    (phaseBoundConstant_pos a b).le) (phaseA_nonneg hq.le)

theorem normalized_dual_phase_sum_error {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (hrle : r η a b ≤ 2) :
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ ≤
      phaseErrorConstant a b * η ^ 3 *
        (∑' z : ℤ × ℤ,
          dualQ z * dualRealGauss (η * q a b / 8) z) := by
  let t : ℝ := η * q a b / 8
  have ht : 0 < t := by dsimp [t]; positivity
  have hK : 0 ≤ phaseErrorConstant a b := phaseErrorConstant_nonneg hq
  have hpoint (z : ℤ × ℤ) :
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        (phaseErrorConstant a b * η ^ 2) *
          (dualQ z * dualRealGauss t z) := by
    have hbase := dual_phase_term_error hη hq z
    have hamp := dualAmp_le_small hη hq hrle z
    have hfac : 0 ≤
        ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (half_pos Real.pi_pos).le
          (phaseBoundConstant_pos a b).le) (dualQ_nonneg z))
        (mul_nonneg (phaseA_nonneg hq.le) (sq_nonneg η))
    have hmul := mul_le_mul_of_nonneg_right hamp hfac
    dsimp [t, phaseErrorConstant]
    calc
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖ ≤
        dualAmp η a b z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := hbase
      _ ≤ dualRealGauss (η * q a b / 8) z *
          ((Real.pi / 2) * phaseBoundConstant a b * dualQ z) *
          (phaseA a b * η ^ 2) := by nlinarith [hmul]
      _ = ((Real.pi / 2 * phaseBoundConstant a b * phaseA a b) * η ^ 2) *
          (dualQ z * dualRealGauss (η * q a b / 8) z) := by ring
  have hmajor : Summable (fun z : ℤ × ℤ =>
      (phaseErrorConstant a b * η ^ 2) *
        (dualQ z * dualRealGauss t z)) :=
    (dualMoment_summable ht).mul_left _
  have hnorm : Summable (fun z : ℤ × ℤ =>
      ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
    hmajor.of_nonneg_of_le (fun z => norm_nonneg _) hpoint
  have hsum := norm_tsum_le_tsum_norm hnorm
  have htsum := Summable.tsum_le_tsum hpoint hnorm hmajor
  have hvar := dualVar_summable hη hq
  have hfixed := dualFixed_summable hη hq
  calc
    η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
      (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖ =
      η * ‖(∑' z : ℤ × ℤ, (dualVarTerm η a b z - dualFixedTerm η a b z))‖ := by
        rw [hvar.tsum_sub hfixed]
    _ ≤ η * (∑' z : ℤ × ℤ,
          ‖dualVarTerm η a b z - dualFixedTerm η a b z‖) :=
      mul_le_mul_of_nonneg_left hsum hη.le
    _ ≤ η * (∑' z : ℤ × ℤ,
          (phaseErrorConstant a b * η ^ 2) *
            (dualQ z * dualRealGauss t z)) :=
      mul_le_mul_of_nonneg_left htsum hη.le
    _ = phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ, dualQ z * dualRealGauss (η * q a b / 8) z) := by
      rw [tsum_mul_left]
      dsimp [t]
      ring

open scoped Topology
open Filter

private theorem dual_moment_reindex (t : ℝ) :
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
      ∑' z : ℤ × ℤ,
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  calc
    (∑' z : ℤ × ℤ, dualQ z * dualRealGauss t z) =
        ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ (e z) * GaussianMoment.realGauss t (e z) := by
      apply tsum_congr
      intro z
      have hQ : RankTwoPoisson.eisQ (e z) = dualQ z := by
        rcases z with ⟨k,l⟩
        change (k : ℝ) ^ 2 - (k : ℝ) * ((-l : ℤ) : ℝ) +
          ((-l : ℤ) : ℝ) ^ 2 =
          (k : ℝ) ^ 2 + (k : ℝ) * (l : ℝ) + (l : ℝ) ^ 2
        push_cast
        ring
      simp only [GaussianMoment.realGauss, dualRealGauss, hQ]
    _ = ∑' z : ℤ × ℤ,
          RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z :=
      e.tsum_eq (fun z : ℤ × ℤ =>
        RankTwoPoisson.eisQ z * GaussianMoment.realGauss t z)

theorem normalized_dual_phase_sum_error_tendsto_zero {a b : ℝ}
    (hq : 0 < q a b) :
    Tendsto
      (fun η : ℝ =>
        η * ‖(∑' z : ℤ × ℤ, dualVarTerm η a b z) -
          (∑' z : ℤ × ℤ, dualFixedTerm η a b z)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let K : ℝ := q a b / 8
  have hK : 0 < K := by dsimp [K]; positivity
  have hmoment :
      Tendsto
        (fun η : ℝ => η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert! GaussianMoment.scaled_moment_vanishes_const K hK using 1
    funext η
    dsimp [K]
    rw [dual_moment_reindex]
    ring_nf
  have hright :
      Tendsto
        (fun η : ℝ => phaseErrorConstant a b * η ^ 3 *
          (∑' z : ℤ × ℤ,
            dualQ z * dualRealGauss (η * q a b / 8) z))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert! hmoment.const_mul (phaseErrorConstant a b) using 1
    · funext η
      ring
    · simp
  have hr_lim : Tendsto (fun η : ℝ => r η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt (fun η : ℝ => r η a b) 0 := by
      unfold r
      fun_prop
    simpa [r] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hrle : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), r η a b ≤ 2 := by
    have hevent : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), x ≤ 2 :=
      eventually_le_nhds (by norm_num)
    exact hr_lim.eventually hevent
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hright
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact mul_nonneg hη.le (norm_nonneg _)
  · filter_upwards [self_mem_nhdsWithin, hrle] with η hη hbound
    exact normalized_dual_phase_sum_error hη hq hbound

theorem dualGaussian_eq_dualVarTerm {η a b : ℝ}
    (hη : 0 < η) (hq : 0 < q a b) (z : ℤ × ℤ) :
    RankTwoComplex.dualGaussian (A η a b) (B η a b) (D η a b) z =
      dualVarTerm η a b z := by
  rw [dualGaussian_explicit hη hq z]
  have hQ :
      ((z.1 : ℂ) ^ 2 + (z.1 : ℂ) * (z.2 : ℂ) + (z.2 : ℂ) ^ 2) =
        (dualQ z : ℂ) := by
    dsimp [dualQ]
    push_cast
    ring
  have hT :
      (((a-b : ℝ) : ℂ) * (z.1 : ℂ) ^ 2 +
        2 * (a : ℂ) * (z.1 : ℂ) * (z.2 : ℂ) +
        (b : ℂ) * (z.2 : ℂ) ^ 2) =
        (dualTrace a b z : ℂ) := by
    dsimp [dualTrace]
    push_cast
    ring
  rw [hQ, hT]
  have hrC : (r η a b : ℂ) ≠ 0 := by
    exact_mod_cast (r_pos hη hq).ne'
  have harg :
      -(Real.pi : ℂ) *
        ((η : ℂ) * (q a b : ℂ) / (4 * (r η a b : ℂ)) *
          (dualQ z : ℂ) +
          Complex.I / (2 * (r η a b : ℂ)) * (dualTrace a b z : ℂ)) =
      (((-Real.pi * (η * q a b / (4 * r η a b)) * dualQ z : ℝ) : ℂ)) +
        Complex.I * ((phaseAngle a b z / r η a b : ℝ) : ℂ) := by
    dsimp [phaseAngle]
    push_cast
    field_simp [hrC]
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  rfl

end OscSpecial

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT

theorem osc_q_eq_eis_norm_sq (a b : ℤ) :
    OscSpecial.q (a : ℝ) (b : ℝ) =
      ‖eisEmbedding (ActualEisensteinCoordinates.eval a b)‖ ^ 2 := by
  rw [eisEmbedding_eval_norm_sq]
  dsimp [OscSpecial.q]
  push_cast
  ring

theorem two_coordinate_norm_four :
    let a := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((a*a-a*b+b*b : ℤ) : ℝ)) = 4 := by
  have h2 : (2 : O) = ActualEisensteinCoordinates.eval 2 0 := by
    simp [ActualEisensteinCoordinates.eval]
  rw [h2, ShortDraftLatticeCount.coords_eval]
  norm_num

end ActualEisensteinCubic

open Filter
open scoped Topology

theorem abel_transfer (P V W : ℝ → ℂ) (p w : ℂ)
    (hP : Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 p))
    (hW : Tendsto (fun η : ℝ => (η : ℂ) * W η) (𝓝[>] (0 : ℝ)) (𝓝 w))
    (hE : Tendsto (fun η => η * ‖V η - W η‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))) :
    Tendsto (fun η : ℝ => (η : ℂ) * (P η * V η))
      (𝓝[>] (0 : ℝ)) (𝓝 (p * w)) := by
  have hdiff : Tendsto (fun η : ℝ => (η : ℂ) * (V η - W η))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun η : ℝ => ‖(η : ℂ) * (V η - W η)‖) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun η => η * ‖V η - W η‖) := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    exact hE.congr' heq.symm
  have hV : Tendsto (fun η : ℝ => (η : ℂ) * V η)
      (𝓝[>] (0 : ℝ)) (𝓝 w) := by
    convert! hW.add hdiff using 1
    · funext η; ring
    · simp
  convert! hP.mul hV using 1
  · funext η; ring

namespace ActualEisensteinCubic

section

theorem gamma_scalar (n : ℝ) (hn : 0 < n) (G S : ℂ)
    (h : (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * G) =
      (((n / 2 : ℝ) : ℂ) *
        (((4 / (n*n) : ℝ) : ℂ) *
          (((2 / (Real.sqrt 3 * 4) : ℝ) : ℂ) * S)))) :
    G = S / 2 := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast at h
  field_simp [hnC, hsC] at h
  calc
    G = (2 * G) / 2 := by ring
    _ = S / 2 := by rw [h]

open EisensteinEmbedding ConcreteTraceCRT Complex

private theorem breveE_norm_one_all (z : ℂ) :
    ‖ShortDraftTrace.breveE z‖ = 1 := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (z + star z))‖ = 1
  rw [Complex.norm_exp]
  have hr : (2 * (Real.pi : ℂ) * Complex.I * (z + star z)).re = 0 := by
    simp [Complex.mul_re]
  rw [hr, Real.exp_zero]

theorem fixedDualPhase_norm_one (c y : O) :
    ‖fixedDualPhase c y‖ = 1 := by
  unfold fixedDualPhase
  exact breveE_norm_one_all _

end

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem variableDualPhase_abel_limit (a b : ℤ)
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
      (∑' y : O, fixedDualPhase c y *
        Complex.exp (-(Real.pi : ℂ) *
          (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
          (‖eisEmbedding y‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r))) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let c : O := ActualEisensteinCoordinates.eval a b
  let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
  let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
  let L2 : ℂ := ((2 / (Real.sqrt 3 *
    (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
  let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
  let W (η : ℝ) (y : O) := Complex.exp
    (-(Real.pi : ℂ) *
      (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
      (‖eisEmbedding y‖ ^ 2 : ℂ))
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  have hfiber (r : O ⧸ Ideal.span {(2 : O)}) :
      Tendsto (fun η : ℝ => (η : ℂ) *
        (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w)))
        (𝓝[>] (0 : ℝ)) (𝓝 K) := by
    let F : ℝ → ℂ := fun t => ∑' w : O,
      Complex.exp (-(Real.pi : ℂ) * (t : ℂ) *
        (‖eisEmbedding (GaussianShiftedPartition.representative 2 r + 2*w)‖ ^ 2 : ℂ))
    have hbase : Tendsto (fun t : ℝ => (t : ℂ) * F t)
        (𝓝[>] (0 : ℝ)) (𝓝 L2) := by
      simpa only [F, L2, a2, b2] using
        actual_O_fiber_gaussian_mass (2 : O)
          (GaussianShiftedPartition.representative 2 r) h2
    have h := OscSpecial.abel_mass_dual_scale (a : ℝ) (b : ℝ) hq F L2 hbase
    simpa only [W, F, K] using h
  have hsum : Tendsto (fun η : ℝ =>
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) * K)) := by
    apply tendsto_finsetSum Finset.univ
    intro r hr
    exact (hfiber r).const_mul _
  have hpoint (η : ℝ) (hη : 0 < η) :
      (η : ℂ) * (∑' y : O, fixedDualPhase c y * W η y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w))) := by
    have hrpos : 0 < OscSpecial.r η (a : ℝ) (b : ℝ) := by
      unfold OscSpecial.r
      positivity
    have htpos : 0 < OscSpecial.dualScale η (a : ℝ) (b : ℝ) := by
      unfold OscSpecial.dualScale
      positivity
    have hbase := (eis_gaussian_summable htpos).norm
    have hkernel : Summable (fun y : O => fixedDualPhase c y * W η y) := by
      apply hbase.of_norm_bounded
      intro y
      simp only [norm_mul]
      have hp : ‖fixedDualPhase c y‖ = 1 := fixedDualPhase_norm_one c y
      rw [hp, one_mul]
    have hpart := fixedDualPhase_weighted_partition c (W η) hkernel
    rw [hpart, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have heq : (fun η : ℝ => (η : ℂ) *
      (∑' y : O, fixedDualPhase c y * W η y)) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun η : ℝ => ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
        ((η : ℂ) * (∑' w : O, W η
          (GaussianShiftedPartition.representative 2 r + 2*w)))) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hpoint η hη
  have hlim := hsum.congr' heq.symm
  have hKsum :
      (∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) * K) =
      K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) := by
    rw [← Finset.sum_mul, mul_comm]
  rw [hKsum] at hlim
  exact hlim

end ActualEisensteinCubic

end

end OAI

end


