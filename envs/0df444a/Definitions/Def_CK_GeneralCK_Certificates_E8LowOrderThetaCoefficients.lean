-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8LowOrderThetaCoefficients
-- name    : CK_GeneralCK_Certificates_E8LowOrderThetaCoefficients
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:10:07.72384+00:00
-- url     : https://prove2.me/theorems/69ecf5d3-0676-49ab-a642-b20f441b3fc3
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8LowOrderThetaCoefficients` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8LowOrderThetaCoefficients` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8LowOrderThetaCoefficients` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8LowOrderThetaCoefficients (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8LowOrderThetaCoefficients.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticInverseRecurrence
import Definitions.Def_CK_GeneralCK_Certificates_DyadicLogSeries

-- ===== source module GeneralCK.Certificates.E8LowOrderThetaCoefficients =====
section

/-! Fixed-order algebra for the first nonlinear coefficients of the E8 inverse germ. -/

namespace GeneralCK.Certificates.E8LowOrderThetaCoefficients

open E8AnalyticGerm E8AnalyticInverseRecurrence
open E8AnalyticCoefficientBoxes E8OriginRemainder

private theorem powCoeff_two_five_odd (b : Nat -> Complex)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 2 5 = 0 := by
  simp [powCoeff, Finset.sum_range_succ, b0, b2, b4]

private theorem powCoeff_three_five_odd (b : Nat -> Complex)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 3 5 = 3 * b 1 ^ 2 * b 3 := by
  simp [powCoeff, Finset.sum_range_succ, b0, b2, b4]
  ring

private theorem powCoeff_four_five_odd (b : Nat -> Complex)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 4 5 = 0 := by
  simp [powCoeff, Finset.sum_range_succ, b0, b2, b4]

private theorem powCoeff_five_five_odd (b : Nat -> Complex)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    powCoeff b 5 5 = b 1 ^ 5 := by
  simp [powCoeff, Finset.sum_range_succ, b0, b2, b4]
  ring

/-- Order-five Faà di Bruno after the vanishing even coefficients are removed. -/
theorem composeCoeff_five_odd (a b : Nat -> Complex)
    (b0 : b 0 = 0) (b2 : b 2 = 0) (b4 : b 4 = 0) :
    composeCoeff a b 5 =
      a 1 * b 5 + 3 * a 3 * b 1 ^ 2 * b 3 + a 5 * b 1 ^ 5 := by
  simp only [composeCoeff, Finset.sum_range_succ]
  rw [powCoeff_one, powCoeff_two_five_odd b b0 b2 b4,
    powCoeff_three_five_odd b b0 b2 b4,
    powCoeff_four_five_odd b b0 b2 b4,
    powCoeff_five_five_odd b b0 b2 b4]
  simp [powCoeff]
  ring

theorem composeCoeff_three_odd (a b : Nat -> Complex)
    (b0 : b 0 = 0) (b2 : b 2 = 0) :
    composeCoeff a b 3 = a 1 * b 3 + a 3 * b 1 ^ 3 := by
  have hp2 : powCoeff b 2 3 = 0 := by
    simp [powCoeff, Finset.sum_range_succ, b0, b2]
  have hp3 : powCoeff b 3 3 = b 1 ^ 3 := by
    simp [powCoeff, Finset.sum_range_succ, b0, b2]
    ring
  simp only [composeCoeff, Finset.sum_range_succ]
  rw [powCoeff_one, hp2, hp3]
  simp [powCoeff]

private theorem logTwo_complex_ne : (Real.log 2 : Complex) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

private theorem clogTwo_eq : Complex.log (2 : Complex) = (Real.log 2 : Complex) :=
  (Complex.natCast_log (n := 2)).symm

private theorem clogTwo_ne : Complex.log (2 : Complex) ≠ 0 := by
  rw [clogTwo_eq]
  exact logTwo_complex_ne

theorem thetaTaylorCoeff_one :
    thetaTaylorCoeff 1 = 8 / (Real.log 2 : Complex) := by
  have hc := composeCoeff_theta_q 1
  norm_num [composeCoeff, powCoeff, Finset.sum_range_succ, targetCoeff,
    qTaylorCoeff_one] at hc
  rw [clogTwo_eq] at hc
  apply (eq_div_iff logTwo_complex_ne).2
  linear_combination 8 * hc

/-- Once the two nonlinear coefficients of the slope germ are evaluated,
the executable inverse recurrence gives the closed q3 formula. -/
theorem qTaylorCoeff_three_formula_of_theta
    (h3 : thetaTaylorCoeff 3 =
      64 / (3 * (Real.log 2 : Complex)) - 32 / (Real.log 2 : Complex) ^ 2) :
    qTaylorCoeff 3 =
      -(Real.log 2 : Complex) ^ 2 * (2 * (Real.log 2 : Complex) - 3) / 384 := by
  have hc := composeCoeff_theta_q 3
  rw [composeCoeff_three_odd thetaTaylorCoeff qTaylorCoeff qTaylorCoeff_zero
    (qTaylorCoeff_eq_zero_of_even (show Even 2 by decide))] at hc
  rw [thetaTaylorCoeff_one, h3, qTaylorCoeff_one] at hc
  change (8 / (Real.log 2 : Complex)) * qTaylorCoeff 3 +
    (64 / (3 * (Real.log 2 : Complex)) - 32 / (Real.log 2 : Complex) ^ 2) *
      ((Real.log 2 : Complex) / 8) ^ 3 = 0 at hc
  field_simp [logTwo_complex_ne] at hc ⊢
  simp [clogTwo_ne] at hc
  rw [clogTwo_eq] at hc
  linear_combination (1 / 32) * hc

/-- The corresponding fifth-order recurrence. -/
theorem qTaylorCoeff_five_formula_of_theta
    (h3 : thetaTaylorCoeff 3 =
      64 / (3 * (Real.log 2 : Complex)) - 32 / (Real.log 2 : Complex) ^ 2)
    (h5 : thetaTaylorCoeff 5 =
      384 / (5 * (Real.log 2 : Complex)) - 224 / (Real.log 2 : Complex) ^ 2 +
        192 / (Real.log 2 : Complex) ^ 3) :
    qTaylorCoeff 5 = (Real.log 2 : Complex) ^ 3 *
      (44 * (Real.log 2 : Complex) ^ 2 - 135 * (Real.log 2 : Complex) + 90) /
        122880 := by
  have hc := composeCoeff_theta_q 5
  rw [composeCoeff_five_odd thetaTaylorCoeff qTaylorCoeff qTaylorCoeff_zero
    (qTaylorCoeff_eq_zero_of_even (show Even 2 by decide))
    (qTaylorCoeff_eq_zero_of_even (show Even 4 by decide))] at hc
  rw [thetaTaylorCoeff_one, h3, h5, qTaylorCoeff_one,
    qTaylorCoeff_three_formula_of_theta h3] at hc
  norm_num [targetCoeff] at hc
  field_simp [logTwo_complex_ne] at hc ⊢
  simp [clogTwo_ne] at hc
  rw [clogTwo_eq] at hc
  linear_combination (1 / 4096) * hc

theorem qTaylorCoeff_three_in_sourceBox_of_theta
    (h3 : thetaTaylorCoeff 3 =
      64 / (3 * (Real.log 2 : Complex)) - 32 / (Real.log 2 : Complex) ^ 2) :
    ‖qTaylorCoeff 3 - (sourceCenter 3 : Complex)‖ ≤ (sourceHalfWidth 3 : Real) := by
  have hl := Real.sum_range_le_log_div (x := (1 / 3 : Real))
    (by norm_num) (by norm_num) 70
  have hu := Real.log_div_le_sum_range_add (x := (1 / 3 : Real))
    (by norm_num) (by norm_num) 70
  norm_num [Finset.sum_range_succ] at hl hu
  rw [qTaylorCoeff_three_formula_of_theta h3]
  have heq :
      -(Real.log 2 : Complex) ^ 2 * (2 * (Real.log 2 : Complex) - 3) / 384 -
          (sourceCenter 3 : Complex) =
        ((-(Real.log 2) ^ 2 * (2 * Real.log 2 - 3) / 384 -
          (sourceCenter 3 : Real) : Real) : Complex) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
  norm_num [sourceCenter, sourceHalfWidth, sourceBox, a3]
  constructor <;> nlinarith [sq_nonneg (Real.log 2 - 2 / 3),
    sq_nonneg (7 / 10 - Real.log 2)]

theorem qTaylorCoeff_five_in_sourceBox_of_theta
    (h3 : thetaTaylorCoeff 3 =
      64 / (3 * (Real.log 2 : Complex)) - 32 / (Real.log 2 : Complex) ^ 2)
    (h5 : thetaTaylorCoeff 5 =
      384 / (5 * (Real.log 2 : Complex)) - 224 / (Real.log 2 : Complex) ^ 2 +
        192 / (Real.log 2 : Complex) ^ 3) :
    ‖qTaylorCoeff 5 - (sourceCenter 5 : Complex)‖ ≤ (sourceHalfWidth 5 : Real) := by
  have hl := Real.sum_range_le_log_div (x := (1 / 3 : Real))
    (by norm_num) (by norm_num) 70
  have hu := Real.log_div_le_sum_range_add (x := (1 / 3 : Real))
    (by norm_num) (by norm_num) 70
  norm_num [Finset.sum_range_succ] at hl hu
  rw [qTaylorCoeff_five_formula_of_theta h3 h5]
  have heq :
      (Real.log 2 : Complex) ^ 3 *
          (44 * (Real.log 2 : Complex) ^ 2 - 135 * (Real.log 2 : Complex) + 90) /
          122880 - (sourceCenter 5 : Complex) =
        (((Real.log 2) ^ 3 *
          (44 * (Real.log 2) ^ 2 - 135 * Real.log 2 + 90) / 122880 -
          (sourceCenter 5 : Real) : Real) : Complex) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
  norm_num [sourceCenter, sourceHalfWidth, sourceBox, a5]
  let lo : Real := 2 *
    (2325760473904013634145345094599081659990371197488375883709756999268847086475462468067331056744976282577228958619985747185244 /
      6710726203993771723317218309814869996472227123771670224476645382798430427616596376412960555909137204157027962584781455822125 : Real)
  let hi : Real := 2 *
    (6202027930410703024387586918930884426640989859969002356559351998051329908090255661561769222085404872128745567109262594366109 /
      17895269877316724595512582159506319990592605663391120598604387687462481140310923670434561482424365877752074566892750548859000 : Real)
  let f : Real → Real := fun x => x ^ 3 * (44 * x ^ 2 - 135 * x + 90) / 122880
  have hlo : lo ≤ Real.log 2 := by dsimp [lo]; linarith
  have hhi : Real.log 2 ≤ hi := by dsimp [hi]; linarith
  have hLmem : Real.log 2 ∈ Set.Icc (69 / 100 : Real) (694 / 1000) := by
    constructor <;> linarith
  have hlomem : lo ∈ Set.Icc (69 / 100 : Real) (694 / 1000) := by
    constructor <;> norm_num [lo]
  have hhimem : hi ∈ Set.Icc (69 / 100 : Real) (694 / 1000) := by
    constructor <;> norm_num [hi]
  have hderiv (x : Real) : deriv f x =
      x ^ 2 * (220 * x ^ 2 - 540 * x + 270) / 122880 := by
    rw [show f = fun x : Real =>
      (90 * x ^ 3 - 135 * x ^ 4 + 44 * x ^ 5) / 122880 by
        funext x
        dsimp [f]
        ring]
    have hp := ((((hasDerivAt_id x).pow 3).const_mul 90).sub
      (((hasDerivAt_id x).pow 4).const_mul 135)).add
      (((hasDerivAt_id x).pow 5).const_mul 44)
    have hpd := hp.div_const 122880
    have hpd' := hpd.congr_of_eventuallyEq
      (f₁ := fun y : Real => (90 * y ^ 3 - 135 * y ^ 4 + 44 * y ^ 5) / 122880)
      (Filter.Eventually.of_forall (fun y => by simp [id_eq]))
    rw [hpd'.deriv]
    simp [id_eq]
    ring
  have hmono : StrictMonoOn f (Set.Icc (69 / 100 : Real) (694 / 1000)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (by fun_prop)
    intro x hx
    rw [hderiv]
    have hx' : 69 / 100 < x ∧ x < 694 / 1000 := by
      simpa [Set.mem_Ioo] using hx
    have hq : 0 < 220 * x ^ 2 - 540 * x + 270 := by
      nlinarith [sq_nonneg (x - 694 / 1000)]
    exact div_pos (mul_pos (sq_pos_of_pos (by linarith [hx'.1])) hq) (by norm_num)
  have hfl : f lo ≤ f (Real.log 2) :=
    hlo.eq_or_lt.elim (fun h => by rw [h]) (fun h => (hmono hlomem hLmem h).le)
  have hfu : f (Real.log 2) ≤ f hi :=
    hhi.eq_or_lt.elim (fun h => by rw [h]) (fun h => (hmono hLmem hhimem h).le)
  have hblo : (a5.lo : Real) ≤ f lo := by norm_num [f, lo, a5]
  have hbhi : f hi ≤ (a5.hi : Real) := by norm_num [f, hi, a5]
  have hbox : (a5.lo : Real) ≤ f (Real.log 2) ∧
      f (Real.log 2) ≤ (a5.hi : Real) :=
    ⟨hblo.trans hfl, hfu.trans hbhi⟩
  norm_num [a5] at hbox
  dsimp [f] at hbox
  constructor <;> linarith [hbox.1, hbox.2]

theorem qTaylorCoeff_three_five_in_sourceBoxes_of_theta
    (h3 : thetaTaylorCoeff 3 =
      64 / (3 * (Real.log 2 : Complex)) - 32 / (Real.log 2 : Complex) ^ 2)
    (h5 : thetaTaylorCoeff 5 =
      384 / (5 * (Real.log 2 : Complex)) - 224 / (Real.log 2 : Complex) ^ 2 +
        192 / (Real.log 2 : Complex) ^ 3) :
    (‖qTaylorCoeff 3 - (sourceCenter 3 : Complex)‖ ≤ (sourceHalfWidth 3 : Real)) ∧
    (‖qTaylorCoeff 5 - (sourceCenter 5 : Complex)‖ ≤ (sourceHalfWidth 5 : Real)) :=
  ⟨qTaylorCoeff_three_in_sourceBox_of_theta h3,
    qTaylorCoeff_five_in_sourceBox_of_theta h3 h5⟩

end GeneralCK.Certificates.E8LowOrderThetaCoefficients

end


