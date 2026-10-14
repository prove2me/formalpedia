-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0419_parallel1
-- name    : PNT_ZeroFree_433_0419_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:14:41.393972+00:00
-- url     : https://prove2.me/theorems/005850b7-aeb5-44c2-9d32-b141d360ae3b
-- title:
--   Zero-free region foundations: Detector.LocalWeights, Detector.Euler, Detector.Local, Detector.CorrectionBounds [0419_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Detector.LocalWeights
--   - OAI.NumberTheory.DirichletL.Detector.Euler
--   - OAI.NumberTheory.DirichletL.Detector.Local
--   - OAI.NumberTheory.DirichletL.Detector.CorrectionBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/LocalWeights.lean#L9-L88
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/Euler.lean#L11-L43
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/Local.lean#L11-L93
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/CorrectionBounds.lean#L11-L82

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/LocalWeights.lean#L9-L88
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/Euler.lean#L11-L43
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/Local.lean#L11-L93
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/CorrectionBounds.lean#L11-L82
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Detector.LocalWeights
section
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma even_diagonal_exponent (r : ℕ) : r + (2*r).choose 2 = 2*r*r := by
  rw [Nat.choose_two_right, mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  cases r with
  | zero => simp
  | succ r =>
    rw [show 2*(r+1)-1 = 2*r+1 by omega]
    ring

def localCubePhase (C omega : ℂ) (e l k : ℕ) : ℂ :=
  C^l * omega^((e+3*l)*k+e*l+l.choose 2)

theorem localCubePhase_even (C omega : ℂ) (hC : C^2=omega) (ho : omega^2=1)
    (e r k : ℕ) : localCubePhase C omega e (2*r) k = omega^(e*k) := by
  unfold localCubePhase
  rw [pow_mul C 2 r, hC, ← pow_add]
  have he : r+((e+3*(2*r))*k+e*(2*r)+(2*r).choose 2) =
      e*k+2*(3*r*k+e*r+r*r) := by
    have hd := even_diagonal_exponent r
    nlinarith
  rw [he, pow_add, pow_mul omega 2, ho, one_pow, mul_one]

def weightedScalar (Q eta a G1 C omega X W V scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (-eta*X/G1)^e * (a*X^3/Q)^l * localCubePhase C omega e l k * scalar * W^k * V^m

lemma weightedScalar_zero (Q eta a G1 C omega X W V : ℂ) (e l k m : ℕ) :
    weightedScalar Q eta a G1 C omega X W V 0 e l k m = 0 := by
  simp [weightedScalar]

def evenRatio (Q a X V : ℂ) : ℂ := a^2*Q^4*X^6*V

lemma weighted_squarefree_boundary (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r)*G1) 1 (2*r) 0 r =
      evenRatio Q a X V ^ r * (-eta*X) := by
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [mul_zero, pow_zero, pow_one, mul_one]
  unfold evenRatio
  rw [mul_pow, mul_pow, mul_pow, div_pow, mul_pow, pow_mul, pow_mul, pow_mul, pow_mul]
  field_simp
  ring

lemma weighted_even_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+5)*(Q-1))
      0 (2*r+2) 0 (r+1+d) =
      evenRatio Q a X V ^ r * (evenRatio Q a X V*(1-Q⁻¹)*V^d) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [zero_mul, pow_zero, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_even_kone (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r : ℕ) :
    weightedScalar Q eta a G1 C omega X W V (Q^(6*r+6))
      0 (2*r+2) 1 (r+1) = evenRatio Q a X V ^ r * (W*evenRatio Q a X V) := by
  unfold weightedScalar
  rw [show 2*r+2=2*(r+1) by ring, localCubePhase_even C omega hC ho]
  simp only [pow_zero, pow_one, one_mul, mul_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

lemma weighted_squarefree_bulk (Q eta a G1 C omega X W V : ℂ)
    (hQ : Q ≠ 0) (hG : G1 ≠ 0) (hC : C^2=omega) (ho : omega^2=1) (r d : ℕ) :
    weightedScalar Q eta a G1 C omega X W V
      ((omega⁻¹*G1)*(Q^(6*r)*(Q-1))) 1 (2*r) 1 (r+1+d) =
      evenRatio Q a X V ^ r * (-eta*(Q-1)*X*W*V^(d+1)) := by
  have hω : omega ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at ho; norm_num at ho
  unfold weightedScalar
  rw [localCubePhase_even C omega hC ho]
  simp only [one_mul, pow_one]
  unfold evenRatio
  simp only [mul_pow, div_pow, pow_add, pow_mul]
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.Euler
section
namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

def markedFactor (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ((R * (1 - qInv) - K * V ^ a) / (1 - V) + J) / (1 - R)

def markedTableSeries (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ∑' r : ℕ, R ^ r *
    ((∑' m : ℕ, (R * (1 - qInv) * V ^ m - K * V ^ (m + a))) + J)

theorem marked_table_resummation (R V qInv K J : ℂ) (a : ℕ)
    (hR : ‖R‖ < 1) (hV : ‖V‖ < 1) :
    markedTableSeries R V qInv K J a = markedFactor R V qInv K J a := by
  have hgeo := hasSum_geometric_of_norm_lt_one hV
  have hfirst := hgeo.mul_left (R * (1 - qInv))
  have hsecond : HasSum (fun m : ℕ => K * V ^ (m + a))
      (K * V ^ a * (1 - V)⁻¹) := by
    convert! hgeo.mul_left (K * V ^ a) using 1
    funext m
    rw [pow_add]
    ring
  have hin := (hfirst.sub hsecond).tsum_eq
  unfold markedTableSeries
  rw [hin, tsum_mul_right, tsum_geometric_of_norm_lt_one hR]
  unfold markedFactor
  simp only [div_eq_mul_inv]
  ring

theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.Local
section
namespace OAI

namespace SevenEighths.ProbeLocal
noncomputable section

def localFactor (V W Pstar : ℂ) : ℂ := 1 / (1 - V) + W / (1 - W) + Pstar

def localCorrection (V W D Pstar : ℂ) : ℂ :=
  localFactor V W Pstar * ((1 - V) * (1 - W)) / (1 - D)

def continuedCorrection (V W D Pstar : ℂ) : ℂ :=
  (1 - V * W + (1 - V) * (1 - W) * Pstar) / (1 - D)

theorem continuedCorrection_eq_raw (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar = localCorrection V W D Pstar := by
  unfold continuedCorrection localCorrection localFactor
  field_simp
  ring

def compensatedReplacement (V W D Pstar B q : ℂ) : ℂ :=
  ((B - q) * (1 - V) * (1 - W) * Pstar - q * (1 - V * W)) / (1 - D)

theorem correction_defect (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    localCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold localCorrection localFactor
  field_simp
  ring

theorem compensatedReplacement_eq_raw (V W D Pstar B q : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hP : localFactor V W Pstar ≠ 0) :
    compensatedReplacement V W D Pstar B q =
      localCorrection V W D Pstar * (B * Pstar / localFactor V W Pstar - q) := by
  unfold localCorrection compensatedReplacement
  field_simp
  unfold localFactor
  field_simp
  ring

theorem compensatedReplacement_ramified (V Pstar B q : ℂ) (hV : 1 - V ≠ 0) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * localCorrection V 0 0 Pstar := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  ring

theorem normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        localCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

theorem continuedCorrection_defect (V W D Pstar : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

theorem continued_normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        continuedCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement continuedCorrection
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

theorem continued_ramified_compensation (V Pstar B q : ℂ) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * continuedCorrection V 0 0 Pstar := by
  simp only [compensatedReplacement, continuedCorrection, mul_zero, sub_zero,
    mul_one, div_one]
  ring

end
end SevenEighths.ProbeLocal

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.CorrectionBounds
section
namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

lemma one_sub_ne_zero_of_norm_le_half (a : ℂ) (ha : ‖a‖ ≤ 1/2) : 1 - a ≠ 0 := by
  intro h
  have : a = 1 := by linear_combination -h
  rw [this, norm_one] at ha
  norm_num at ha

lemma inv_one_sub_norm_le_two (a : ℂ) (ha : ‖a‖ ≤ 1/2) : ‖(1-a)⁻¹‖ ≤ 2 := by
  have hl := norm_sub_norm_le (1 : ℂ) a
  simp only [norm_one] at hl
  have hd : 0 < ‖1-a‖ := by linarith
  rw [norm_inv, ← one_div, div_le_iff₀ hd]
  linarith

theorem unramified_marked_error_bound (R V qInv K W D : ℂ)
    (hR : ‖R‖ ≤ 1/2) (hV : ‖V‖ ≤ 1/2) (hq : ‖qInv‖ ≤ 1) (hD : ‖D‖ ≤ 1/2) :
    ‖ProbeEuler.markedFactor R V qInv K (-D + W*R) 1 + D‖ ≤
      12 * ‖R‖ * (1 + ‖W‖) + 4 * ‖K‖ * ‖V‖ := by
  rw [ProbeEuler.unramified_marked_error R V qInv K W D
    (one_sub_ne_zero_of_norm_le_half R hR) (one_sub_ne_zero_of_norm_le_half V hV),
    div_eq_mul_inv, mul_inv, norm_mul, norm_mul]
  have hnum : ‖R*((1-qInv)+(1-V)*(W-D))-K*V‖ ≤
      ‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖ := by
    calc
      _ ≤ ‖R*((1-qInv)+(1-V)*(W-D))‖ + ‖K*V‖ := norm_sub_le _ _
      _ = ‖R‖ * ‖(1-qInv)+(1-V)*(W-D)‖ + ‖K‖*‖V‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖R‖ * (‖1-qInv‖ + ‖1-V‖*‖W-D‖) + ‖K‖*‖V‖ := by
        gcongr
        simpa only [norm_mul] using norm_add_le (1-qInv) ((1-V)*(W-D))
      _ ≤ ‖R‖ * (2 + (1+‖V‖)*(‖W‖+‖D‖)) + ‖K‖*‖V‖ := by
        gcongr
        · calc ‖1-qInv‖ ≤ ‖(1:ℂ)‖+‖qInv‖ := norm_sub_le _ _
               _ ≤ 2 := by simp only [norm_one]; linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) V
        · exact norm_sub_le W D
  have hv := inv_one_sub_norm_le_two V hV
  have hr := inv_one_sub_norm_le_two R hR
  calc
    _ ≤ (‖R‖ * (2 + (1 + ‖V‖) * (‖W‖ + ‖D‖)) + ‖K‖ * ‖V‖) * (2*2) := by
      gcongr
    _ ≤ 12 * ‖R‖ * (1+‖W‖) + 4*‖K‖*‖V‖ := by
      have he : 2 + (1+‖V‖)*(‖W‖+‖D‖) ≤ 3*(1+‖W‖) := by
        have : (1+‖V‖)*(‖W‖+‖D‖) ≤ (3/2:ℝ)*(‖W‖+1/2) := by gcongr ; linarith
        nlinarith [norm_nonneg W]
      nlinarith [mul_le_mul_of_nonneg_left he (norm_nonneg R)]

theorem continuedCorrection_defect_bound (V W D Pstar : ℂ)
    (hV : ‖V‖ ≤ 1/2) (hD : ‖D‖ ≤ 1/2) :
    ‖continuedCorrection V W D Pstar - 1‖ ≤
      2 * (‖D‖ * (‖V‖+‖W‖+‖V‖*‖W‖) + ‖V‖*‖W‖ +
        2*(1+‖W‖)*‖Pstar+D‖) := by
  rw [continuedCorrection_defect _ _ _ _ (one_sub_ne_zero_of_norm_le_half D hD),
    div_eq_mul_inv, norm_mul]
  have hA : ‖V+W-V*W‖ ≤ ‖V‖+‖W‖+‖V‖*‖W‖ := by
    calc
      _ ≤ ‖V+W‖+‖V*W‖ := norm_sub_le _ _
      _ ≤ _ := by rw [norm_mul]; gcongr; exact norm_add_le V W
  have hnum : ‖D*(V+W-V*W)-V*W+(1-V)*(1-W)*(Pstar+D)‖ ≤
      ‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖ := by
    calc
      _ ≤ ‖D*(V+W-V*W)-V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := norm_add_le _ _
      _ ≤ ‖D*(V+W-V*W)‖+‖V*W‖+‖(1-V)*(1-W)*(Pstar+D)‖ := by gcongr; exact norm_sub_le _ _
      _ = ‖D‖*‖V+W-V*W‖+‖V‖*‖W‖+‖1-V‖*‖1-W‖*‖Pstar+D‖ := by simp only [norm_mul]
      _ ≤ _ := by
        gcongr
        · calc ‖1-V‖ ≤ 1+‖V‖ := by simpa only [norm_one] using norm_sub_le (1:ℂ) V
               _ ≤ 2 := by linarith
        · simpa only [norm_one] using norm_sub_le (1:ℂ) W
  calc
    _ ≤ (‖D‖*(‖V‖+‖W‖+‖V‖*‖W‖)+‖V‖*‖W‖+2*(1+‖W‖)*‖Pstar+D‖)*2 := by
      gcongr
      exact inv_one_sub_norm_le_two D hD
    _ = _ := by ring

end SevenEighths.ProbeLocal
end

end OAI

end


