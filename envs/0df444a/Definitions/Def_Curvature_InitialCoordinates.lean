-- Prove2me | Definitions.Def_Curvature_InitialCoordinates
-- name    : Curvature_InitialCoordinates
-- status  : Definition
-- author  : @ssakaue
-- created : 2026-11-24T07:09:40.082062+00:00
-- url     : https://prove2.me/theorems/a7075f21-7928-4db2-809f-9821b2ae9ebd
-- title:
--   Coefficient cost and surviving dyadic levels in a coordinate initialization
-- statement:
--   This file defines the cost of a coefficient vector and the quantities that describe which dyadic initial levels survive in each coordinate. For lengths $\ell\in(0,\infty)^N$, thresholds $h\in(0,\infty)^N$ and coefficients $v\in\mathbb R^N$, the **coefficient cost** is
--
--   $$
--   \Phi_{\ell,h}(v)\coloneqq\sum_{j=1}^N\ell_j\Bigl(h_j+|v_j|\bigl(1+\log\max\{1,|v_j|/h_j\}\bigr)\Bigr).
--   $$
--
--   For each point of the domain, minimize the coefficient cost over the vectors $v\in[-1,1]^N$ that represent the point. The file `Def_Curvature_DyadicRun.lean` defines the representation cost as the supremum of these minima over the domain (Appendix A.1).
--
--   In one coordinate with smallest threshold $h$, the dyadic levels $k=0,\ldots,n-1$ have thresholds $2^kh$, and each level is either revoked or surviving. The surviving weight of the coordinate is $1+\sum_k(2^kh)^{-1}$ over the surviving levels $k$, and the surviving diagonal matrix has the entries $c\,\ell_j$ times the surviving weight of coordinate $j$, for a scale $c>0$. For one coordinate, the file bounds the signed sum of the initial terms, each evaluated at the end point of its level, jointly with the trace term computed from the surviving weight. The file also bounds a single created term at its revocation point or at the final iterate. These bounds are used in Appendices B.4 and B.5.
-- source:
--   arXiv:2611.27572v1, Appendix A.1, p. 23; Appendices B.4–B.5, pp. 37–39. https://arxiv.org/html/2611.27572v1#A2.SS5

import Definitions.Def_Curvature_BallState
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
set_option autoImplicit false
namespace Curvature

theorem revokedDropNonpos (ε v δ ρ S : ℝ)
    (hε : 0 < ε) (hε' : ε ≤ 1) (hv : 0 < v)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ v) (hS : S ≤ v / 2)
    (hρ : 8 * v / ε ≤ |ρ|) :
    (ε ^ 2 / (48 * v)) / 2 * (δ ^ 2 - (δ - ρ) ^ 2) + S ≤ 0 := by
  let threshold := 8 * v / ε
  let coefficient := (ε ^ 2 / (48 * v)) / 2
  have hprod : ρ * δ ≤ |ρ| * v :=
    mul_le_mul (le_abs_self ρ) hδ' hδ (abs_nonneg ρ)
  have habsDecrease : |ρ| * (|ρ| - 2 * v) ≤ ρ ^ 2 - 2 * ρ * δ := by
    calc
      |ρ| * (|ρ| - 2 * v) = ρ ^ 2 - 2 * (|ρ| * v) := by
        rw [mul_sub, ← pow_two, sq_abs]
        ring
      _ ≤ ρ ^ 2 - 2 * ρ * δ := by linarith
  have hthreshold : 2 * v ≤ threshold := by
    apply (le_div_iff₀ hε).2
    nlinarith [mul_le_mul_of_nonneg_right hε' hv.le]
  have hdecrease : threshold * (threshold - 2 * v) ≤ ρ ^ 2 - 2 * ρ * δ :=
    (mul_le_mul hρ (sub_le_sub_right hρ _) (sub_nonneg.mpr hthreshold)
      (abs_nonneg ρ)).trans habsDecrease
  have hcoeff : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  calc
    coefficient * (δ ^ 2 - (δ - ρ) ^ 2) + S
        ≤ -(coefficient * (threshold * (threshold - 2 * v))) + v / 2 := by
      rw [show δ ^ 2 - (δ - ρ) ^ 2 = -(ρ ^ 2 - 2 * ρ * δ) by ring, mul_neg]
      exact add_le_add (neg_le_neg (mul_le_mul_of_nonneg_left hdecrease hcoeff)) hS
    _ = (ε - 1) * v / 6 := by
      dsimp [coefficient, threshold]
      field_simp [hε.ne', hv.ne']
      ring
    _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hε') hv.le) (by positivity)

end Curvature

end

section
set_option autoImplicit false
namespace Curvature

private theorem sum_dyadic_shift (f : ℝ → ℝ) (n : ℕ) (h : ℝ) :
    (∑ k ∈ Finset.range (n + 1), f (2 ^ k * h)) =
      f h + ∑ k ∈ Finset.range n, f (2 ^ k * (2 * h)) := by
  rw [Finset.sum_range_succ']
  simp only [pow_succ, mul_assoc, pow_zero, one_mul]
  ring

private theorem dyadic_tail (n : ℕ) (h a c : ℝ) (hh : 0 < h) (hc : 0 < c) :
    (∑ k ∈ Finset.range n, a ^ 2 / (c * (2 ^ k * h))) ≤ 2 * a ^ 2 / (c * h) := by
  induction n generalizing h with
  | zero => simp; positivity
  | succ n ih =>
    rw [sum_dyadic_shift (fun x => a ^ 2 / (c * x))]
    calc
      _ ≤ a ^ 2 / (c * h) + 2 * a ^ 2 / (c * (2 * h)) :=
        add_le_add_right (ih (2 * h) (by positivity)) _
      _ = _ := by field_simp; ring

theorem dyadicClippedSum_le (n : ℕ) (h a c : ℝ) (hh : 0 < h) (ha : 0 ≤ a) (hc : 0 < c) :
    (∑ k ∈ Finset.range n, min (6 * a) (a ^ 2 / (c * (2 ^ k * h)))) ≤
      6 * a * max 0 (Real.logb 2 (a / h)) + (6 + 2 / c) * a := by
  induction n generalizing h with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  | succ n ih =>
    rw [sum_dyadic_shift (fun x => min (6 * a) (a ^ 2 / (c * x)))]
    by_cases hbig : 2 * h < a
    · have ha' : 0 < a := by linarith
      have hx : 1 ≤ a / (2 * h) := (one_le_div (by positivity)).mpr hbig.le
      have hy : 1 ≤ a / h := (one_le_div hh).mpr (by linarith)
      have hlog : Real.logb 2 (a / h) = Real.logb 2 (a / (2 * h)) + 1 := by
        have he : a / h = (a / (2 * h)) * 2 := by field_simp
        rw [he, Real.logb_mul (by positivity) (by norm_num), Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
      have ht := ih (2 * h) (by positivity)
      rw [max_eq_right (Real.logb_nonneg (by norm_num) hx)] at ht
      rw [max_eq_right (Real.logb_nonneg (by norm_num) hy), hlog]
      linarith only [ht, min_le_left (6 * a) (a ^ 2 / (c * h))]
    · have ht := (Finset.sum_le_sum (s := Finset.range n) (fun k _ =>
          min_le_right (6 * a) (a ^ 2 / (c * (2 ^ k * (2 * h)))))).trans
          (dyadic_tail n (2 * h) a c (by positivity) hc)
      have hs : 2 * a ^ 2 / (c * (2 * h)) ≤ 2 / c * a := by
        apply (div_le_iff₀ (by positivity)).mpr
        calc
          2 * a ^ 2 ≤ 2 * a * (2 * h) := by nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hbig) ha]
          _ = 2 / c * a * (c * (2 * h)) := by field_simp
      have hn : 0 ≤ 6 * a * max 0 (Real.logb 2 (a/h)) := by positivity
      linarith only [ht.trans hs, min_le_left (6 * a) (a ^ 2 / (c * h)), hn]

/-- The signed initial term and the trace cost at one threshold. -/
theorem initialOneScale (x v h β : ℝ) (revoked : Bool) (hh : 0 < h)
    (hβ : β ≤ 25/64) (hx : |x| ≤ 3*h) (hit : revoked = true → h ≤ |x|) :
    (2*x*v-x^2)/h + (if revoked then β*h else 0) ≤
      min (6*|v|) (|v|^2 / ((39/64)*h)) := by
  have hcredit : (if revoked then β*h else 0) * h ≤ (25/64 : ℝ) * x^2 := by
    cases revoked with
    | false => simp; positivity
    | true =>
      simp only [if_true]
      have hsq := pow_le_pow_left₀ hh.le (hit rfl) 2
      rw [sq_abs] at hsq
      nlinarith [mul_le_mul_of_nonneg_right hβ (sq_nonneg h)]
  apply le_min
  · rw [← le_sub_iff_add_le, div_le_iff₀ hh]
    have habs : x*v ≤ |x| * |v| := by simpa [abs_mul] using le_abs_self (x*v)
    nlinarith [mul_le_mul_of_nonneg_right hx (abs_nonneg v), sq_nonneg x]
  · rw [sq_abs, ← le_sub_iff_add_le, div_le_iff₀ hh]
    have hc : (v^2 / ((39/64)*h)) * h = (64/39)*v^2 := by field_simp
    nlinarith [sq_nonneg ((39/64 : ℝ)*x-v)]

theorem initialScales (J : ℕ) (h v β : ℝ) (hh : 0 < h) (x : ℕ → ℝ) (revoked : ℕ → Bool)
    (hβ : β ≤ 25/64) (hend : ∀ k < J, |x k| ≤ 3 * (2^k*h))
    (hit : ∀ k < J, revoked k = true → 2^k*h ≤ |x k|) :
    (∑ k ∈ Finset.range J, ((2*x k*v-(x k)^2)/(2^k*h) +
      if revoked k then β*(2^k*h) else 0)) ≤
      6*|v| * max 0 (Real.logb 2 (|v|/h)) + (6+2/(39/64 : ℝ))*|v| := by
  apply le_trans _ (dyadicClippedSum_le J h |v| (39/64) hh (abs_nonneg _) (by norm_num))
  exact Finset.sum_le_sum fun k hk =>
    initialOneScale (x k) v _ β (revoked k) (by positivity) hβ
      (hend k (Finset.mem_range.mp hk)) (hit k (Finset.mem_range.mp hk))

end Curvature

end

section
set_option autoImplicit false
namespace Curvature

/-- Bound a single created regularization term at its revocation point or the final iterate. -/
theorem termLifetimeBound {d : ℕ} (a : Term d) (start added ending u : Vec d)
    (ε v S : ℝ) (revoked : Bool) (hε : 0 < ε) (hε' : ε ≤ 1) (hv : 0 < v)
    (hm : a.m = dotProduct a.q added) (hγ : a.γ = ε ^ 2 / (48 * v))
    (hδ : 0 ≤ dotProduct a.q (start - added))
    (hδ' : dotProduct a.q (start - added) ≤ v) (hS : S ≤ v / 2)
    (hend : |a.residual ending| ≤ 3 * (8 * v / ε))
    (hhit : revoked = true → 8 * v / ε ≤ |a.residual ending|) :
    a.value u - a.divergence u ending + S ≤
      ε / 2 * |excess a.q start u| + (if revoked then 0 else (1 + ε ^ 2 / 48) * v / 2) := by
  let δ := dotProduct a.q (start - added)
  let r := excess a.q start u
  let ρ := a.residual ending
  have hcoeff : 0 ≤ a.γ := by rw [hγ]; positivity
  have hcross : -(a.γ * ρ * r) ≤ ε / 2 * |r| := by
    calc
      -(a.γ * ρ * r) ≤ |a.γ * ρ * r| := neg_le_abs _
      _ = a.γ * |ρ| * |r| := by rw [abs_mul, abs_mul, abs_of_nonneg hcoeff]
      _ ≤ (a.γ * (3 * (8 * v / ε))) * |r| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hend hcoeff) (abs_nonneg _)
      _ = ε / 2 * |r| := by rw [hγ]; field_simp; ring
  have hres : a.residual u = δ - r := by
    simp [δ, r, Term.residual, excess, hm, dotProduct_sub]
  have hdisp : dotProduct a.q (u - ending) = δ - r - ρ := by
    simp [δ, r, ρ, Term.residual, excess, hm, dotProduct_sub]
  have hid : a.value u - a.divergence u ending + S =
      a.γ / 2 * (δ ^ 2 - (δ - ρ) ^ 2) + S - a.γ * ρ * r := by
    unfold Term.value Term.divergence
    rw [hres, hdisp]
    ring
  rw [hid]
  change _ ≤ ε / 2 * |r| + _
  cases revoked with
  | true =>
    have h := revokedDropNonpos ε v δ ρ S hε hε' hv hδ hδ' hS (hhit rfl)
    rw [← hγ] at h
    simp only [ite_true, add_zero]
    linarith
  | false =>
    have hsq : δ ^ 2 ≤ v ^ 2 := sq_le_sq' (by linarith [show 0 ≤ δ from hδ]) hδ'
    have hpos : 0 ≤ a.γ / 2 := by positivity
    have hpart := mul_le_mul_of_nonneg_left
      (show δ ^ 2 - (δ - ρ) ^ 2 ≤ v ^ 2 by linarith [sq_nonneg (δ - ρ)]) hpos
    have hid' : a.γ / 2 * v ^ 2 + v / 2 = (1 + ε ^ 2 / 48) * v / 2 := by
      rw [hγ]
      field_simp
      ring
    simp only [Bool.false_eq_true, ↓reduceIte]
    linarith

end Curvature

end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

def activeScaleWeight (n : ℕ) (h : ℝ) (revoked : ℕ → Bool) : ℝ :=
  1 + ∑ k ∈ Finset.range n, if revoked k then 0 else (2 ^ k * h)⁻¹

def revokedScaleSum (n : ℕ) (h : ℝ) (revoked : ℕ → Bool) : ℝ :=
  ∑ k ∈ Finset.range n, if revoked k then 2 ^ k * h else 0

theorem activeScaleWeight_pos (n : ℕ) {h : ℝ} (hh : 0 < h) (revoked : ℕ → Bool) :
    0 < activeScaleWeight n h revoked := by
  unfold activeScaleWeight
  have hn : 0 ≤ ∑ k ∈ Finset.range n, if revoked k then (0 : ℝ) else (2 ^ k * h)⁻¹ :=
    Finset.sum_nonneg fun k _ => by split <;> positivity
  linarith

/-- Bounds the inverse diagonal entry for any subset of surviving dyadic levels. -/
theorem activeScaleWeight_inv_le (n : ℕ) (h : ℝ) (revoked : ℕ → Bool)
    (hh : 0 < h) (hfinal : 1 ≤ 2 ^ n * h) :
    (activeScaleWeight n h revoked)⁻¹ ≤ h + revokedScaleSum n h revoked := by
  induction n generalizing h revoked with
  | zero => simpa [activeScaleWeight, revokedScaleSum] using hfinal
  | succ n ih =>
    let tail := fun k => revoked (k+1)
    have hfinal' : 1 ≤ 2 ^ n * (2*h) := by simpa [pow_succ, mul_assoc] using hfinal
    have hw : activeScaleWeight (n+1) h revoked =
        activeScaleWeight n (2*h) tail + (if revoked 0 then 0 else h⁻¹) := by
      simp [activeScaleWeight, Finset.sum_range_succ', tail, pow_succ, mul_assoc, add_assoc]
    have hr : revokedScaleSum (n+1) h revoked =
        revokedScaleSum n (2*h) tail + (if revoked 0 then h else 0) := by
      simp [revokedScaleSum, Finset.sum_range_succ', tail, pow_succ, mul_assoc]
    rw [hw, hr]
    cases hzero : revoked 0 with
    | true =>
      have ht := ih (2*h) tail (by positivity) hfinal'
      simp only [if_true, add_zero]
      linarith
    | false =>
      simp only [Bool.false_eq_true, if_false, add_zero]
      have hwpos := activeScaleWeight_pos n (by positivity : 0 < 2*h) tail
      have hrecip : (activeScaleWeight n (2*h) tail + h⁻¹)⁻¹ ≤ h := by
        simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hh)
          (le_add_of_nonneg_left hwpos.le : h⁻¹ ≤ activeScaleWeight n (2*h) tail + h⁻¹)
      have hn : 0 ≤ revokedScaleSum n (2*h) tail :=
        Finset.sum_nonneg fun k _ => by split <;> positivity
      linarith

/-- The signed initial regularizer and the trace in one coordinate. -/
theorem initialCoordinateJointBound (J : ℕ) (h v β : ℝ) (hh : 0 < h) (hfinal : 1 ≤ 2^J*h)
    (x : ℕ → ℝ) (revoked : ℕ → Bool) (hβ₀ : 0 ≤ β) (hβ : β ≤ 25/64)
    (hend : ∀ k < J, |x k| ≤ 3*(2^k*h))
    (hit : ∀ k < J, revoked k = true → 2^k*h ≤ |x k|) :
    (∑ k ∈ Finset.range J, (2*x k*v-(x k)^2)/(2^k*h)) +
      β * (activeScaleWeight J h revoked)⁻¹ ≤
      β*h + 6*|v| * max 0 (Real.logb 2 (|v|/h)) + (6+2/(39/64 : ℝ))*|v| := by
  have htrace := mul_le_mul_of_nonneg_left (activeScaleWeight_inv_le J h revoked hh hfinal) hβ₀
  have hl := initialScales J h v β hh x revoked hβ hend hit
  rw [Finset.sum_add_distrib] at hl
  have hr : β * revokedScaleSum J h revoked =
      ∑ k ∈ Finset.range J, if revoked k then β*(2^k*h) else 0 := by
    rw [revokedScaleSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by split <;> simp_all
  rw [mul_add, hr] at htrace
  linarith

end Curvature

end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

def coefficientCost {N : ℕ} (ℓ h v : Vec N) : ℝ :=
  ∑ j, ℓ j * (h j + |v j| * (1 + Real.log (max 1 (|v j| / h j))))

private theorem logb_posPart_le {r : ℝ} (hr : 0 ≤ r) :
    max 0 (Real.logb 2 r) ≤ 2 * Real.log (max 1 r) := by
  by_cases h : r ≤ 1
  · rw [max_eq_left h, Real.log_one, mul_zero, max_eq_left]
    exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hr h) (Real.log_nonneg (by norm_num))
  · have h₁ := (lt_of_not_ge h).le
    rw [max_eq_right h₁, max_eq_right (Real.logb_nonneg (by norm_num) h₁), Real.logb]
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1:ℝ) < 2))).mpr
    nlinarith only [mul_nonneg (Real.log_nonneg h₁)
      (show 0 ≤ 2 * Real.log 2 - 1 by linarith only [Real.log_two_gt_d9])]

theorem initialCoordinateCost_le (J : ℕ) (h v ε β : ℝ) (hh : 0 < h)
    (hfinal : 1 ≤ 2^J*h) (hv : |v| ≤ 1) (hε : ε ≤ 1) (hβ₀ : 0 ≤ β)
    (hβ : β ≤ 25/64) (x : ℕ → ℝ) (revoked : ℕ → Bool)
    (hend : ∀ k < J, |x k| ≤ 3*(2^k*h))
    (hit : ∀ k < J, revoked k = true → 2^k*h ≤ |x k|) :
    v^2 + (∑ k ∈ Finset.range J, (2*x k*v-(x k)^2)/(2^k*h)) +
      β * (activeScaleWeight J h revoked)⁻¹ + ε/128*h ≤
      12 * (h + |v| * (1 + Real.log (max 1 (|v|/h)))) := by
  have hc := initialCoordinateJointBound J h v β hh hfinal x revoked hβ₀ hβ hend hit
  have hl := mul_le_mul_of_nonneg_left (logb_posPart_le (div_nonneg (abs_nonneg v) hh.le))
      (show 0 ≤ 6*|v| by positivity)
  have hv₂ := mul_le_mul_of_nonneg_left hv (abs_nonneg v)
  rw [mul_one, ← sq, sq_abs] at hv₂
  linarith only [hc, hl, hv₂, abs_nonneg v, hh, mul_le_mul_of_nonneg_right hβ hh.le,
    mul_le_mul_of_nonneg_right hε hh.le]

def survivingDiagonal {N : ℕ} (scale : ℝ) (ℓ h : Vec N) (J : Fin N → ℕ)
    (revoked : Fin N → ℕ → Bool) : Mat N :=
  Matrix.diagonal (fun j => scale * ℓ j * activeScaleWeight (J j) (h j) (revoked j))

theorem trace_survivingDiagonal_le {N : ℕ} (cov : Mat N) (scale : ℝ) (hscale : 0 < scale)
    (ℓ h : Vec N) (hℓ : ∀ j, 0 < ℓ j) (hh : ∀ j, 0 < h j)
    (J : Fin N → ℕ) (revoked : Fin N → ℕ → Bool) (hdiag : ∀ j, cov j j ≤ ℓ j ^ 2) :
    (cov * (survivingDiagonal scale ℓ h J revoked)⁻¹).trace ≤
      ∑ j, ℓ j / scale * (activeScaleWeight (J j) (h j) (revoked j))⁻¹ := by
  classical
  let b := fun j => scale * ℓ j * activeScaleWeight (J j) (h j) (revoked j)
  change (cov * (Matrix.diagonal b)⁻¹).trace ≤ _
  have hi : (Matrix.diagonal b)⁻¹ = Matrix.diagonal (fun j => (b j)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have hz : ∀ j, b j ≠ 0 := fun j => (mul_pos (mul_pos hscale (hℓ j))
      (activeScaleWeight_pos _ (hh j) _)).ne'
    simp [hz, Matrix.diagonal_one]
  rw [hi]
  apply Finset.sum_le_sum
  intro j _
  change (cov * Matrix.diagonal (fun j => (b j)⁻¹)) j j ≤ _
  rw [Matrix.mul_diagonal]
  have hb : 0 < b j := mul_pos (mul_pos hscale (hℓ j)) (activeScaleWeight_pos _ (hh j) _)
  calc
    _ ≤ ℓ j ^ 2 * (b j)⁻¹ := mul_le_mul_of_nonneg_right (hdiag j) (inv_nonneg.mpr hb.le)
    _ = _ := by dsimp [b]; field_simp [(hℓ j).ne']

end Curvature

end
end


