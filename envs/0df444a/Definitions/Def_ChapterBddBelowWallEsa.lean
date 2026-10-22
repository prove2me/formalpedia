-- Prove2me | Definitions.Def_ChapterBddBelowWallEsa
-- name    : ChapterBddBelowWallEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T11:23:48.427455+00:00
-- url     : https://prove2.me/theorems/36c3377a-f1ed-4519-a68d-613c64972589
-- title:
--   The Lean 4 theorem `continuous_bumpG_prime` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterBddBelowWallEsa.lean`): generated def bundle for ChapterBddBelowWallEsa. See BookProof/ChapterBddBelowWallEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowWallEsa.lean

import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterWeakSecondDerivative
import Mathlib


/-!
# `−d²/dx² + V` is essentially self-adjoint for every smooth potential **bounded below**

`BookProof/ChapterScalaronWallEsa.lean` proves essential self-adjointness of `−d²/dx² + V` on
the compactly supported smooth core of `L²(ℝ)` for every smooth `V ≥ 0`, by a convexity
argument: for `V ≥ 0` and `Re z = 0` the modulus square of a classical `L²` solution of
`W'' = (V − z)W` is convex, non-negative and integrable, hence zero.  The convexity breaks as
soon as `V` dips below `0`, and `BookProof/ChapterLimitCircleExample.lean` and
`BookProof/ChapterConformalFiberDeficiency.lean` show the conclusion itself is false for
potentials unbounded below.

This module closes the remaining gap between the two: **bounded below is enough.**  It is the
one-dimensional input of `CONSOLIDATED_PLAN.md`'s QG-2 **Case A** (a potential carried by a
positive-kinetic direction), and together with the Case B counterexamples it makes the sign
dichotomy sharp — for smooth real potentials on the line, boundedness below is what decides
essential self-adjointness on the compactly supported smooth core, and no growth condition
enters on either side.

## The argument (a cutoff energy estimate)

Let `W` be a classical `L²` solution of `W'' = (V − z)W` with `Re z = 0`, `Im z ≠ 0` and
`V ≥ −K`.  For a real `C¹` cutoff `ζ` of compact support, the function `ζ²·conj(W)·W'` has
compact support, so the integral of its derivative vanishes:

`∫ 2ζζ'·conj(W)W' + ∫ ζ²|W'|² + ∫ ζ²(V − z)|W|² = 0`.

* **Real part.**  `∫ ζ²|W'|² + ∫ ζ²V|W|² = −2∫ ζζ'·Re(conj(W)W')`, and the pointwise Young
  inequality `2|ζζ'||W||W'| ≤ ½ζ²|W'|² + 2ζ'²|W|²` turns this into a *uniform* bound
  `∫ ζ_r²|W'|² ≤ 4M²‖W‖² + 2K‖W‖²` for the scaled cutoffs `ζ_r(x) = g(x/r)` (`|ζ_r'| ≤ M/r`).
  This is where `V ≥ −K` is used, and it is the only place.
* **Imaginary part.**  `|Im z|·∫ ζ_r²|W|² = |2∫ ζ_rζ_r'·Im(conj(W)W')| ≤ (1/r)∫ζ_r²|W'|²
  + r∫ζ_r'²|W|² ≤ (C + M²‖W‖²)/r → 0`, while `∫ ζ_r²|W|² ≥ ∫_{[−r,r]}|W|² → ‖W‖²`.  Hence
  `W = 0`.

## What is proved

* `bumpG`, `zeta` — the scaled cutoff family, with `zeta_one`, `hasCompactSupport_zeta` and
  the derivative bound `abs_zeta'_le`;
* `ode_solution_eq_zero_of_bddBelow` — the ODE step: a square-integrable classical solution of
  `W'' = (V − z)W` with `V ≥ −K`, `Re z = 0` and `Im z ≠ 0` vanishes identically;
* `wallHam_deficiencyTrivialAt_of_bddBelow` — hence the deficiency space at such a `z` is
  trivial;
* **`wallHam_essentiallySelfAdjoint_of_bddBelow`** — `−d²/dx² + V` is essentially self-adjoint
  on the compactly supported smooth core for every smooth `V` bounded below;
* `wallHam_essentiallySelfAdjoint_of_bddBelow'` — the same with the hypothesis phrased as
  `BddBelow (Set.range V)`;
* `esa_iff_dichotomy_examples` is *not* claimed: the converse direction is false in general
  (boundedness below is sufficient, not necessary), and no such claim is made here.
-/

namespace BookProof.BddBelowWallEsa

open MeasureTheory Metric Filter Topology Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction BookProof.WeakSecondDeriv

noncomputable section

/-! ## 1. The scaled cutoff family -/

/-- A fixed smooth bump on the line: `1` on `[−1,1]`, supported in `[−2,2]`. -/
def bumpG : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩

/-- Its derivative. -/
def bumpG' : ℝ → ℝ := deriv (bumpG : ℝ → ℝ)

lemma hasDerivAt_bumpG (x : ℝ) : HasDerivAt (bumpG : ℝ → ℝ) (bumpG' x) x :=
  (((bumpG.contDiff (n := 1)).differentiable (by norm_num)) x).hasDerivAt

lemma continuous_bumpG' : Continuous bumpG' :=
  (bumpG.contDiff (n := 2)).continuous_deriv (by norm_num)

lemma hasCompactSupport_bumpG' : HasCompactSupport bumpG' := bumpG.hasCompactSupport.deriv

lemma bumpG_one {x : ℝ} (hx : |x| ≤ 1) : (bumpG : ℝ → ℝ) x = 1 := by
  refine bumpG.one_of_mem_closedBall ?_
  simpa [Real.dist_eq, bumpG] using hx

lemma bumpG_zero {x : ℝ} (hx : 2 ≤ |x|) : (bumpG : ℝ → ℝ) x = 0 := by
  refine bumpG.zero_of_le_dist ?_
  simpa [Real.dist_eq, bumpG] using hx

/-- A uniform bound for the derivative of the fixed bump. -/
def bumpM : ℝ := (hasCompactSupport_bumpG'.exists_bound_of_continuous continuous_bumpG').choose

lemma abs_bumpG'_le (x : ℝ) : |bumpG' x| ≤ bumpM := by
  have h := (hasCompactSupport_bumpG'.exists_bound_of_continuous continuous_bumpG').choose_spec x
  simpa [Real.norm_eq_abs, bumpM] using h

lemma bumpM_nonneg : 0 ≤ bumpM := le_trans (abs_nonneg _) (abs_bumpG'_le 0)

/-- The cutoff at scale `r`: `1` on `[−r, r]`, supported in `[−2r, 2r]`. -/
def zeta (r : ℝ) : ℝ → ℝ := fun x => (bumpG : ℝ → ℝ) (x / r)

/-- Its derivative. -/
def zeta' (r : ℝ) : ℝ → ℝ := fun x => bumpG' (x / r) / r

lemma hasDerivAt_zeta (r : ℝ) (x : ℝ) :
    @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      ((NormedAlgebra.toNormedSpace ℝ).toModule)
      _ _ (zeta r) (zeta' r x) x := by
  have h := (hasDerivAt_bumpG (x / r)).comp x ((hasDerivAt_id x).div_const r)
  convert h using 1
  · funext y; simp [zeta, Function.comp_apply, id_eq]
  · simp [zeta', div_eq_mul_inv]

lemma continuous_zeta (r : ℝ) : Continuous (zeta r) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_zeta r x).continuousAt

lemma continuous_zeta' (r : ℝ) : Continuous (zeta' r) :=
  (continuous_bumpG'.comp (continuous_id.div_const r)).div_const r

lemma zeta_nonneg (r : ℝ) (x : ℝ) : 0 ≤ zeta r x := bumpG.nonneg

lemma zeta_le_one (r : ℝ) (x : ℝ) : zeta r x ≤ 1 := bumpG.le_one

lemma zeta_one {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : |x| ≤ r) : zeta r x = 1 := by
  refine bumpG_one ?_
  rw [abs_div, abs_of_pos hr, div_le_one hr]
  exact hx

lemma hasCompactSupport_zeta {r : ℝ} (hr : 0 < r) : HasCompactSupport (zeta r) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(2 * r)) (b := 2 * r))
  intro x hx
  refine bumpG_zero ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rw [abs_div, abs_of_pos hr, le_div_iff₀ hr]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma hasCompactSupport_zeta' {r : ℝ} (hr : 0 < r) : HasCompactSupport (zeta' r) := by
  have h : zeta' r = deriv (zeta r) := funext fun x => (hasDerivAt_zeta r x).deriv.symm
  rw [h]
  exact (hasCompactSupport_zeta hr).deriv

lemma hasCompactSupport_zeta_sq {r : ℝ} (hr : 0 < r) :
    @HasCompactSupport ℝ ℝ _ instMulZeroClassOfSemiring.toZero
      (fun x => (zeta r x) ^ 2) := by
  have h := (hasCompactSupport_zeta hr).mul_right (f' := zeta r)
  convert h using 1
  funext y; simp [pow_two]

lemma hasCompactSupport_zeta'_sq {r : ℝ} (hr : 0 < r) :
    @HasCompactSupport ℝ ℝ _ instMulZeroClassOfSemiring.toZero
      (fun x => (zeta' r x) ^ 2) := by
  have h := (hasCompactSupport_zeta' hr).mul_right (f' := zeta' r)
  convert h using 1
  funext y; simp [pow_two]

lemma abs_zeta'_le {r : ℝ} (hr : 0 < r) (x : ℝ) : |zeta' r x| ≤ bumpM / r := by
  rw [zeta', abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (abs_bumpG'_le _) hr.le

/-! ## 2. The weighted integration-by-parts identities -/

section Ode

variable {V : ℝ → ℝ} {z : ℂ} {W W' : ℝ → ℂ}

/-- The derivative of the Wronskian-type product `conj(W)·W'`. -/
lemma hasDerivAt_wronsk (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW2 : ∀ x, HasDerivAt W' ((((V x : ℝ) : ℂ) - z) * W x) x) (x : ℝ) :
    HasDerivAt (fun y => (starRingEnd ℂ) (W y) * W' y)
      ((starRingEnd ℂ) (W' x) * W' x
        + (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)) x :=
  ((hW x).star).mul (hW2 x)

lemma wronsk_deriv_re (x : ℝ) :
    ((starRingEnd ℂ) (W' x) * W' x
        + (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)).re
      = ‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2 := by
  have h1 : (starRingEnd ℂ) (W' x) * W' x = ((‖W' x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  have h2 : (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)
      = ((((V x : ℝ) : ℂ) - z)) * ((‖W x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (W x)) ((((V x : ℝ) : ℂ) - z)), mul_assoc,
      Complex.conj_mul']
    push_cast; ring
  rw [h1, h2]
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma wronsk_deriv_im (x : ℝ) :
    ((starRingEnd ℂ) (W' x) * W' x
        + (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)).im
      = -z.im * ‖W x‖ ^ 2 := by
  have h1 : (starRingEnd ℂ) (W' x) * W' x = ((‖W' x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  have h2 : (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)
      = ((((V x : ℝ) : ℂ) - z)) * ((‖W x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (W x)) ((((V x : ℝ) : ℂ) - z)), mul_assoc,
      Complex.conj_mul']
    push_cast; ring
  rw [h1, h2]
  simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The real part of the weighted identity, before integration. -/
lemma hasDerivAt_reWeighted (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW2 : ∀ x, HasDerivAt W' ((((V x : ℝ) : ℂ) - z) * W x) x) (r : ℝ) (x : ℝ) :
    @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      ((NormedAlgebra.toNormedSpace ℝ).toModule) _ _
      (fun y => (zeta r y) ^ 2 * ((starRingEnd ℂ) (W y) * W' y).re)
      (2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re
        + (zeta r x) ^ 2 * (‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2)) x := by
  have hz2 : @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      ((NormedAlgebra.toNormedSpace ℝ).toModule)
      _ _ (fun y => (zeta r y) ^ 2) (2 * zeta r x * zeta' r x) x := by
    have h := (hasDerivAt_zeta r x).pow 2
    convert h using 1
    · funext y; rfl
    · simp [mul_comm, mul_assoc, mul_left_comm]
  have hP : HasDerivAt (fun y => ((starRingEnd ℂ) (W y) * W' y).re)
      (‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2) x := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_wronsk hW hW2 x)
    simp only [Function.comp_def, Complex.reCLM_apply] at h
    rwa [wronsk_deriv_re (V := V) (z := z) (W := W) (W' := W') x] at h
  have hmul := hz2.mul hP
  convert hmul using 1
  · funext y; simp

/-- The imaginary part of the weighted identity, before integration. -/
lemma hasDerivAt_imWeighted (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW2 : ∀ x, HasDerivAt W' ((((V x : ℝ) : ℂ) - z) * W x) x) (r : ℝ) (x : ℝ) :
    @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      ((NormedAlgebra.toNormedSpace ℝ).toModule) _ _
      (fun y => (zeta r y) ^ 2 * ((starRingEnd ℂ) (W y) * W' y).im)
      (2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im
        + (zeta r x) ^ 2 * (-z.im * ‖W x‖ ^ 2)) x := by
  have hz2 : @HasDerivAt ℝ _ ℝ
      DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup
      ((NormedAlgebra.toNormedSpace ℝ).toModule)
      _ _ (fun y => (zeta r y) ^ 2) (2 * zeta r x * zeta' r x) x := by
    have h := (hasDerivAt_zeta r x).pow 2
    convert h using 1
    · funext y; rfl
    · simp [mul_comm, mul_assoc, mul_left_comm]
  have hP : HasDerivAt (fun y => ((starRingEnd ℂ) (W y) * W' y).im)
      (-z.im * ‖W x‖ ^ 2) x := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_wronsk hW hW2 x)
    simp only [Function.comp_def, Complex.imCLM_apply] at h
    rwa [wronsk_deriv_im (V := V) (z := z) (W := W) (W' := W') x] at h
  have hmul := hz2.mul hP
  convert hmul using 1
  · funext y; simp

end Ode

/-! ## 3. The ODE step for potentials bounded below -/

set_option maxHeartbeats 1600000 in
-- The cutoff energy estimate is a single long chain of integral inequalities over the same
-- five integrands; elaborating them in one proof exceeds the default heartbeat budget.
/-- **A square-integrable classical solution of `W'' = (V − z)W` with `V` bounded below,
`Re z = 0` and `Im z ≠ 0` vanishes identically.**  This is the sharp form of
`BookProof.ScalaronWallEsa.ode_solution_eq_zero`, which assumes `V ≥ 0`: the proof there is a
convexity argument that needs the sign, the proof here is the cutoff energy estimate, which
needs only a lower bound. -/
theorem ode_solution_eq_zero_of_bddBelow {V : ℝ → ℝ} (hVc : Continuous V) {K : ℝ}
    (hVK : ∀ x, -K ≤ V x) {z : ℂ} (hzre : z.re = 0) (hzim : z.im ≠ 0)
    {W W' : ℝ → ℂ} (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW2 : ∀ x, HasDerivAt W' ((((V x : ℝ) : ℂ) - z) * W x) x)
    (hint : Integrable (fun x => ‖W x‖ ^ 2) volume) :
    ∀ x, W x = 0 := by
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun x => (hW x).continuousAt
  have hW'c : Continuous W' := continuous_iff_continuousAt.2 fun x => (hW2 x).continuousAt
  have hPc : Continuous fun x => ((starRingEnd ℂ) (W x) * W' x).re :=
    Complex.continuous_re.comp ((Complex.continuous_conj.comp hWc).mul hW'c)
  have hQc : Continuous fun x => ((starRingEnd ℂ) (W x) * W' x).im :=
    Complex.continuous_im.comp ((Complex.continuous_conj.comp hWc).mul hW'c)
  have hPle : ∀ x, |((starRingEnd ℂ) (W x) * W' x).re| ≤ ‖W x‖ * ‖W' x‖ := by
    intro x
    calc |((starRingEnd ℂ) (W x) * W' x).re| ≤ ‖(starRingEnd ℂ) (W x) * W' x‖ :=
          Complex.abs_re_le_norm _
      _ = ‖W x‖ * ‖W' x‖ := by rw [norm_mul, RCLike.norm_conj]
  have hQle : ∀ x, |((starRingEnd ℂ) (W x) * W' x).im| ≤ ‖W x‖ * ‖W' x‖ := by
    intro x
    calc |((starRingEnd ℂ) (W x) * W' x).im| ≤ ‖(starRingEnd ℂ) (W x) * W' x‖ :=
          Complex.abs_im_le_norm _
      _ = ‖W x‖ * ‖W' x‖ := by rw [norm_mul, RCLike.norm_conj]
  set N : ℝ := ∫ x, ‖W x‖ ^ 2 with hN
  have hNnn : 0 ≤ N := integral_nonneg fun x => by positivity
  set K0 : ℝ := max K 0 with hK0def
  have hK0 : 0 ≤ K0 := le_max_right _ _
  have hVK0 : ∀ x, -K0 ≤ V x := fun x => le_trans (neg_le_neg (le_max_left K 0)) (hVK x)
  set C : ℝ := 4 * bumpM ^ 2 * N + 2 * K0 * N with hC
  -- the uniform smallness of the cutoff `L²` mass
  have key : ∀ r : ℝ, 1 ≤ r →
      |z.im| * (∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2) ≤ (C + bumpM ^ 2 * N) / r := by
    intro r hr1
    have hr : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
    have hsuppZ2 := hasCompactSupport_zeta_sq hr
    have hsuppZ'2 := hasCompactSupport_zeta'_sq hr
    have hsuppZ := hasCompactSupport_zeta hr
    -- integrability of the basic integrands
    have iA : Integrable (fun x => (zeta r x) ^ 2 * ‖W' x‖ ^ 2) volume :=
      Continuous.integrable_of_hasCompactSupport
        (((continuous_zeta r).pow 2).mul (hW'c.norm.pow 2)) hsuppZ2.mul_right
    have iB : Integrable (fun x => (zeta r x) ^ 2 * ‖W x‖ ^ 2) volume :=
      Continuous.integrable_of_hasCompactSupport
        (((continuous_zeta r).pow 2).mul (hWc.norm.pow 2)) hsuppZ2.mul_right
    have iV : Integrable (fun x => (zeta r x) ^ 2 * (V x * ‖W x‖ ^ 2)) volume :=
      Continuous.integrable_of_hasCompactSupport
        (((continuous_zeta r).pow 2).mul (hVc.mul (hWc.norm.pow 2))) hsuppZ2.mul_right
    have iE : Integrable (fun x => (zeta' r x) ^ 2 * ‖W x‖ ^ 2) volume :=
      Continuous.integrable_of_hasCompactSupport
        (((continuous_zeta' r).pow 2).mul (hWc.norm.pow 2)) hsuppZ'2.mul_right
    have iJr : Integrable
        (fun x => 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re) volume :=
      Continuous.integrable_of_hasCompactSupport
        (((continuous_const.mul (continuous_zeta r)).mul (continuous_zeta' r)).mul hPc)
        ((hsuppZ.mul_left (f := fun _ => (2 : ℝ))).mul_right).mul_right
    have iJi : Integrable
        (fun x => 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im) volume :=
      Continuous.integrable_of_hasCompactSupport
        (((continuous_const.mul (continuous_zeta r)).mul (continuous_zeta' r)).mul hQc)
        ((hsuppZ.mul_left (f := fun _ => (2 : ℝ))).mul_right).mul_right
    have iFr : Integrable
        (fun x => (zeta r x) ^ 2 * ((starRingEnd ℂ) (W x) * W' x).re) volume :=
      Continuous.integrable_of_hasCompactSupport
        (((continuous_zeta r).pow 2).mul hPc) hsuppZ2.mul_right
    have iFi : Integrable
        (fun x => (zeta r x) ^ 2 * ((starRingEnd ℂ) (W x) * W' x).im) volume :=
      Continuous.integrable_of_hasCompactSupport
        (((continuous_zeta r).pow 2).mul hQc) hsuppZ2.mul_right
    have iAV : Integrable
        (fun x => (zeta r x) ^ 2 * ‖W' x‖ ^ 2 + (zeta r x) ^ 2 * (V x * ‖W x‖ ^ 2)) volume :=
      iA.add iV
    have iAV' : Integrable
        (fun x => (zeta r x) ^ 2 * (‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2)) volume := by
      refine iAV.congr (Filter.Eventually.of_forall fun x => ?_)
      rw [hzre]; ring
    have iBim : Integrable (fun x => (-z.im) * ((zeta r x) ^ 2 * ‖W x‖ ^ 2)) volume :=
      iB.const_mul _
    have iBim' : Integrable
        (fun x => (zeta r x) ^ 2 * (-z.im * ‖W x‖ ^ 2)) volume := by
      refine iBim.congr (Filter.Eventually.of_forall fun x => ?_)
      ring
    -- the two weighted identities
    have hidR : (∫ x, 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re)
        + ((∫ x, (zeta r x) ^ 2 * ‖W' x‖ ^ 2)
          + ∫ x, (zeta r x) ^ 2 * (V x * ‖W x‖ ^ 2)) = 0 := by
      have h0 : ∫ x, (2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re
          + (zeta r x) ^ 2 * (‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2)) = 0 :=
        MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
          (fun x => hasDerivAt_reWeighted hW hW2 r x) (iJr.add iAV') iFr
      have hpt : (fun x => 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re
            + (zeta r x) ^ 2 * (‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2))
          = fun x => 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re
            + ((zeta r x) ^ 2 * ‖W' x‖ ^ 2 + (zeta r x) ^ 2 * (V x * ‖W x‖ ^ 2)) := by
        funext x; rw [hzre]; ring
      rw [hpt, integral_add iJr iAV, integral_add iA iV] at h0
      exact h0
    have hidI : (∫ x, 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im)
        + (-z.im) * (∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2) = 0 := by
      have h0 : ∫ x, (2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im
          + (zeta r x) ^ 2 * (-z.im * ‖W x‖ ^ 2)) = 0 :=
        MeasureTheory.integral_eq_zero_of_hasDerivAt_of_integrable
          (fun x => hasDerivAt_imWeighted hW hW2 r x) (iJi.add iBim') iFi
      have hpt : (fun x => 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im
            + (zeta r x) ^ 2 * (-z.im * ‖W x‖ ^ 2))
          = fun x => 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im
            + (-z.im) * ((zeta r x) ^ 2 * ‖W x‖ ^ 2) := by
        funext x; ring
      rw [hpt, integral_add iJi iBim, integral_const_mul] at h0
      exact h0
    -- the cutoff derivative energy is small
    have hEle : (∫ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2) ≤ bumpM ^ 2 / r ^ 2 * N := by
      have hpt : ∀ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2 ≤ bumpM ^ 2 / r ^ 2 * ‖W x‖ ^ 2 := by
        intro x
        have h2 : (zeta' r x) ^ 2 ≤ bumpM ^ 2 / r ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg (zeta' r x)) (abs_zeta'_le hr x) 2
          rw [sq_abs] at this
          calc (zeta' r x) ^ 2 ≤ (bumpM / r) ^ 2 := this
            _ = bumpM ^ 2 / r ^ 2 := by rw [div_pow]
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
      calc (∫ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2)
          ≤ ∫ x, bumpM ^ 2 / r ^ 2 * ‖W x‖ ^ 2 := integral_mono iE (hint.const_mul _) hpt
        _ = bumpM ^ 2 / r ^ 2 * N := by rw [integral_const_mul]
    have hEle1 : (∫ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2) ≤ bumpM ^ 2 * N := by
      refine hEle.trans ?_
      have h1 : bumpM ^ 2 / r ^ 2 ≤ bumpM ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sq_nonneg bumpM) (by nlinarith : (0:ℝ) ≤ r ^ 2 - 1)]
      exact mul_le_mul_of_nonneg_right h1 hNnn
    have hEnn : 0 ≤ ∫ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2 :=
      integral_nonneg fun x => by positivity
    -- the potential term is bounded below
    have hVint : -(K0 * N) ≤ ∫ x, (zeta r x) ^ 2 * (V x * ‖W x‖ ^ 2) := by
      have hpt : ∀ x, -K0 * ‖W x‖ ^ 2 ≤ (zeta r x) ^ 2 * (V x * ‖W x‖ ^ 2) := by
        intro x
        have h0 : (0 : ℝ) ≤ (zeta r x) ^ 2 := sq_nonneg _
        have h1 : (zeta r x) ^ 2 ≤ 1 := by
          nlinarith [zeta_nonneg r x, zeta_le_one r x]
        have h2 : -K0 ≤ (zeta r x) ^ 2 * V x := by
          nlinarith [mul_nonneg h0 (by linarith [hVK0 x] : (0:ℝ) ≤ V x + K0)]
        have h3 : (0 : ℝ) ≤ ‖W x‖ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h2 h3]
      calc -(K0 * N) = ∫ x, -K0 * ‖W x‖ ^ 2 := by rw [integral_const_mul]; ring
        _ ≤ _ := integral_mono (hint.const_mul _) iV hpt
    -- Young's inequality for the cross term, real part
    have hYr : ∀ x, |2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re|
        ≤ 1 / 2 * ((zeta r x) ^ 2 * ‖W' x‖ ^ 2) + 2 * ((zeta' r x) ^ 2 * ‖W x‖ ^ 2) := by
      intro x
      have habs : |2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re|
          = 2 * |zeta r x| * |zeta' r x| * |((starRingEnd ℂ) (W x) * W' x).re| := by
        rw [abs_mul, abs_mul, abs_mul, abs_two]
      rw [habs]
      have hstep : 2 * |zeta r x| * |zeta' r x| * |((starRingEnd ℂ) (W x) * W' x).re|
          ≤ 2 * |zeta r x| * |zeta' r x| * (‖W x‖ * ‖W' x‖) :=
        mul_le_mul_of_nonneg_left (hPle x) (by positivity)
      refine hstep.trans ?_
      have := sq_nonneg (|zeta r x| * ‖W' x‖ - 2 * (|zeta' r x| * ‖W x‖))
      nlinarith [sq_abs (zeta r x), sq_abs (zeta' r x), abs_nonneg (zeta r x),
        abs_nonneg (zeta' r x), norm_nonneg (W x), norm_nonneg (W' x)]
    -- Young's inequality for the cross term, imaginary part, with weight `1/r`
    have hYi : ∀ x, |2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im|
        ≤ 1 / r * ((zeta r x) ^ 2 * ‖W' x‖ ^ 2) + r * ((zeta' r x) ^ 2 * ‖W x‖ ^ 2) := by
      intro x
      have habs : |2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im|
          = 2 * |zeta r x| * |zeta' r x| * |((starRingEnd ℂ) (W x) * W' x).im| := by
        rw [abs_mul, abs_mul, abs_mul, abs_two]
      rw [habs]
      have hstep : 2 * |zeta r x| * |zeta' r x| * |((starRingEnd ℂ) (W x) * W' x).im|
          ≤ 2 * |zeta r x| * |zeta' r x| * (‖W x‖ * ‖W' x‖) :=
        mul_le_mul_of_nonneg_left (hQle x) (by positivity)
      refine hstep.trans ?_
      set a : ℝ := |zeta r x| * ‖W' x‖ with ha
      set b : ℝ := |zeta' r x| * ‖W x‖ with hb
      have hz2 : (zeta r x) ^ 2 * ‖W' x‖ ^ 2 = a ^ 2 := by
        rw [ha, mul_pow, sq_abs]
      have hz'2 : (zeta' r x) ^ 2 * ‖W x‖ ^ 2 = b ^ 2 := by
        rw [hb, mul_pow, sq_abs]
      have hcomm : 2 * |zeta r x| * |zeta' r x| * (‖W x‖ * ‖W' x‖) = 2 * (a * b) := by
        rw [ha, hb]; ring
      rw [hz2, hz'2, hcomm]
      have hexp : 1 / r * a ^ 2 + r * b ^ 2 - 2 * (a * b) = (a - r * b) ^ 2 / r := by
        field_simp; ring
      have hnn : (0 : ℝ) ≤ (a - r * b) ^ 2 / r := by positivity
      linarith
    -- the cutoff kinetic energy is uniformly bounded
    have hAle : (∫ x, (zeta r x) ^ 2 * ‖W' x‖ ^ 2) ≤ C := by
      have hJr : |∫ x, 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re|
          ≤ 1 / 2 * (∫ x, (zeta r x) ^ 2 * ‖W' x‖ ^ 2)
            + 2 * ∫ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2 := by
        refine (abs_integral_le_integral_abs).trans ?_
        have hb : Integrable (fun x => 1 / 2 * ((zeta r x) ^ 2 * ‖W' x‖ ^ 2)
            + 2 * ((zeta' r x) ^ 2 * ‖W x‖ ^ 2)) volume := (iA.const_mul _).add (iE.const_mul _)
        calc (∫ x, |2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re|)
            ≤ ∫ x, (1 / 2 * ((zeta r x) ^ 2 * ‖W' x‖ ^ 2)
              + 2 * ((zeta' r x) ^ 2 * ‖W x‖ ^ 2)) := integral_mono iJr.abs hb hYr
          _ = _ := by
              rw [integral_add (iA.const_mul _) (iE.const_mul _), integral_const_mul,
                integral_const_mul]
      have h1 := abs_le.1 hJr
      have := h1.1
      rw [hC]
      nlinarith [hEle1, hVint, hNnn, hEnn]
    -- and hence the cutoff `L²` mass is `O(1/r)`
    have hJi : |∫ x, 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im|
        ≤ 1 / r * (∫ x, (zeta r x) ^ 2 * ‖W' x‖ ^ 2)
          + r * ∫ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2 := by
      refine (abs_integral_le_integral_abs).trans ?_
      have hb : Integrable (fun x => 1 / r * ((zeta r x) ^ 2 * ‖W' x‖ ^ 2)
          + r * ((zeta' r x) ^ 2 * ‖W x‖ ^ 2)) volume := (iA.const_mul _).add (iE.const_mul _)
      calc (∫ x, |2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im|)
          ≤ ∫ x, (1 / r * ((zeta r x) ^ 2 * ‖W' x‖ ^ 2)
            + r * ((zeta' r x) ^ 2 * ‖W x‖ ^ 2)) := integral_mono iJi.abs hb hYi
        _ = _ := by
            rw [integral_add (iA.const_mul _) (iE.const_mul _), integral_const_mul,
              integral_const_mul]
    have hBnn : 0 ≤ ∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2 := integral_nonneg fun x => by positivity
    have hAnn : 0 ≤ ∫ x, (zeta r x) ^ 2 * ‖W' x‖ ^ 2 := integral_nonneg fun x => by positivity
    have habsB : |z.im| * (∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2)
        = |∫ x, 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im| := by
      have : (∫ x, 2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im)
          = z.im * (∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2) := by linarith [hidI]
      rw [this, abs_mul, abs_of_nonneg hBnn]
    rw [habsB]
    refine hJi.trans ?_
    have hrE : r * (∫ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2) ≤ bumpM ^ 2 * N / r := by
      have := mul_le_mul_of_nonneg_left hEle (le_of_lt hr)
      calc r * (∫ x, (zeta' r x) ^ 2 * ‖W x‖ ^ 2) ≤ r * (bumpM ^ 2 / r ^ 2 * N) := this
        _ = bumpM ^ 2 * N / r := by field_simp
    have hrA : 1 / r * (∫ x, (zeta r x) ^ 2 * ‖W' x‖ ^ 2) ≤ C / r := by
      rw [one_div, inv_mul_eq_div, div_le_div_iff_of_pos_right hr]
      exact hAle
    have : C / r + bumpM ^ 2 * N / r = (C + bumpM ^ 2 * N) / r := by ring
    linarith
  -- pass to the limit
  have hNzero : N = 0 := by
    have hsets : ∀ n : ℕ, MeasurableSet (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
      fun _ => measurableSet_Icc
    have hmono : Monotone fun n : ℕ => Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
      intro m n hmn
      have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact Icc_subset_Icc (by linarith) (by linarith)
    have hunion : (⋃ n : ℕ, Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) = univ := by
      ext x
      simp only [mem_iUnion, mem_Icc, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have hlim : Tendsto (fun n : ℕ => ∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ‖W x‖ ^ 2)
        atTop (𝓝 N) := by
      have h := tendsto_setIntegral_of_monotone (f := fun x => ‖W x‖ ^ 2)
        (μ := (volume : Measure ℝ)) hsets hmono (by rw [hunion]; exact hint.integrableOn)
      rwa [hunion, setIntegral_univ] at h
    have himpos : (0 : ℝ) < |z.im| := abs_pos.2 hzim
    have hbound : ∀ n : ℕ, (∫ x in Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ‖W x‖ ^ 2)
        ≤ (C + bumpM ^ 2 * N) / (|z.im| * ((n : ℝ) + 1)) := by
      intro n
      have hcast : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      set r : ℝ := (n : ℝ) + 1 with hrdef
      have hr1 : (1 : ℝ) ≤ r := by rw [hrdef]; linarith
      have hr : (0 : ℝ) < r := by linarith
      have iB : Integrable (fun x => (zeta r x) ^ 2 * ‖W x‖ ^ 2) volume :=
        Continuous.integrable_of_hasCompactSupport
          (((continuous_zeta r).pow 2).mul (hWc.norm.pow 2))
          (hasCompactSupport_zeta_sq hr).mul_right
      have hset : (∫ x in Icc (-r) r, ‖W x‖ ^ 2) ≤ ∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2 := by
        have heq : (∫ x in Icc (-r) r, ‖W x‖ ^ 2)
            = ∫ x in Icc (-r) r, (zeta r x) ^ 2 * ‖W x‖ ^ 2 := by
          refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
          rw [zeta_one hr (abs_le.2 ⟨hx.1, hx.2⟩)]
          ring
        rw [heq]
        exact setIntegral_le_integral iB (Filter.Eventually.of_forall fun x => by positivity)
      have hk := key r hr1
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < |z.im| * r)]
      have h1 : (∫ x in Icc (-r) r, ‖W x‖ ^ 2) * (|z.im| * r)
          ≤ (∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2) * (|z.im| * r) :=
        mul_le_mul_of_nonneg_right hset (by positivity)
      have h2 : (∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2) * (|z.im| * r) ≤ C + bumpM ^ 2 * N := by
        have h3 := mul_le_mul_of_nonneg_right hk hr.le
        rw [div_mul_cancel₀ _ (ne_of_gt hr)] at h3
        calc (∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2) * (|z.im| * r)
            = (|z.im| * (∫ x, (zeta r x) ^ 2 * ‖W x‖ ^ 2)) * r := by ring
          _ ≤ C + bumpM ^ 2 * N := h3
      linarith
    have hlim2 : Tendsto (fun n : ℕ => (C + bumpM ^ 2 * N) / (|z.im| * ((n : ℝ) + 1)))
        atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds
        (Filter.Tendsto.const_mul_atTop himpos
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
    have hle : N ≤ 0 := le_of_tendsto_of_tendsto' hlim hlim2 hbound
    linarith
  -- a continuous non-negative function with vanishing integral is zero
  have hae : (fun x => ‖W x‖ ^ 2) =ᵐ[(volume : Measure ℝ)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hint).1 hNzero
  have heq : (fun x => ‖W x‖ ^ 2) = (0 : ℝ → ℝ) :=
    (Continuous.ae_eq_iff_eq volume (hWc.norm.pow 2) continuous_const).1 hae
  intro x
  have hx2 : ‖W x‖ ^ 2 = 0 := congrFun heq x
  have hx0 : ‖W x‖ = 0 := by nlinarith [norm_nonneg (W x)]
  exact norm_eq_zero.1 hx0

/-! ## 4. Essential self-adjointness -/

/-- **Trivial deficiency spaces at every purely imaginary `z ≠ 0`, for a smooth potential
bounded below.** -/
theorem wallHam_deficiencyTrivialAt_of_bddBelow (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {K : ℝ} (hVK : ∀ x, -K ≤ V x)
    {z : ℂ} (hzre : z.re = 0) (hzim : z.im ≠ 0) :
    DeficiencyTrivialAt (ccDomain ℝ) (wallHam V hV) z := by
  intro u hu
  have hloc : LocallyIntegrable (fun x => (u x : ℂ)) (volume : Measure ℝ) :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have hc : Continuous fun x : ℝ => ((V x : ℝ) : ℂ) - z :=
    (Complex.continuous_ofReal.comp hV.continuous).sub continuous_const
  obtain ⟨W, W', hW, hW', hWae⟩ :=
    exists_deriv2_of_weak_eq hloc hc (fun g hg => wallHam_weak_eq V hV z u hu hg)
  have hintu : Integrable (fun x => ‖u x‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have hintW : Integrable (fun x => ‖W x‖ ^ 2) (volume : Measure ℝ) := by
    refine hintu.congr ?_
    filter_upwards [hWae] with x hx
    rw [hx]
  have hzero := ode_solution_eq_zero_of_bddBelow hV.continuous hVK hzre hzim hW hW' hintW
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [hWae] with x hx
  simp [hx, hzero x]

/-- **`−d²/dx² + V` is essentially self-adjoint on the compactly supported smooth core of
`L²(ℝ)` for every smooth potential `V` bounded below.**  No growth hypothesis and no sign
hypothesis enter: only a finite lower bound `V ≥ −K`. -/
theorem wallHam_essentiallySelfAdjoint_of_bddBelow (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) {K : ℝ} (hVK : ∀ x, -K ≤ V x) :
    EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) :=
  ⟨wallHam_deficiencyTrivialAt_of_bddBelow V hV hVK (by simp) (by simp),
    wallHam_deficiencyTrivialAt_of_bddBelow V hV hVK (by simp) (by simp)⟩



/-- The non-negative case of `BookProof.ScalaronWallEsa.wallHam_essentiallySelfAdjoint` is a
special case: take `K = 0`. -/
theorem wallHam_essentiallySelfAdjoint_of_nonneg (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hVnn : ∀ x, 0 ≤ V x) :
    EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) :=
  wallHam_essentiallySelfAdjoint_of_bddBelow V hV (K := 0) (fun x => by simpa using hVnn x)

end

end BookProof.BddBelowWallEsa


