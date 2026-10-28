-- Prove2me | Definitions.Def_ChapterNonnegSemigroupGenerator
-- name    : ChapterNonnegSemigroupGenerator
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T15:17:25.556343+00:00
-- url     : https://prove2.me/theorems/3859d5b8-d14a-4bb9-b304-d3ceb3de4406
-- title:
--   Chapter NonnegSemigroupGenerator
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNonnegSemigroupGenerator.lean`): generated def bundle for ChapterNonnegSemigroupGenerator. See BookProof/ChapterNonnegSemigroupGenerator.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNonnegSemigroupGenerator.lean

import Definitions.Def_ChapterNonnegSemigroup
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegSquareRoot
import Definitions.Def_ChapterNonnegUnitaryGroup
import Definitions.Def_ChapterPositiveSquareRootUnique
import Theorems.Thm_BookProof_NonnegSemigroup_isSelfAdjoint_expNeg
import Theorems.Thm_BookProof_NonnegSemigroup_expNeg_add
import Theorems.Thm_BookProof_NonnegSemigroup_norm_expNeg_sub_self_le
import Theorems.Thm_BookProof_NonnegSemigroup_isSelfAdjoint_semigroupS
import Theorems.Thm_BookProof_NonnegSemigroup_semigroupS_add
import Theorems.Thm_BookProof_NonnegSemigroup_norm_semigroupS_apply_le
import Theorems.Thm_BookProof_NonnegSemigroup_tendsto_semigroupS_zero
import Mathlib


/-!
# The generator of the contraction semigroup `e^{-tT}`

`BookProof.ChapterNonnegSemigroup` built, for a non-negative self-adjoint linear relation
`T` on a complex Hilbert space `F`, the contraction semigroup `e^{-tT}`
(`BookProof.NonnegSemigroup.semigroupS`) as the Yosida limit of the bounded semigroups
`e^{-tT_a}`, together with the semigroup law, self-adjointness, the contraction bound and
strong continuity at `0`.  This chapter supplies the three items that chapter left open:

* **Positivity.**  `e^{-tA} = (e^{-tA/2})²` is a positive operator for every self-adjoint
  `A` (`expNeg_nonneg`), and positivity passes to the limit: `0 ≤ e^{-tT}`
  (`semigroupS_nonneg`).
* **Strong continuity in `t`, not merely at `0`.**  The semigroup law turns the estimate at
  the origin into a *uniform* modulus of continuity along the whole orbit:
  `‖e^{-tT}x − e^{-sT}x‖ ≤ ‖e^{-(t-s)T}x − x‖` (`norm_semigroupS_sub_semigroupS_le`), hence
  `semigroupS_uniformly_continuous`.
* **The generator.**  `e^{-tT}` commutes with the resolvent (`semigroupS_invCLMAt_comm`),
  hence leaves the domain of `T` invariant and commutes with `T` on it:
  `(h, k) ∈ T → (e^{-tT}h, e^{-tT}k) ∈ T` (`semigroupS_mem_of_mem`).  The quantitative
  estimate `‖e^{-tT}h − h + t·k‖ ≤ t (2ε + t‖k''‖)` (`norm_semigroupS_sub_add_smul_le`),
  obtained from the bounded estimate `norm_expNeg_sub_add_smul_le` by the mean-value
  inequality along the approximations, gives the **differential equation** in difference
  quotient form: `t⁻¹ (e^{-tT}h − h) → −k` as `t ↓ 0`
  (`tendsto_semigroupS_difference_quotient`) and, at a general time,
  `u⁻¹ (e^{-(t+u)T}h − e^{-tT}h) → −e^{-tT}k` (`tendsto_semigroupS_difference_quotient_at`):
  `T` is the generator of its own semigroup.
* **Decay from a spectral lower bound.**  If `Re⟪h, k⟫ ≥ λ‖h‖²` on the graph of `T`, the
  Yosida approximations inherit the bound in the form `T_a ≥ aλ/(a + λ)` (`yosidaCLM_ge`),
  the bounded semigroups decay at that rate (`norm_expNeg_le_exp`, Gronwall on
  `s ↦ e^{2μs}‖e^{-sA}x‖²`), and in the limit `‖e^{-tT}x‖ ≤ e^{-λt}‖x‖`
  (`norm_semigroupS_le_exp`): a spectral gap becomes a decay rate.
-/

namespace BookProof.NonnegSemigroupGenerator

open BookProof.ClosureUniqueness BookProof.PositiveSquareRoot BookProof.NonnegSquareRoot
open BookProof.NonnegResolvent BookProof.NonnegUnitaryGroup BookProof.NonnegSemigroup
open Filter Topology NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

noncomputable local instance ratNormedAlgebra'' : NormedAlgebra ℚ (F →L[ℂ] F) :=
  NormedAlgebra.restrictScalars ℚ ℂ (F →L[ℂ] F)

/-! ## Positivity of the semigroup -/

/-- `e^{-tA}` is a **positive** operator for every self-adjoint `A`: it is the square of the
self-adjoint operator `e^{-tA/2}`. -/
theorem expNeg_nonneg {A : F →L[ℂ] F} (hA : IsSelfAdjoint A) (t : ℝ) : 0 ≤ expNeg A t := by
  set B := expNeg A (t / 2) with hB
  have hBsa : IsSelfAdjoint B := isSelfAdjoint_expNeg hA _
  have hsq : expNeg A t = B * B := by
    rw [hB, ← expNeg_add]
    norm_num
  rw [hsq, ContinuousLinearMap.nonneg_iff_isPositive]
  have hsa : IsSelfAdjoint (B * B) := by
    change star (B * B) = B * B
    rw [star_mul, hBsa.star_eq]
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa, fun x => ?_⟩
  have hsym : (inner ℂ (B (B x)) x : ℂ) = inner ℂ (B x) (B x) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hBsa) (B x) x
  have hval : (B * B) x = B (B x) := rfl
  simp only [ContinuousLinearMap.reApplyInnerSelf, hval, hsym]
  simpa using inner_self_nonneg (𝕜 := ℂ) (x := B x)

variable {T : Submodule ℂ (F × F)}

/-- **`0 ≤ e^{-tT}`**: the limit semigroup is a positive operator. -/
theorem semigroupS_nonneg (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ semigroupS hT hsv ht := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (isSelfAdjoint_semigroupS hT hsv ht),
    fun x => ?_⟩
  have hlim : Tendsto (fun n : ℕ => (inner ℂ (approxS hT n t x) x : ℂ)) atTop
      (𝓝 (inner ℂ (semigroupS hT hsv ht x) x : ℂ)) :=
    (tendsto_semigroupS hT hsv ht x).inner (𝕜 := ℂ) tendsto_const_nhds
  have hre : Tendsto (fun n : ℕ => (inner ℂ (approxS hT n t x) x : ℂ).re) atTop
      (𝓝 (inner ℂ (semigroupS hT hsv ht x) x : ℂ).re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  simp only [ContinuousLinearMap.reApplyInnerSelf]
  refine ge_of_tendsto' hre (fun n => ?_)
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive (approxS hT n t)).1
    (expNeg_nonneg (isSelfAdjoint_yosidaAt hT n) t)
  simpa [ContinuousLinearMap.reApplyInnerSelf] using hpos.2 x

/-! ## Strong continuity in the time variable -/

/-- The semigroup depends on the *value* of the time, not on the proof of its
non-negativity. -/
theorem semigroupS_congr (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s = t) : semigroupS hT hsv hs = semigroupS hT hsv ht := by
  subst hst; rfl

/-- Increments of the orbit are controlled by the increment at the origin. -/
theorem norm_semigroupS_sub_semigroupS_le (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (x : F) :
    ‖semigroupS hT hsv (hs.trans hst) x - semigroupS hT hsv hs x‖
      ≤ ‖semigroupS hT hsv (sub_nonneg.2 hst) x - x‖ := by
  have hd : (0 : ℝ) ≤ t - s := sub_nonneg.2 hst
  have h1 : semigroupS hT hsv (hs.trans hst)
      = semigroupS hT hsv hs * semigroupS hT hsv hd := by
    rw [← semigroupS_add hT hsv hs hd]
    exact semigroupS_congr hT hsv _ _ (by ring)
  have h2 : semigroupS hT hsv (hs.trans hst) x - semigroupS hT hsv hs x
      = semigroupS hT hsv hs (semigroupS hT hsv hd x - x) := by
    rw [map_sub, h1]
    rfl
  rw [h2]
  exact norm_semigroupS_apply_le hT hsv hs _

/-- **Strong continuity in `t`**, uniformly along the orbit: for every vector the map
`t ↦ e^{-tT}x` is uniformly continuous on `[0, ∞)`. -/
theorem semigroupS_uniformly_continuous (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t), |t - s| < δ →
      ‖semigroupS hT hsv ht x - semigroupS hT hsv hs x‖ < ε := by
  obtain ⟨δ, hδ, hbound⟩ := tendsto_semigroupS_zero hT hsv x hε
  refine ⟨δ, hδ, fun s t hs ht habs => ?_⟩
  rcases le_total s t with hst | hts
  · have hd : |t - s| = t - s := abs_of_nonneg (sub_nonneg.2 hst)
    have h1 := norm_semigroupS_sub_semigroupS_le hT hsv hs hst x
    have h2 := hbound (t - s) (sub_nonneg.2 hst) (by rw [hd] at habs; exact habs)
    calc ‖semigroupS hT hsv ht x - semigroupS hT hsv hs x‖
        = ‖semigroupS hT hsv (hs.trans hst) x - semigroupS hT hsv hs x‖ := rfl
      _ ≤ ‖semigroupS hT hsv (sub_nonneg.2 hst) x - x‖ := h1
      _ < ε := h2
  · have hd : |t - s| = s - t := by
      rw [abs_of_nonpos (by linarith)]; ring
    have h1 := norm_semigroupS_sub_semigroupS_le hT hsv ht hts x
    have h2 := hbound (s - t) (sub_nonneg.2 hts) (by rw [hd] at habs; exact habs)
    rw [norm_sub_rev]
    calc ‖semigroupS hT hsv hs x - semigroupS hT hsv ht x‖
        = ‖semigroupS hT hsv (ht.trans hts) x - semigroupS hT hsv ht x‖ := rfl
      _ ≤ ‖semigroupS hT hsv (sub_nonneg.2 hts) x - x‖ := h1
      _ < ε := h2

/-! ## Commutation with the resolvent and invariance of the domain -/

/-- The Yosida approximation commutes with every resolvent. -/
theorem commute_yosidaAt_invCLMAt (hT : IsNonnegSelfAdjoint T) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    Commute (yosidaAt hT n) (invCLMAt hT hb) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcomm : Commute (invCLMAt hT ha) (invCLMAt hT hb) := by
    change invCLMAt hT ha * invCLMAt hT hb = invCLMAt hT hb * invCLMAt hT ha
    ext y
    simpa [ContinuousLinearMap.mul_apply] using invCLMAt_comm hT ha hb y
  have hfin := ((Commute.one_left (invCLMAt hT hb)).sub_left
    (hcomm.smul_left ((((n : ℝ) + 1 : ℝ) : ℂ)))).smul_left ((((n : ℝ) + 1 : ℝ) : ℂ))
  simpa [yosidaAt, yosidaCLM] using hfin

/-- The approximating semigroups commute with every resolvent. -/
theorem commute_approxS_invCLMAt (hT : IsNonnegSelfAdjoint T) (n : ℕ) (t : ℝ) {b : ℝ}
    (hb : 0 < b) : Commute (approxS hT n t) (invCLMAt hT hb) :=
  ((commute_yosidaAt_invCLMAt hT n hb).smul_left (-t : ℝ)).exp_left

/-- **`e^{-tT}` commutes with the resolvent `(T + b)⁻¹`.** -/
theorem semigroupS_invCLMAt_comm (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) {b : ℝ} (hb : 0 < b) (y : F) :
    semigroupS hT hsv ht (invCLMAt hT hb y) = invCLMAt hT hb (semigroupS hT hsv ht y) := by
  refine tendsto_nhds_unique (tendsto_semigroupS hT hsv ht (invCLMAt hT hb y)) ?_
  have h1 : ∀ n : ℕ, approxS hT n t (invCLMAt hT hb y)
      = invCLMAt hT hb (approxS hT n t y) := by
    intro n
    have := congrArg (fun S : F →L[ℂ] F => S y) (commute_approxS_invCLMAt hT n t hb)
    simpa [ContinuousLinearMap.mul_apply] using this
  simp only [h1]
  exact ((invCLMAt hT hb).continuous.tendsto _).comp (tendsto_semigroupS hT hsv ht y)

/-- **The semigroup leaves the domain of `T` invariant and commutes with `T` there**:
`(h, k) ∈ T` implies `(e^{-tT}h, e^{-tT}k) ∈ T`. -/
theorem semigroupS_mem_of_mem (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {t : ℝ} (ht : 0 ≤ t) :
    (semigroupS hT hsv ht h, semigroupS hT hsv ht k) ∈ T := by
  have hone : (0 : ℝ) < 1 := one_pos
  set R := invCLMAt hT hone with hR
  have hRh : R (k + h) = h := by
    refine invCLMAt_eq_of_mem hT hone ?_
    simpa using hk
  have hcomm : semigroupS hT hsv ht (R (k + h)) = R (semigroupS hT hsv ht (k + h)) :=
    semigroupS_invCLMAt_comm hT hsv ht hone _
  have hsplit : semigroupS hT hsv ht (k + h)
      = semigroupS hT hsv ht k + semigroupS hT hsv ht h := map_add _ _ _
  have hkey : R (semigroupS hT hsv ht k + semigroupS hT hsv ht h)
      = semigroupS hT hsv ht h := by
    rw [← hsplit, ← hcomm, hRh]
  have hmem := invCLMAt_mem hT hone (semigroupS hT hsv ht k + semigroupS hT hsv ht h)
  rw [← hR, hkey] at hmem
  simpa using hmem

/-! ## The generator -/

/-- The bounded estimate behind the differential equation: if the orbit of `k` moves by at
most `M` on `[0, t]`, then `e^{-tA}h − h` is `t (‖k − Ah‖ + M)`-close to `−t k`. -/
theorem norm_expNeg_sub_add_smul_le {A : F →L[ℂ] F} (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t)
    (h k : F) {M : ℝ} (hM : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖expNeg A s k - k‖ ≤ M) :
    ‖expNeg A t h - h + t • k‖ ≤ t * (‖k - A h‖ + M) := by
  set g : ℝ → F := fun u => expNeg A u h - h + u • k with hg
  have hderiv : ∀ u ∈ Set.Icc (0 : ℝ) t,
      HasDerivWithinAt g (-(expNeg A u (A h)) + k) (Set.Icc (0 : ℝ) t) u := by
    intro u _
    have h1 : HasDerivAt (fun v : ℝ => expNeg A v h) (-(expNeg A u (A h))) u :=
      hasDerivAt_expNeg A u h
    have h2 : HasDerivAt (fun v : ℝ => v • k) k u := by
      simpa using (hasDerivAt_id u).smul_const k
    exact ((h1.sub_const h).add h2).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) t, ‖-(expNeg A u (A h)) + k‖ ≤ ‖k - A h‖ + M := by
    intro u hu
    have hdec : -(expNeg A u (A h)) + k = expNeg A u (k - A h) + (k - expNeg A u k) := by
      rw [map_sub]; abel
    have h1 : ‖expNeg A u (k - A h)‖ ≤ ‖k - A h‖ := norm_expNeg_le A hA hu.1 _
    have h2 : ‖k - expNeg A u k‖ ≤ M := by
      rw [← norm_neg, neg_sub]
      exact hM u hu
    calc ‖-(expNeg A u (A h)) + k‖
        = ‖expNeg A u (k - A h) + (k - expNeg A u k)‖ := by rw [hdec]
      _ ≤ ‖expNeg A u (k - A h)‖ + ‖k - expNeg A u k‖ := norm_add_le _ _
      _ ≤ ‖k - A h‖ + M := by linarith
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) hderiv hbound
    (convex_Icc (0 : ℝ) t) (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht)
  have hgt : g t = expNeg A t h - h + t • k := rfl
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hgt, hg0, sub_zero] at hmain
  calc ‖expNeg A t h - h + t • k‖ ≤ (‖k - A h‖ + M) * ‖t - (0 : ℝ)‖ := hmain
    _ = t * (‖k - A h‖ + M) := by
        rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg ht]; ring

/-- The same estimate for the limit semigroup: `k'` is any approximation of `k` from the
domain, with `(k', k'') ∈ T`. -/
theorem norm_semigroupS_sub_add_smul_le (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T)
    {k' k'' : F} (hk' : (k', k'') ∈ T) {ε : ℝ} (hkk' : ‖k - k'‖ ≤ ε) {t : ℝ} (ht : 0 ≤ t) :
    ‖semigroupS hT hsv ht h - h + t • k‖ ≤ t * (2 * ε + t * ‖k''‖) := by
  have hstep : ∀ n : ℕ, ‖approxS hT n t h - h + t • k‖
      ≤ t * (‖k - yosidaAt hT n h‖ + (2 * ε + t * ‖k''‖)) := by
    intro n
    refine norm_expNeg_sub_add_smul_le (yosidaAt_nonneg hT n) ht h k ?_
    intro s hs
    have hA := yosidaAt_nonneg hT n
    have h1 : ‖expNeg (yosidaAt hT n) s (k - k')‖ ≤ ‖k - k'‖ :=
      norm_expNeg_le _ hA hs.1 _
    have h2 : ‖expNeg (yosidaAt hT n) s k' - k'‖ ≤ s * ‖yosidaAt hT n k'‖ :=
      norm_expNeg_sub_self_le _ hA hs.1 k'
    have h3 : ‖yosidaAt hT n k'‖ ≤ ‖k''‖ :=
      norm_yosidaCLM_le_of_mem hT (a := (n : ℝ) + 1) (by positivity) hk'
    have hdec : expNeg (yosidaAt hT n) s k - k
        = expNeg (yosidaAt hT n) s (k - k') + (expNeg (yosidaAt hT n) s k' - k') + (k' - k) := by
      rw [map_sub]; abel
    have h4 : ‖k' - k‖ ≤ ε := by rw [norm_sub_rev]; exact hkk'
    have h5 : s * ‖yosidaAt hT n k'‖ ≤ t * ‖k''‖ := by
      have := hs.2
      have hnn : (0 : ℝ) ≤ ‖yosidaAt hT n k'‖ := norm_nonneg _
      nlinarith [norm_nonneg k'', hs.1]
    calc ‖expNeg (yosidaAt hT n) s k - k‖
        ≤ ‖expNeg (yosidaAt hT n) s (k - k') + (expNeg (yosidaAt hT n) s k' - k')‖
            + ‖k' - k‖ := by rw [hdec]; exact norm_add_le _ _
      _ ≤ ‖expNeg (yosidaAt hT n) s (k - k')‖ + ‖expNeg (yosidaAt hT n) s k' - k'‖
            + ‖k' - k‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 2 * ε + t * ‖k''‖ := by
          have := h1.trans hkk'
          linarith [h2.trans h5]
  have hlim : Tendsto (fun n : ℕ => ‖approxS hT n t h - h + t • k‖) atTop
      (𝓝 ‖semigroupS hT hsv ht h - h + t • k‖) :=
    (((tendsto_semigroupS hT hsv ht h).sub tendsto_const_nhds).add tendsto_const_nhds).norm
  have hrhs : Tendsto (fun n : ℕ => t * (‖k - yosidaAt hT n h‖ + (2 * ε + t * ‖k''‖))) atTop
      (𝓝 (t * (0 + (2 * ε + t * ‖k''‖)))) := by
    have hy : Tendsto (fun n : ℕ => ‖k - yosidaAt hT n h‖) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := k) (f := atTop (α := ℕ))).sub
        (tendsto_yosidaAt hT hsv hk)
      simpa using this.norm
    exact ((hy.add tendsto_const_nhds).const_mul t)
  have := le_of_tendsto_of_tendsto' hlim hrhs hstep
  simpa using this

/-- **The differential equation at `t = 0`**: `t⁻¹ (e^{-tT}h − h) → −k` as `t ↓ 0`, for
every `(h, k) ∈ T`. -/
theorem tendsto_semigroupS_difference_quotient (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (t : ℝ) (ht : 0 < t), t < δ →
      ‖t⁻¹ • (semigroupS hT hsv ht.le h - h) + k‖ < ε := by
  obtain ⟨z, hz, hkz⟩ := (dense_domain hT hsv).exists_dist_lt k (ε := ε / 8) (by linarith)
  obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hz
  have hpy : (z, p.2) ∈ T := by
    have hpe : p = (z, p.2) := by rw [← hp1]; simp
    rwa [← hpe]
  have hkz' : ‖k - z‖ ≤ ε / 8 := by
    rw [← dist_eq_norm]
    exact hkz.le
  refine ⟨ε / (2 * (‖p.2‖ + 1)), by positivity, fun t ht htδ => ?_⟩
  have hmain := norm_semigroupS_sub_add_smul_le hT hsv hk hpy hkz' ht.le
  have hrw : t⁻¹ • (semigroupS hT hsv ht.le h - h) + k
      = t⁻¹ • (semigroupS hT hsv ht.le h - h + t • k) := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  have hnorm : ‖(t⁻¹ : ℝ)‖ = t⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht)]
  have htp : 0 < ‖p.2‖ + 1 := by positivity
  have hsmall : t * ‖p.2‖ < ε / 2 := by
    have h1 : t < ε / (2 * (‖p.2‖ + 1)) := htδ
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg p.2]
  rw [hrw, norm_smul, hnorm]
  have hb : t⁻¹ * ‖semigroupS hT hsv ht.le h - h + t • k‖
      ≤ t⁻¹ * (t * (2 * (ε / 8) + t * ‖p.2‖)) := by
    have : (0 : ℝ) ≤ t⁻¹ := (inv_pos.2 ht).le
    exact mul_le_mul_of_nonneg_left hmain this
  have heq : t⁻¹ * (t * (2 * (ε / 8) + t * ‖p.2‖)) = 2 * (ε / 8) + t * ‖p.2‖ := by
    field_simp
  rw [heq] at hb
  linarith

/-- **The differential equation at a general time**:
`u⁻¹ (e^{-(t+u)T}h − e^{-tT}h) → −e^{-tT}k` as `u ↓ 0`. -/
theorem tendsto_semigroupS_difference_quotient_at (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {t : ℝ} (ht : 0 ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (u : ℝ) (hu : 0 < u), u < δ →
      ‖u⁻¹ • (semigroupS hT hsv (add_nonneg ht hu.le) h - semigroupS hT hsv ht h)
        + semigroupS hT hsv ht k‖ < ε := by
  obtain ⟨δ, hδ, hbound⟩ :=
    tendsto_semigroupS_difference_quotient hT hsv (semigroupS_mem_of_mem hT hsv hk ht) hε
  refine ⟨δ, hδ, fun u hu huδ => ?_⟩
  have hsplit : semigroupS hT hsv (add_nonneg ht hu.le) h
      = semigroupS hT hsv hu.le (semigroupS hT hsv ht h) := by
    have h1 : semigroupS hT hsv (add_nonneg ht hu.le)
        = semigroupS hT hsv (add_nonneg hu.le ht) :=
      semigroupS_congr hT hsv _ _ (by ring)
    rw [h1, semigroupS_add hT hsv hu.le ht]
    rfl
  rw [hsplit]
  exact hbound u hu huδ

/-! ## Exponential decay from a spectral lower bound -/

/-- **Decay for a bounded generator**: if `Re⟪Ax, x⟫ ≥ μ‖x‖²` for every `x`, then
`‖e^{-tA}x‖ ≤ e^{-μt}‖x‖` for `t ≥ 0`.  (Gronwall on `s ↦ e^{2μs}‖e^{-sA}x‖²`.) -/
theorem norm_expNeg_le_exp (A : F →L[ℂ] F) {mu : ℝ}
    (hmu : ∀ x : F, mu * ‖x‖ ^ 2 ≤ (inner ℂ (A x) x : ℂ).re) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖expNeg A t x‖ ≤ Real.exp (-(mu * t)) * ‖x‖ := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.exp (2 * mu * s) * ‖expNeg A s x‖ ^ 2)
      (Real.exp (2 * mu * s) * (2 * mu) * ‖expNeg A s x‖ ^ 2
        + Real.exp (2 * mu * s)
          * (-2 * (inner ℂ (A (expNeg A s x)) (expNeg A s x) : ℂ).re)) s := by
    intro s
    have hE : HasDerivAt (fun s : ℝ => Real.exp (2 * mu * s))
        (Real.exp (2 * mu * s) * (2 * mu)) s := by
      have h1 : HasDerivAt (fun y : ℝ => 2 * mu * y) (2 * mu) s := by
        simpa using (hasDerivAt_id s).const_mul (2 * mu)
      exact h1.exp
    exact hE.mul (hasDerivAt_normSq_expNeg A x s)
  have hanti : Antitone (fun s : ℝ => Real.exp (2 * mu * s) * ‖expNeg A s x‖ ^ 2) := by
    refine antitone_of_deriv_nonpos (fun s => (hderiv s).differentiableAt) (fun s => ?_)
    rw [(hderiv s).deriv]
    have h1 := hmu (expNeg A s x)
    have h2 : (0 : ℝ) < Real.exp (2 * mu * s) := Real.exp_pos _
    nlinarith
  have hkey := hanti ht
  simp only [mul_zero, Real.exp_zero, one_mul, expNeg_zero,
    ContinuousLinearMap.one_apply] at hkey
  have hsq : ‖expNeg A t x‖ ^ 2 ≤ (Real.exp (-(mu * t)) * ‖x‖) ^ 2 := by
    have hpos : (0 : ℝ) < Real.exp (2 * mu * t) := Real.exp_pos _
    have hmul : ‖expNeg A t x‖ ^ 2 ≤ Real.exp (-(2 * mu * t)) * ‖x‖ ^ 2 := by
      rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ hpos]
      linarith [hkey]
    have hrw : Real.exp (-(2 * mu * t)) * ‖x‖ ^ 2 = (Real.exp (-(mu * t)) * ‖x‖) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      ring_nf
    linarith [hmul, hrw.le, hrw.ge]
  have h1 : (0 : ℝ) ≤ ‖expNeg A t x‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ Real.exp (-(mu * t)) * ‖x‖ := by positivity
  nlinarith [hsq, h1, h2]

/-- **The Yosida approximation inherits a spectral lower bound**: if `Re⟪h, k⟫ ≥ λ‖h‖²` on
the graph of `T`, then `T_a ≥ aλ/(a + λ)`. -/
theorem yosidaCLM_ge (hT : IsNonnegSelfAdjoint T) {a lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam)
    (hgap : ∀ h k : F, (h, k) ∈ T → lam * ‖h‖ ^ 2 ≤ (inner ℂ h k : ℂ).re) (h : F) :
    (a * lam / (a + lam)) * ‖h‖ ^ 2 ≤ (inner ℂ (yosidaCLM hT ha h) h : ℂ).re := by
  set y : F := (a : ℂ) • invCLMAt hT ha h with hy
  set z : F := yosidaCLM hT ha h with hz
  have hmem : (y, z) ∈ T := yosidaCLM_mem hT ha h
  have hsum : (a : ℂ) • h = (a : ℂ) • y + z := by
    rw [hy, hz, yosidaCLM_apply, smul_smul, smul_sub, smul_smul]
    module
  set v : ℝ := (inner ℂ y z : ℂ).re with hv
  have hvz : (inner ℂ z y : ℂ).re = v := by
    rw [hv, ← inner_conj_symm z y, Complex.conj_re]
  have hgapy : lam * ‖y‖ ^ 2 ≤ v := hgap y z hmem
  have hcs : v ≤ ‖y‖ * ‖z‖ := by
    rw [hv]
    exact re_inner_le_norm (𝕜 := ℂ) y z
  have hzy : lam * ‖y‖ ≤ ‖z‖ := by
    rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
    · rw [← h0]
      simp
    · have := hgapy.trans hcs
      have hy2 : lam * ‖y‖ * ‖y‖ ≤ ‖y‖ * ‖z‖ := by nlinarith
      nlinarith
  -- the two Pythagoras identities
  have hnorma : ‖((a : ℝ) : ℂ)‖ = a := by simp [abs_of_pos ha]
  have hE1 : a ^ 2 * ‖h‖ ^ 2 = a ^ 2 * ‖y‖ ^ 2 + 2 * a * v + ‖z‖ ^ 2 := by
    have hn : ‖(a : ℂ) • h‖ ^ 2 = ‖(a : ℂ) • y + z‖ ^ 2 := by rw [hsum]
    have hl : ‖(a : ℂ) • h‖ ^ 2 = a ^ 2 * ‖h‖ ^ 2 := by
      rw [norm_smul, hnorma, mul_pow]
    have hay : ‖(a : ℂ) • y‖ ^ 2 = a ^ 2 * ‖y‖ ^ 2 := by
      rw [norm_smul, hnorma, mul_pow]
    have hinner : (inner ℂ ((a : ℂ) • y) z : ℂ).re = a * v := by
      rw [inner_smul_left, Complex.conj_ofReal, Complex.mul_re]
      simp [hv]
    rw [hl, norm_add_sq (𝕜 := ℂ), hay] at hn
    simp only [RCLike.re_to_complex] at hn
    rw [hinner] at hn
    linarith
  have hE2 : a * (inner ℂ z h : ℂ).re = a * v + ‖z‖ ^ 2 := by
    have hstep : (inner ℂ z ((a : ℂ) • h) : ℂ) = inner ℂ z ((a : ℂ) • y + z) := by rw [hsum]
    rw [inner_add_right, inner_smul_right, inner_smul_right] at hstep
    have := congrArg Complex.re hstep
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re] at this
    rw [hvz] at this
    have hzz : (inner ℂ z z : ℂ).re = ‖z‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) z
    rw [this, hzz]
  -- the algebraic core
  have hN : 0 ≤ v * (a - lam) + ‖z‖ ^ 2 - lam * a * ‖y‖ ^ 2 := by
    rcases le_total lam a with hc | hc
    · nlinarith [hgapy, hzy, norm_nonneg y, norm_nonneg z]
    · have hfac : 0 ≤ (‖z‖ - lam * ‖y‖) * (‖z‖ + a * ‖y‖) := by
        have h1 : 0 ≤ ‖z‖ - lam * ‖y‖ := by linarith
        have h2 : 0 ≤ ‖z‖ + a * ‖y‖ := by positivity
        exact mul_nonneg h1 h2
      nlinarith [hcs, hfac, norm_nonneg y, norm_nonneg z]
  have hid : a ^ 2 * ((inner ℂ z h : ℂ).re * (a + lam) - a * lam * ‖h‖ ^ 2)
      = a ^ 2 * (v * (a - lam) + ‖z‖ ^ 2 - lam * a * ‖y‖ ^ 2) := by
    linear_combination (a * (a + lam)) * hE2 - (a * lam) * hE1
  have hcancel : (inner ℂ z h : ℂ).re * (a + lam) - a * lam * ‖h‖ ^ 2
      = v * (a - lam) + ‖z‖ ^ 2 - lam * a * ‖y‖ ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 2 ha.ne') hid
  have hsum' : 0 < a + lam := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ hsum']
  linarith [hN, hcancel]

/-- **Exponential decay of the semigroup below a spectral gap**: if `Re⟪h, k⟫ ≥ λ‖h‖²` for
every `(h, k) ∈ T` with `λ ≥ 0`, then `‖e^{-tT}x‖ ≤ e^{-λt}‖x‖` for every `t ≥ 0`. -/
theorem norm_semigroupS_le_exp (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {lam : ℝ} (hlam : 0 ≤ lam)
    (hgap : ∀ h k : F, (h, k) ∈ T → lam * ‖h‖ ^ 2 ≤ (inner ℂ h k : ℂ).re)
    {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖semigroupS hT hsv ht x‖ ≤ Real.exp (-(lam * t)) * ‖x‖ := by
  have hstep : ∀ n : ℕ, ‖approxS hT n t x‖
      ≤ Real.exp (-((((n : ℝ) + 1) * lam / (((n : ℝ) + 1) + lam)) * t)) * ‖x‖ := by
    intro n
    exact norm_expNeg_le_exp (yosidaAt hT n)
      (fun w => yosidaCLM_ge hT (a := (n : ℝ) + 1) (by positivity) hlam hgap w) ht x
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 1) + lam) atTop atTop := by
    refine tendsto_atTop_mono (fun n : ℕ => ?_) tendsto_natCast_atTop_atTop
    linarith
  have hzero : Tendsto (fun n : ℕ => lam ^ 2 / (((n : ℝ) + 1) + lam)) atTop (𝓝 0) :=
    hden.const_div_atTop _
  have hmu : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * lam / (((n : ℝ) + 1) + lam)) atTop (𝓝 lam) := by
    have hsub := (tendsto_const_nhds (x := lam) (f := atTop (α := ℕ))).sub hzero
    rw [sub_zero] at hsub
    refine hsub.congr (fun n => ?_)
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) + lam := by positivity
    field_simp
    ring
  have hrhs : Tendsto
      (fun n : ℕ => Real.exp (-((((n : ℝ) + 1) * lam / (((n : ℝ) + 1) + lam)) * t)) * ‖x‖)
      atTop (𝓝 (Real.exp (-(lam * t)) * ‖x‖)) :=
    (Real.continuous_exp.tendsto _ |>.comp ((hmu.mul tendsto_const_nhds).neg)).mul
      tendsto_const_nhds
  exact le_of_tendsto_of_tendsto' ((tendsto_semigroupS hT hsv ht x).norm) hrhs hstep

end BookProof.NonnegSemigroupGenerator


