-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_SmoothBall
-- name    : KLSModular_FunctionalInequalities_Analysis_Cutoff_SmoothBall
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:18:34.129574+00:00
-- url     : https://prove2.me/theorems/e579c572-cae8-4aab-bbfa-980860e9fc63
-- title:
--   Smooth radial cutoffs and local Lipschitz bounds
-- statement:
--   `bump` is a fixed smooth function equal to $1$ on the closed unit ball and $0$ outside the radius-two ball, while `scaled R` rescales it to equal $1$ on radius $R$ and vanish outside radius $2R$. For $R>0$, the declarations `scaled_nonneg`, `scaled_le_one`, `scaled_eq_one`, `scaled_eq_zero`, `contDiff_scaled`, and `fderiv_scaled_eq_zero` give its range, support, smoothness, and vanishing derivative on the inner ball; `hasFDerivAt_scaled`, `norm_fderiv_scaled_le`, and `lipschitzWith_scaled` give derivative and Lipschitz estimates from a global derivative bound for the fixed bump. The bundle also proves the product gradient rule `gradient_scaled_mul`, existence of a nonnegative global derivative bound `exists_bound_fderiv_bump`, and that a locally Lipschitz function is Lipschitz on every compact set via `lipschitzOnWith_of_locallyLipschitz_of_isCompact`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
--   import Mathlib.Analysis.Calculus.BumpFunction.Normed
--   import Mathlib.Analysis.Calculus.MeanValue
--   import Mathlib.MeasureTheory.Measure.Haar.Basic
--   import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
--   import Mathlib.Topology.MetricSpace.Lipschitz
--   import FunctionalInequalities.Analysis.Lipschitz.Gradient
--   import FunctionalInequalities.Analysis.Cutoff.Profile
--   import Mathlib.Analysis.Calculus.FDeriv.Norm
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def bump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Lipschitz/Gradient`](https://prove2.me/theorems/c121ae0a-019e-498c-bab1-b5d194574dc8), [`Analysis/Cutoff/Profile`](https://prove2.me/theorems/2770d0f0-88ba-4965-8db8-6b9999985219).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Cutoff/SmoothBall.lean) · `FunctionalInequalities.Analysis.Cutoff.SmoothBall` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Cutoff/SmoothBall.lean#L37-L181 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Cutoff.SmoothBall`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Cutoff_SmoothBall`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_Profile
import Mathlib.Analysis.Calculus.FDeriv.Norm

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
namespace FunctionalInequalities
namespace Energy
namespace Euclidean
namespace LipschitzApproximation
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Basic
/-- A fixed smooth bump: one on the closed unit ball, zero outside radius two. -/
def bump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
/-- The bump rescaled to be one on radius `R` and zero outside radius `2 * R`. -/
def scaled (R : ℝ) (x : E) : ℝ := (bump (E := E)) (R⁻¹ • x)
theorem scaled_nonneg (R : ℝ) (x : E) : 0 ≤ scaled R x := by
  unfold scaled; exact (bump (E := E)).nonneg
theorem scaled_le_one (R : ℝ) (x : E) : scaled R x ≤ 1 := by
  unfold scaled; exact (bump (E := E)).le_one
theorem scaled_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : scaled R x = 1 := by
  unfold scaled
  apply (bump (E := E)).one_of_mem_closedBall
  show R⁻¹ • x ∈ Metric.closedBall (0 : E) 1
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hR, inv_mul_le_iff₀ hR, mul_one]
  exact hx
theorem scaled_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) : scaled R x = 0 := by
  unfold scaled
  apply (bump (E := E)).zero_of_le_dist
  show (2 : ℝ) ≤ dist (R⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, le_inv_mul_iff₀ hR]
  linarith
theorem contDiff_scaled (R : ℝ) : ContDiff ℝ ∞ (scaled (E := E) R) := by
  unfold scaled
  exact ((bump (E := E)).contDiff (n := ⊤)).comp (contDiff_const_smul R⁻¹)
theorem continuous_scaled (R : ℝ) : Continuous (scaled (E := E) R) :=
  (contDiff_scaled R).continuous
theorem hasFDerivAt_scaled (R : ℝ) (x : E) :
    HasFDerivAt (scaled R) (R⁻¹ • fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)) x := by
  have h1 : HasFDerivAt (fun y : E => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have h2 : HasFDerivAt (⇑(bump (E := E))) (fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)) (R⁻¹ • x) :=
    (((bump (E := E)).contDiff (n := 1)).differentiable (by simp) (R⁻¹ • x)).hasFDerivAt
  have h3 : (fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ E) =
      R⁻¹ • fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x) := by
    ext v
    simp
  unfold scaled
  exact (h2.comp x h1).congr_fderiv h3
theorem fderiv_scaled_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ < R) :
    fderiv ℝ (scaled R) x = 0 := by
  have h : scaled (E := E) R =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : E) R by
      simpa [Metric.mem_ball, dist_zero_right] using hx)] with y hy
    exact scaled_eq_one hR (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy))
  rw [h.fderiv_eq]
  simp
theorem norm_fderiv_scaled_le {R : ℝ} (hR : 0 < R) {M : ℝ}
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M) (x : E) :
    ‖fderiv ℝ (scaled R) x‖ ≤ R⁻¹ * M := by
  rw [(hasFDerivAt_scaled R x).fderiv, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  gcongr
  exact hM _
theorem lipschitzWith_scaled {R : ℝ} (hR : 0 < R) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M) :
    LipschitzWith (R⁻¹ * M).toNNReal (scaled (E := E) R) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((contDiff_scaled R).differentiable (by simp))
  intro x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  exact norm_fderiv_scaled_le hR hM x
theorem gradient_scaled_mul [CompleteSpace E] {R : ℝ} {g : E → ℝ} {x : E} (hx : DifferentiableAt ℝ g x) :
    gradient (fun y => scaled R y * g y) x =
      scaled R x • gradient g x + g x • gradient (scaled R) x := by
  have h1 : HasFDerivAt (scaled R) (fderiv ℝ (scaled R) x) x :=
    (hasFDerivAt_scaled R x).differentiableAt.hasFDerivAt
  have h : HasFDerivAt (fun y => scaled R y * g y)
      (scaled R x • fderiv ℝ g x + g x • fderiv ℝ (scaled R) x) x := h1.mul hx.hasFDerivAt
  rw [gradient_eq_of_hasFDerivAt h]
  simp only [map_add, map_smulₛₗ, starRingEnd_apply, star_trivial]
  rfl
end Basic
section FiniteDimensional
variable [FiniteDimensional ℝ E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A locally Lipschitz real function is Lipschitz on every compact set. -/
theorem lipschitzOnWith_of_locallyLipschitz_of_isCompact {f : E → ℝ} (hf : LocallyLipschitz f)
    {s : Set E} (hs : IsCompact s) : ∃ K : NNReal, LipschitzOnWith K f s := by
  have key : ∀ x : E, ∃ r : ℝ, 0 < r ∧ ∃ K : NNReal, LipschitzOnWith K f (Metric.ball x r) := by
    intro x
    obtain ⟨K, t, ht, hK⟩ := hf x
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
    exact ⟨r, hr, K, hK.mono hrt⟩
  choose r hr K hK using key
  obtain ⟨T, -, hT⟩ := hs.elim_nhds_subcover (fun x => Metric.ball x (r x))
    (fun x _ => Metric.ball_mem_nhds x (hr x))
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric (ι := T)
    (c := fun i => Metric.ball (i : E) (r i)) hs (fun _ => Metric.isOpen_ball)
    (fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hT hx)
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf.continuous.continuousOn
  set K' : NNReal := T.sup K with hK'
  set C' : ℝ := max C 0 with hC'
  refine ⟨(max (K' : ℝ) (2 * C' / δ)).toNNReal, LipschitzOnWith.of_dist_le' ?_⟩
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · obtain ⟨i, hi⟩ := hcover x hx
    have hxi : x ∈ Metric.ball (i : E) (r i) := hi (Metric.mem_ball_self hδ)
    have hyi : y ∈ Metric.ball (i : E) (r i) := hi (by simpa [dist_comm] using hxy)
    have hKi : LipschitzOnWith (K i) f (Metric.ball (i : E) (r i)) := hK i
    calc dist (f x) (f y) ≤ K i * dist x y := hKi.dist_le_mul x hxi y hyi
      _ ≤ K' * dist x y := by
          gcongr
          exact_mod_cast Finset.le_sup (f := K) i.2
      _ ≤ max (K' : ℝ) (2 * C' / δ) * dist x y := by gcongr; exact le_max_left _ _
  · push Not at hxy
    have hCx : ‖f x‖ ≤ C' := (hC x hx).trans (le_max_left _ _)
    have hCy : ‖f y‖ ≤ C' := (hC y hy).trans (le_max_left _ _)
    have hC0 : 0 ≤ C' := le_max_right _ _
    calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * C' := by linarith
      _ = (2 * C' / δ) * δ := by field_simp
      _ ≤ (2 * C' / δ) * dist x y := by gcongr
      _ ≤ max (K' : ℝ) (2 * C' / δ) * dist x y := by gcongr; exact le_max_right _ _
theorem exists_bound_fderiv_bump :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M := by
  have hc : Continuous (fderiv ℝ (⇑(bump (E := E)))) :=
    ((bump (E := E)).contDiff (n := 1)).continuous_fderiv (by simp)
  have hs : HasCompactSupport (fderiv ℝ (⇑(bump (E := E)))) :=
    (bump (E := E)).hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
end FiniteDimensional
end LipschitzApproximation
end Euclidean
end Energy
end FunctionalInequalities


