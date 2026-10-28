-- Prove2me | Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
-- name    : KLSModular_BrownianMotion_Gaussian_BrownianMotion
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:42:39.952988+00:00
-- url     : https://prove2.me/theorems/649e1eeb-150a-4919-a925-1b143db57096
-- title:
--   Canonical Brownian motion from a Gaussian projective limit
-- statement:
--   Vendored from the BrownianMotion library, repository https://github.com/RemyDegenne/brownian-motion, commit a7ad7af662044313bc80a7c0756360fb3745f931. A process satisfying `IsPreBrownianReal` has the finite-dimensional laws of the canonical nonnegative-time Gaussian process; `preBrownian` is the coordinate process on `gaussianLimit`, and `brownian` is a noncomputably chosen continuous modification of it. `HasLaw.IsPreBrownianReal` transfers the canonical finite-dimensional law condition, while `IsPreBrownianReal.isAEKolmogorovProcess` supplies the stated even-moment increment bound for positive integer exponents. The result `IsPreBrownianReal.exists_continuous_modification` gives a measurable modification whose paths are locally β-Hölder for β in the explicitly specified range below 1/2, and the file also supplies the Borel and measurable-space instances for continuous maps.
--
--   **Original module imports**
--
--   ```lean
--   public import BrownianMotion.Auxiliary.HasLaw
--   public import BrownianMotion.Continuity.KolmogorovChentsov
--   public import BrownianMotion.Gaussian.CovMatrix
--   public import BrownianMotion.Gaussian.GaussianProcess
--   public import BrownianMotion.Gaussian.Moment
--   public import BrownianMotion.Gaussian.ProjectiveLimit
--   public import Mathlib.Probability.ConditionalExpectation
--   public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
--   public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
--   public import Mathlib.Probability.Independence.BoundedContinuousFunction
--   public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
--   public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
--   public import Mathlib.Probability.BrownianMotion.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   protected noncomputable def IsPreBrownianReal.mk (X) (h : IsPreBrownianReal X P) : ℝ≥0 → Ω → ℝ :=
--     h.exists_continuous_modification.choose
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`BrownianMotion/Auxiliary/HasLaw`](https://prove2.me/theorems/57cfac41-866e-49cc-bb26-d87715ab27c5), [`BrownianMotion/Continuity/KolmogorovChentsov`](https://prove2.me/theorems/1a8dc606-1f9c-4b34-b930-dbe8b859391f), [`BrownianMotion/Gaussian/CovMatrix`](https://prove2.me/theorems/d80696ff-da68-4d43-8075-a81458b3bcd2), [`BrownianMotion/Gaussian/GaussianProcess`](https://prove2.me/theorems/fa543ae6-e9ed-4def-ba67-54ac5ce2461d), [`BrownianMotion/Gaussian/Moment`](https://prove2.me/theorems/8fd71939-804d-4268-8004-6618d58ce16f), [`BrownianMotion/Gaussian/ProjectiveLimit`](https://prove2.me/theorems/2e20a93b-e9e8-4194-ab6e-28d84386dee2).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/BrownianMotion/BrownianMotion/Gaussian/BrownianMotion.lean) · `BrownianMotion.Gaussian.BrownianMotion` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/BrownianMotion/Gaussian/BrownianMotion.lean#L188-L633 (repository human-ai-mathematics/kls-lean, commit 408915f, module `BrownianMotion.Gaussian.BrownianMotion`, definition bundle `KLSModular_BrownianMotion_Gaussian_BrownianMotion`; the repository is private at upload time). Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_BrownianMotion_Auxiliary_HasLaw
import Definitions.Def_KLSModular_BrownianMotion_Continuity_KolmogorovChentsov
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_CovMatrix
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_GaussianProcess
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_Moment
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_ProjectiveLimit
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.BoundedContinuousFunction
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Probability.BrownianMotion.Basic

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- Vendored from https://github.com/RemyDegenne/brownian-motion at commit a7ad7af662044313bc80a7c0756360fb3745f931 (upstream path BrownianMotion/Gaussian/BrownianMotion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory NNReal WithLp Finset MeasurableSpace Filtration Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
namespace ProbabilityTheory
section IsPreBrownianReal
variable (X : ℝ≥0 → Ω → ℝ)
variable {X} {P : Measure Ω}
lemma HasLaw.IsPreBrownianReal (hX : HasLaw (fun ω ↦ (X · ω)) gaussianLimit P) :
    IsPreBrownianReal X P where
  hasLaw _ := hasLaw_restrict_gaussianLimit.comp hX
lemma IsPreBrownianReal.isAEKolmogorovProcess {n : ℕ} (hn : 0 < n) (h : IsPreBrownianReal X P) :
    IsAEKolmogorovProcess X P (2 * n) n (Nat.doubleFactorial (2 * n - 1)) := by
  let Y t ω := (h.aemeasurable t).mk (X t) ω
  have hXY t := (h.aemeasurable t).ae_eq_mk
  have hY := h.congr hXY
  refine ⟨Y, ?_, ?_⟩
  constructor
  · intro s t
    rw [← BorelSpace.measurable_eq]
    refine Measurable.prodMk (h.aemeasurable s).measurable_mk (h.aemeasurable t).measurable_mk
  rotate_left
  · positivity
  · positivity
  · exact fun t ↦ (h.aemeasurable t).ae_eq_mk
  refine fun s t ↦ Eq.le ?_
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change ∫⁻ ω, (fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    ((Y s - Y t) ω) ∂_ = _
  rw [(hY.hasLaw_sub s t).lintegral_comp (f := fun x ↦ (ENNReal.ofReal |x|) ^ (2 * n))
    (by fun_prop)]
  simp_rw [← fun x ↦ ENNReal.ofReal_pow (abs_nonneg x)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [pow_two_mul_abs]
    rw [← centralMoment_of_integral_id_eq_zero _ (by simp), ← NNReal.sq_sqrt (nndist _ _),
    centralMoment_fun_two_mul_gaussianReal, ENNReal.ofReal_mul (by positivity), mul_comm]
    norm_cast
    congr
    rw [pow_mul, NNReal.sq_sqrt]
    simp only [val_eq_coe, NNReal.coe_pow, coe_nndist, dist_nonneg, ENNReal.ofReal_pow]
    congr
  · simp_rw [← Real.norm_eq_abs]
    apply MemLp.integrable_norm_pow'
    exact IsGaussian.memLp_id _ _ (ENNReal.natCast_ne_top (2 * n))
  · exact ae_of_all _ fun _ ↦ by positivity
/-- If `X` is a pre-Brownian process then there exists a modification of `X` which is measurable
and locally β-Hölder for `0 < β < 1/2` (and thus continuous). See `IsPreBrownianReal.mk`. -/
lemma IsPreBrownianReal.exists_continuous_modification (h : IsPreBrownianReal X P) :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (((n + 2 : ℕ) : ℝ) - 1) / (2 * (n + 2 : ℕ))),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U :=
  haveI := h.isGaussianProcess.isProbabilityMeasure
  exists_modification_holder_iSup isCoverWithBoundedCoveringNumber_Ico_nnreal
    (fun n ↦ h.isAEKolmogorovProcess (by positivity : 0 < n + 2))
    (fun n ↦ by finiteness) zero_lt_one (fun n ↦ by simp; norm_cast; omega)
/-- If `h : IsPreBrownianReal X P`, then `h.mk X` is a continuous modification of `X`. -/
protected noncomputable def IsPreBrownianReal.mk (X) (h : IsPreBrownianReal X P) : ℝ≥0 → Ω → ℝ :=
  h.exists_continuous_modification.choose
end IsPreBrownianReal
def preBrownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω ↦ ω t
@[fun_prop]
lemma measurable_preBrownian (t : ℝ≥0) : Measurable (preBrownian t) := by
  unfold preBrownian
  fun_prop
lemma hasLaw_preBrownian : HasLaw (fun ω ↦ (preBrownian · ω)) gaussianLimit gaussianLimit where
  aemeasurable := (measurable_pi_lambda _ measurable_preBrownian).aemeasurable
  map_eq := Measure.map_id
lemma isPreBrownianReal_preBrownian : IsPreBrownianReal preBrownian gaussianLimit :=
  hasLaw_preBrownian.IsPreBrownianReal
noncomputable
def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := isPreBrownianReal_preBrownian.mk
section Measure
section ContinuousMap.MeasurableSpace
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
instance : MeasurableSpace C(X, Y) := borel _
instance : BorelSpace C(X, Y) where
  measurable_eq := rfl
end ContinuousMap.MeasurableSpace
end Measure
end ProbabilityTheory


