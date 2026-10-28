-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Transport
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:20:52.909142+00:00
-- url     : https://prove2.me/theorems/e2b06803-5a96-41cf-bc8d-6b89b02cb255
-- title:
--   Transport and geometric consequences of compact log-concavity
-- statement:
--   `LogConcave.of_affineIsometry_map` transfers compact-set log-concavity through an affine isometry when the source probability measure maps to the target measure. For a log-concave probability law on a proper metric space, `LogConcave.closedBall_mul_le` gives the log-concavity inequality for equal-radius closed-ball masses; consequently `convex_support` makes the topological support convex and `convex_closedBall_superlevel` makes each equal-radius ball-mass superlevel set convex. These are geometric and transport lemmas and do not introduce a density or a Poincaré inequality.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Probability.AffineSupport
--   import FunctionalInequalities.Probability.LogConcave
--   import Mathlib.Analysis.Convex.Measure
--   import Mathlib.Topology.Maps.Proper.Basic
--   import Mathlib.Probability.ConditionalProbability
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   theorem of_affineIsometry_map {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
--       (ν : ProbabilityMeasure F) (f : F →ᵃⁱ[ℝ] E)
--       (hmap : Measure.map f (ν : Measure F) = (μ : Measure E)) : LogConcave ν
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Theorems in source order:
--
--   - [`map_affineIsometry`](https://prove2.me/theorems/24db795f-31a5-42d9-9329-a7272770b5c9)
--   - [`cond`](https://prove2.me/theorems/a9c544d7-ce6e-4338-89f4-f44a4207b027)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean) · `FunctionalInequalities.KLS.LogConcave.Transport` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean#L31-L173 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Transport`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Transport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Probability.ConditionalProbability

noncomputable section
open MeasureTheory Set Topology
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
section Transport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
/-- A probability law reconstructed by an affine isometry inherits compact-set log-concavity
from its ambient law. Images of compact sets supply the exact test sets. -/
theorem of_affineIsometry_map {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (ν : ProbabilityMeasure F) (f : F →ᵃⁱ[ℝ] E)
    (hmap : Measure.map f (ν : Measure F) = (μ : Measure E)) : LogConcave ν := by
  intro K L hK hL t ht ht1
  have hm (S : Set F) (hS : IsCompact S) : (μ : Measure E) (f '' S) = (ν : Measure F) S := by
    rw [← hmap, Measure.map_apply f.continuous.measurable (hS.image f.continuous).measurableSet,
      Set.preimage_image_eq _ f.injective]
  have hcomb : f '' {z | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
      {z | ∃ x ∈ f '' K, ∃ y ∈ f '' L, z = t • x + (1 - t) • y} := by
    have hf (x y : F) : f (t • x + (1 - t) • y) = t • f x + (1 - t) • f y := by
      simpa only [AffineMap.lineMap_apply_module, sub_sub_cancel, AffineIsometry.coe_toAffineMap]
        using f.toAffineMap.apply_lineMap x y (1 - t)
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, hf x y⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨t • x + (1 - t) • y, ⟨x, hx, y, hy, rfl⟩, hf x y⟩
  have hc : IsCompact {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he : {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : F × F => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x,y), ⟨hx,hy⟩, rfl⟩
      · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩; exact ⟨x,hx,y,hy,rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  have h := hμ (f '' K) (f '' L) (hK.image f.continuous) (hL.image f.continuous) t ht ht1
  rwa [hm K hK, hm L hL, ← hcomb, hm _ hc] at h
variable [ProperSpace E]
omit [BorelSpace E] in
/-- Equal-radius closed-ball masses inherit the log-concavity inequality. This is the
pointwise inequality needed for ball-average regularizations of the measure. -/
theorem closedBall_mul_le {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (x y : E) (r t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (μ : Measure E) (Metric.closedBall x r) ^ t *
        (μ : Measure E) (Metric.closedBall y r) ^ (1 - t) ≤
      (μ : Measure E) (Metric.closedBall (t • x + (1 - t) • y) r) := by
  refine (hμ _ _ (isCompact_closedBall x r) (isCompact_closedBall y r) t ht ht1).trans
    (measure_mono ?_)
  rintro z ⟨u, hu, v, hv, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [Metric.mem_closedBall, dist_eq_norm] at hu hv
  have heq : t • u + (1 - t) • v - (t • x + (1 - t) • y) =
      t • (u - x) + (1 - t) • (v - y) := by simp only [smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖t • (u - x)‖ + ‖(1 - t) • (v - y)‖ := norm_add_le _ _
    _ = t * ‖u - x‖ + (1 - t) * ‖v - y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos ht, abs_of_pos (sub_pos.mpr ht1)]
    _ ≤ t * r + (1 - t) * r :=
      add_le_add (mul_le_mul_of_nonneg_left hu ht.le)
        (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr ht1.le))
    _ = r := by ring
omit [BorelSpace E] in
/-- Compact-set log-concavity forces the topological support to be convex. This uses positive
neighborhood masses, without presupposing an ambient density. -/
theorem convex_support {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    Convex ℝ (μ : Measure E).support := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha1 : a < 1 := by linarith
  have hbeq : b = 1 - a := by linarith
  apply Metric.nhds_basis_closedBall.mem_measureSupport.mpr
  intro r hr
  have hxr := (Measure.mem_support_iff_forall x).mp hx _ (Metric.closedBall_mem_nhds x hr)
  have hyr := (Measure.mem_support_iff_forall y).mp hy _ (Metric.closedBall_mem_nhds y hr)
  have hpos : 0 < (μ : Measure E) (Metric.closedBall x r) ^ a *
      (μ : Measure E) (Metric.closedBall y r) ^ (1 - a) := by positivity
  simpa only [hbeq] using hpos.trans_le (hμ.closedBall_mul_le x y r a ha' ha1)
omit [BorelSpace E] in
/-- Superlevel sets of equal-radius closed-ball masses are convex. -/
theorem convex_closedBall_superlevel {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (r : ℝ) (A : ENNReal) :
    Convex ℝ {x | A ≤ (μ : Measure E) (Metric.closedBall x r)} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have ha1 : a < 1 := by have : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0); linarith
  have hbeq : b = 1 - a := by linarith
  change A ≤ _
  calc
    A = A ^ a * A ^ b := by
      rw [← ENNReal.rpow_add_of_nonneg a b ha hb, hab, ENNReal.rpow_one]
    _ ≤ (μ : Measure E) (Metric.closedBall x r) ^ a *
        (μ : Measure E) (Metric.closedBall y r) ^ b := by
      gcongr
      · exact hx
      · exact hy
    _ ≤ _ := by simpa only [hbeq] using hμ.closedBall_mul_le x y r a ha' ha1
end Transport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
end LogConcave
end KLS
end FunctionalInequalities


