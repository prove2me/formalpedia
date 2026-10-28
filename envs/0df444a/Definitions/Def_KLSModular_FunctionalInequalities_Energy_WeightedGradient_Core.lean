-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Core
-- name    : KLSModular_FunctionalInequalities_Energy_WeightedGradient_Core
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:29:35.068338+00:00
-- url     : https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f
-- title:
--   Smooth core for the weighted gradient operator
-- statement:
--   `WeightedGradient.smoothCore ν` is the submodule of real L²(ν) consisting of classes represented by globally smooth compactly supported functions. Such functions are globally Lipschitz, have compactly supported weighted gradients, and are weighted-gradient tests; `dense_smoothCore` states that this submodule is dense in L²(ν). Under absolute continuity with respect to a Haar measure, the smooth core lies in the operator domain and the domain is dense. If the weighted gradient operator is closable and its support frontier is ν-null, `exists_smoothCore_tendsto` and `closure_domRestrict_smoothCore` state that restriction to the smooth core has the same closure; the same holds for any intermediate submodule between the smooth core and the full domain.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Approximation
--   import FunctionalInequalities.Energy.WeightedGradient.Basic
--   import FunctionalInequalities.Energy.Euclidean.WeakDerivative
--   import FunctionalInequalities.L2.MeanVariance
--   import Mathlib.Analysis.Calculus.MeanValue
--   import Mathlib.Analysis.Normed.Lp.SmoothApprox
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   def smoothCore : Submodule ℝ (Lp ℝ 2 (ν : Measure V))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Euclidean/LipschitzApproximation/Approximation`](https://prove2.me/theorems/f8e5c4c5-238b-4e84-9e52-3dadb9d28961), [`Energy/WeightedGradient/Basic`](https://prove2.me/theorems/f6b93e94-4e8d-4cc9-94ea-458e2669b85c), [`Energy/Euclidean/WeakDerivative`](https://prove2.me/theorems/c4b37c13-923e-4442-bcbf-73e18432fd7e), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/WeightedGradient/Core.lean) · `FunctionalInequalities.Energy.WeightedGradient.Core` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/WeightedGradient/Core.lean#L46-L225 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.WeightedGradient.Core`, definition bundle `KLSModular_FunctionalInequalities_Energy_WeightedGradient_Core`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Approximation
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_WeakDerivative
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Lp.SmoothApprox

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ContDiff
namespace FunctionalInequalities
namespace Energy
namespace WeightedGradient
open Energy.Euclidean
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : ProbabilityMeasure V) (B : V →L[ℝ] V)
omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
omit [CompleteSpace V] in
/-- A smooth compactly supported function is globally Lipschitz. -/
theorem lipschitzWith_of_contDiff_hasCompactSupport {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) : ∃ K : NNReal, LipschitzWith K g := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_of_hasCompactSupport (hg.of_le (mod_cast le_top)) hs
  refine ⟨⟨M, hM0⟩, lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) fun x ↦ ?_⟩
  change ‖fderiv ℝ g x‖ ≤ M
  exact hM x
omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The weighted gradient of a smooth compactly supported function has compact support. -/
theorem hasCompactSupport_apply {g : V → ℝ} (hs : HasCompactSupport g) :
    HasCompactSupport (apply B g) := by
  have h1 : HasCompactSupport (gradient g) := by
    change HasCompactSupport ((toDual ℝ V).symm ∘ fderiv ℝ g)
    exact (hs.fderiv ℝ).comp_left (map_zero _)
  exact h1.comp_left (map_zero B)
omit [FiniteDimensional ℝ V] in
/-- Smooth compactly supported functions are weighted gradient tests for every law. -/
theorem IsTest.of_contDiff_hasCompactSupport {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) : IsTest ν B g := by
  refine ⟨lipschitzWith_of_contDiff_hasCompactSupport hg hs, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hs
    exact MemLp.of_bound hg.continuous.aestronglyMeasurable C (ae_of_all _ hC)
  · have hcont : Continuous (apply B g) :=
      B.continuous.comp (continuous_gradient_of_contDiff hg (by simp))
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hasCompactSupport_apply B hs)
    exact MemLp.of_bound hcont.aestronglyMeasurable C (ae_of_all _ hC)
omit [FiniteDimensional ℝ V] in
/-- Smooth compactly supported functions are square integrable for every probability law. -/
theorem memLp_of_contDiff_hasCompactSupport {g : V → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) : MemLp g 2 (ν : Measure V) :=
  (IsTest.of_contDiff_hasCompactSupport ν 0 hg hs).memLp
/-- The smooth core: classes of smooth compactly supported functions in `L²(ν)`. -/
def smoothCore : Submodule ℝ (Lp ℝ 2 (ν : Measure V)) where
  carrier := {f | ∃ (g : V → ℝ) (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g),
    f = (memLp_of_contDiff_hasCompactSupport ν hg hs).toLp g}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    exact (MemLp.toLp_zero _).symm
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, hs₁, rfl⟩ ⟨g₂, hg₂, hs₂, rfl⟩
    refine ⟨g₁ + g₂, hg₁.add hg₂, hs₁.add hs₂, ?_⟩
    exact (MemLp.toLp_add _ _).symm
  smul_mem' := by
    rintro c f ⟨g, hg, hs, hf⟩
    have hcs : HasCompactSupport (c • g) := by
      have heq : c • g = (fun _ ↦ c) * g := by
        funext x
        simp [smul_eq_mul]
      rw [heq]
      exact hs.mul_left
    refine ⟨c • g, hg.const_smul c, hcs, ?_⟩
    rw [hf]
    exact (MemLp.toLp_const_smul c _).symm
/-- The smooth core is dense in `L²(ν)`. -/
theorem dense_smoothCore : Dense (smoothCore ν : Set (Lp ℝ 2 (ν : Measure V))) := by
  refine (Lp.dense_hasCompactSupport_contDiff (μ := (ν : Measure V)) (F := ℝ) (p := 2)
    (by simp)).mono ?_
  rintro f ⟨g, hfg, hs, hg⟩
  refine ⟨g, hg, hs, ?_⟩
  apply Lp.ext
  exact hfg.trans (memLp_of_contDiff_hasCompactSupport ν hg hs).coeFn_toLp.symm
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The `L²` constant one is the class of the constant test one. -/
theorem L2_const_eq_toLp (c : ℝ) :
    L2.const ν c = (memLp_const c : MemLp (fun _ : V ↦ c) 2 (ν : Measure V)).toLp _ := by
  apply Lp.ext
  exact (L2.const_coeFn ν c).trans (MemLp.coeFn_toLp _).symm
variable {m : Measure V} [m.IsAddHaarMeasure]
/-- The smooth core lies in the domain of the weighted gradient operator. -/
theorem smoothCore_le_domain_operator (hac : (ν : Measure V) ≪ m) :
    smoothCore ν ≤ (operator ν B hac).domain := by
  rintro f ⟨g, hg, hs, rfl⟩
  exact (mem_domain_operator_iff ν B hac _).mpr
    ⟨g, IsTest.of_contDiff_hasCompactSupport ν B hg hs, rfl⟩
/-- The weighted gradient operator is densely defined. -/
theorem dense_domain_operator (hac : (ν : Measure V) ≪ m) :
    Dense ((operator ν B hac).domain : Set (Lp ℝ 2 (ν : Measure V))) :=
  (dense_smoothCore ν).mono (smoothCore_le_domain_operator ν B hac)
/-- Every test is a graph-norm limit of smooth compactly supported functions: the certified
weighted approximation theorem in operator form. -/
theorem exists_smoothCore_tendsto (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (f : (operator ν B hac).domain) :
    ∃ s : ℕ → smoothCore ν,
      Tendsto (fun n ↦ ((s n : Lp ℝ 2 (ν : Measure V)),
        operator ν B hac ⟨s n, smoothCore_le_domain_operator ν B hac (s n).2⟩))
        atTop (𝓝 ((f : Lp ℝ 2 (ν : Measure V)), operator ν B hac f)) := by
  obtain ⟨g, h, hfg⟩ := (mem_domain_operator_iff ν B hac _).mp f.2
  obtain ⟨K, hK⟩ := h.1
  obtain ⟨gSeq, hprop, hconv, hconvB⟩ := LipschitzApproximation.exists_smooth_weighted_L2
    ν m hac B g hK.locallyLipschitz h.memLp h.memLp_apply
  have hmem : ∀ n, (memLp_of_contDiff_hasCompactSupport ν (hprop n).1 (hprop n).2.1).toLp (gSeq n) ∈
      smoothCore ν := fun n ↦ ⟨gSeq n, (hprop n).1, (hprop n).2.1, rfl⟩
  refine ⟨fun n ↦ ⟨_, hmem n⟩, ?_⟩
  have htest : ∀ n, IsTest ν B (gSeq n) := fun n ↦
    IsTest.of_contDiff_hasCompactSupport ν B (hprop n).1 (hprop n).2.1
  have hT : ∀ n, operator ν B hac
      ⟨(memLp_of_contDiff_hasCompactSupport ν (hprop n).1 (hprop n).2.1).toLp (gSeq n),
        smoothCore_le_domain_operator ν B hac (hmem n)⟩ =
      (htest n).memLp_apply.toLp (apply B (gSeq n)) := fun n ↦
    operator_apply ν B hac hfr (htest n) _ rfl
  have hTf : operator ν B hac f = h.memLp_apply.toLp (apply B g) :=
    operator_apply ν B hac hfr h f.2 hfg
  refine Tendsto.prodMk_nhds ?_ ?_
  · rw [hfg, tendsto_iff_norm_sub_tendsto_zero]
    have h1 : ∀ n, ‖(memLp_of_contDiff_hasCompactSupport ν (hprop n).1 (hprop n).2.1).toLp (gSeq n) -
        h.memLp.toLp g‖ = (eLpNorm (fun x ↦ gSeq n x - g x) 2 (ν : Measure V)).toReal := by
      intro n
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
      rfl
    simp_rw [h1]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv
    simpa [Function.comp_def] using this
  · simp only [hT, hTf]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : ∀ n, ‖(htest n).memLp_apply.toLp (apply B (gSeq n)) -
        h.memLp_apply.toLp (apply B g)‖ =
        (eLpNorm (fun x ↦ B (gradient (gSeq n) x) - B (gradient g x)) 2 (ν : Measure V)).toReal := by
      intro n
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
      rfl
    simp_rw [h1]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvB
    simpa [Function.comp_def] using this
/-- For a closable weighted gradient operator, restricting to the smooth core does not change
the closure. -/
theorem closure_domRestrict_smoothCore (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hT : (operator ν B hac).IsClosable) :
    ((operator ν B hac).domRestrict (smoothCore ν)).closure =
      (operator ν B hac).closure :=
  Energy.IsClosable.closure_domRestrict_eq hT (smoothCore_le_domain_operator ν B hac)
    (exists_smoothCore_tendsto ν B hac hfr)
/-- Every core between the smooth core and the full domain, such as `ℝ + C_c^∞`, has the same
closure. -/
theorem closure_domRestrict_eq_of_smoothCore_le (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hT : (operator ν B hac).IsClosable) {S : Submodule ℝ (Lp ℝ 2 (ν : Measure V))}
    (hS : smoothCore ν ≤ S) (hS' : S ≤ (operator ν B hac).domain) :
    ((operator ν B hac).domRestrict S).closure = (operator ν B hac).closure :=
  Energy.IsClosable.closure_domRestrict_eq_of_le hT hS hS'
    (closure_domRestrict_smoothCore ν B hac hfr hT)
end WeightedGradient
end Energy
end FunctionalInequalities


