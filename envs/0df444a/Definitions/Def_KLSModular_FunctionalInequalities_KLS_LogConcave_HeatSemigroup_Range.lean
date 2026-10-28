-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:26:24.965999+00:00
-- url     : https://prove2.me/theorems/a24adaa9-3bf7-4b4a-8f86-f94e3c7a1ac4
-- title:
--   Compactly supported smooth diffusion images
-- statement:
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, let $ν$ be a probability measure on $V$, and let $U : V \to \mathbb{R}$ be $C^1$. `compactSmoothDiffusionImage hU` is the subset of $L^2(ν)$ consisting of the `toLp` representatives of $-L f$, where $f : V \to \mathbb{R}$ is smooth of class $C^\infty$ and compactly supported and $L$ is the weighted Laplacian determined by $U$. The module supplies auxiliary range-density infrastructure for these images; the definition itself imposes no centering or operator-domain condition on an arbitrary $L^2$ element.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator
--   import FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel
--   import FunctionalInequalities.Analysis.Semigroup.Generated.Convergence
--   import FunctionalInequalities.L2.MeanVariance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def compactSmoothDiffusionImage {ν : ProbabilityMeasure V} {U : V → ℝ}
--       (hU : ContDiff ℝ 1 U) : Set (Lp ℝ 2 (ν : Measure V)) :=
--     {w | ∃ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f),
--       w = (memLp_neg_weightedLaplacian (ν := ν) hU hf hc).toLp
--         (fun x => -weightedLaplacian U f x)}
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/HeatSemigroup/InteriorRegularity`](https://prove2.me/theorems/79e586aa-54d4-4c9a-ac32-31116ce1ca0f), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22), [`Analysis/Semigroup/Generated/Convergence`](https://prove2.me/theorems/bf431053-eab1-4154-9189-5a728fdc5db2), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   Theorems in source order:
--
--   - [`centered_mem_closure_compactSmoothDiffusionImage`](https://prove2.me/theorems/cc2ca884-a315-433e-8321-8e49b01e29b4)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Range.lean) · `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Range` · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), item LA6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Range.lean#L37-L42 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Range`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Range`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Generator
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Convergence
import Definitions.Def_KLSModular_FunctionalInequalities_L2_MeanVariance

noncomputable section
open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.L2
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace LinearPMap
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace HeatSemigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
/-- The literal compactly supported smooth diffusion images used in the range-density statement. -/
def compactSmoothDiffusionImage {ν : ProbabilityMeasure V} {U : V → ℝ}
    (hU : ContDiff ℝ 1 U) : Set (Lp ℝ 2 (ν : Measure V)) :=
  {w | ∃ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f),
    w = (memLp_neg_weightedLaplacian (ν := ν) hU hf hc).toLp
      (fun x => -weightedLaplacian U f x)}
end HeatSemigroup
end LogConcave
end KLS
end FunctionalInequalities


