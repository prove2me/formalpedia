-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_Exponent
-- name    : KLSModular_FunctionalInequalities_Probability_Posterior_Exponent
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:15:49.768242+00:00
-- url     : https://prove2.me/theorems/36c30d18-f69a-4499-bf5e-0d0678b5706c
-- title:
--   Linear–quadratic posterior exponent
-- statement:
--   For a real inner-product space $E$, a vector $c\in E$, a continuous linear map $Q:E\to E$, and $x\in E$, `quadraticExponent c Q x` is the real-valued expression $\langle c,x\rangle-\frac12\langle Qx,x\rangle$. This is the linear–quadratic exponent used to define the posterior tilt; no measure or integrability assertion is included.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.InnerProductSpace.Basic
--   import Mathlib.Analysis.InnerProductSpace.Continuous
--   import Mathlib.MeasureTheory.Measure.Tilted
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   import Mathlib.MeasureTheory.Integral.Bochner.Basic
--   import Mathlib.Analysis.Convex.Function
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def quadraticExponent (c : E) (Q : E →L[ℝ] E) (x : E) : ℝ :=
--     ⟪c, x⟫ - (1 / 2 : ℝ) * ⟪Q x, x⟫
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`quadraticExponent_concave`](https://prove2.me/theorems/c00cf1d3-34cb-42b3-91ca-1ba2574014a2)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Posterior/Exponent.lean) · `FunctionalInequalities.Probability.Posterior.Exponent` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E67. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Posterior/Exponent.lean#L26-L28 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Posterior.Exponent`, definition bundle `KLSModular_FunctionalInequalities_Probability_Posterior_Exponent`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.Function

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Probability
namespace Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The exponent `⟪c, x⟫ − ½⟪Q x, x⟫` of the BKL posterior (67) with parameters `(c, Q)`. -/
def quadraticExponent (c : E) (Q : E →L[ℝ] E) (x : E) : ℝ :=
  ⟪c, x⟫ - (1 / 2 : ℝ) * ⟪Q x, x⟫
end Posterior
end Probability
end FunctionalInequalities


