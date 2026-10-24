-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
-- name    : KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:53:39.089032+00:00
-- url     : https://prove2.me/theorems/27d213b0-6519-41d0-8f4e-de76fd4bf759
-- title:
--   Closed-ball cap of an extended-real potential
-- statement:
--   For an extended-real potential $\varphi:E\to\overline{\mathbb{R}}$ and $L\in\mathbb{R}_{\ge0}$, `closedBallCap φ L` equals $\varphi$ on the closed ball of radius $L$ centered at $0$ and equals $+\infty$ outside that ball. The surrounding results establish lower semicontinuity and bounded-domain consequences for the Legendre transform, including finiteness and Lipschitz bounds under the listed hypotheses.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean#L35-L38 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.BoundedConjugate`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
namespace FunctionalInequalities
namespace Analysis
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- Restrict an extended-real potential to the closed ball, assigning top outside. -/
noncomputable def closedBallCap (φ : E → EReal) (L : NNReal) : E → EReal := by
  classical
  exact fun x => if x ∈ closedBall (0 : E) (L : ℝ) then φ x else ⊤
end Analysis
end FunctionalInequalities


