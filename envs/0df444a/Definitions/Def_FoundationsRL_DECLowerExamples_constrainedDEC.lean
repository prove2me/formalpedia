-- Prove2me | Definitions.Def_FoundationsRL_DECLowerExamples_constrainedDEC
-- name    : FoundationsRL_DECLowerExamples_constrainedDEC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:22:16.401271+00:00
-- url     : https://prove2.me/theorems/64fe41d9-bd78-4bb3-8160-fe0b0b0256ec
-- title:
--   Constrained DEC of a class $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M)=\sup_{\widehat M\in\mathrm{co}(\mathcal M)}\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M\cup\{\widehat M\},\widehat M)$
-- statement:
--   For a class $\mathcal M$ of models and a radius $\varepsilon>0$, the **constrained Decision-Estimation Coefficient** of the class is
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M):=\sup_{\widehat M\in\mathrm{co}(\mathcal M)}\mathrm{dec}^{\mathrm c}_\varepsilon\bigl(\mathcal M\cup\{\widehat M\},\widehat M\bigr),
--   $$
--   where $\mathrm{co}(\mathcal M)$ is the convex hull of the class (finite mixtures of its models, decision by decision).
--
--   It is the complexity measure of the regret lower bound of Proposition 28.
--
--   **Formalization Note** The convex hull is the published `FoundationsRL.DECLower.kernelHull`; the inner coefficient is this mission's $[0,\infty]$-valued one, so no reward range is assumed.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.5.1, p. 104

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_kernelHull
import Definitions.Def_FoundationsRL_DECLowerExamples_constrainedDECRef

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FoundationsRL.DECLowerExamples

/-- **Constrained Decision-Estimation Coefficient of a class, values in `[0, ∞]`**
`dec^c_ε(M) := sup_{M̂ ∈ co(M)} dec^c_ε(M ∪ {M̂}, M̂)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.5.1, p. 104.

**Formalization Note.** `co(M)` is the published `FoundationsRL.DECLower.kernelHull` (finite
mixtures, decision by decision), and `insert Mhat Ms` is `M ∪ {M̂}`. The inner coefficient is the
`[0, ∞]`-valued `constrainedDECRef` of this mission, so no reward range is assumed. -/
noncomputable def constrainedDEC {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (ε : ℝ) (Ms : Set (Kernel D (ℝ × O))) : ℝ≥0∞ :=
  ⨆ Mhat ∈ FoundationsRL.DECLower.kernelHull Ms, constrainedDECRef ε (insert Mhat Ms) Mhat

end FoundationsRL.DECLowerExamples


