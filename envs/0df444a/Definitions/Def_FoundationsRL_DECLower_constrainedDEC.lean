-- Prove2me | Definitions.Def_FoundationsRL_DECLower_constrainedDEC
-- name    : FoundationsRL_DECLower_constrainedDEC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:13:51.815106+00:00
-- url     : https://prove2.me/theorems/b5fd99a4-0b97-4d53-bc3b-e52927a05fe9
-- title:
--   Constrained DEC $\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M)=\sup_{\widehat M\in\mathrm{co}(\mathcal M)}\mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M\cup\{\widehat M\},\widehat M)$
-- statement:
--   For a class $\mathcal M$ of models and $\varepsilon>0$, the **constrained Decision-Estimation Coefficient** of the class is
--
--   $$
--   \mathrm{dec}^{\mathrm c}_\varepsilon(\mathcal M):=\sup_{\widehat M\in\mathrm{co}(\mathcal M)}\mathrm{dec}^{\mathrm c}_\varepsilon\bigl(\mathcal M\cup\{\widehat M\},\widehat M\bigr).
--   $$
--
--   The reference model ranges over the convex hull of the class and is added to the class it is compared against.
--
--   It is the complexity measure in Proposition 28: the minimax regret is at least of order $\mathrm{dec}^{\mathrm c}_{\varepsilon_T}(\mathcal M)\cdot T$ for $\varepsilon_T\propto 1/\sqrt T$.
--
--   **Formalization Note** For a class of models all values lie in $[0,1]$, so the real supremum is the true supremum; for an empty class it is $0$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §6.5.1, p. 104

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_constrainedDECRef
import Definitions.Def_FoundationsRL_DECLower_kernelHull

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.DECLower

/-- **Constrained Decision-Estimation Coefficient** `dec^c_ε(M) := sup_{M̂∈co(M)} dec^c_ε(M ∪ {M̂}, M̂)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, §6.5.1, p. 104.

**Formalization Note.** The reference model `M̂` ranges over the convex hull `kernelHull Ms`
(finite mixtures) and is itself added to the class it is compared against
(`insert Mhat Ms` is `M ∪ {M̂}`). For a class of models all values lie in `[0, 1]`, so the real
`sSup` is the true supremum; for an empty class it is `0`. -/
noncomputable def constrainedDEC {D O : Type*} [MeasurableSpace D] [MeasurableSpace O]
    (ε : ℝ) (Ms : Set (Kernel D (ℝ × O))) : ℝ :=
  sSup ((fun Mhat => constrainedDECRef ε (insert Mhat Ms) Mhat) '' kernelHull Ms)

end FoundationsRL.DECLower


