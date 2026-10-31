-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_decGame
-- name    : FoundationsRL_E2DStructured_decGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:23:20.787721+00:00
-- url     : https://prove2.me/theorems/801789d7-4ee8-45e7-bb40-34a98fc60742
-- title:
--   The inner value of the DEC game at a distribution $p$
-- statement:
--   For a class $\mathcal F$, a reference model $\hat f$ and $p\in\Delta(\Pi)$, the inner value of the game is
--   $$\sup_{f\in\mathcal F}\mathbb E_{\pi\sim p}\big[f(\pi_f)-f(\pi)-\gamma\,(f(\pi)-\hat f(\pi))^2\big].$$
--   A distribution $p$ **certifies** an upper bound on the DEC exactly when this quantity is at most that bound.
--
--   **Formalization Note** The supremum is taken in the extended reals; it is $-\infty$ for empty $\mathcal F$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65; §4.3, p. 69

import Mathlib
import Definitions.Def_FoundationsRL_E2DStructured_decObjective

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The inner value `sup_{f∈F} E_{π∼p}[f(π_f) − f(π) − γ·(f(π) − f̂(π))²]` of the DEC game at a
decision distribution `p` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.2, p. 65, (4.15); p. 69, "certifies").

**Formalization Note.** `max` is read `sup`, as in (4.19). The supremum is in `EReal`, which is a
complete lattice, so it needs no boundedness; it is `⊥` when `F` is empty. -/
noncomputable def decGame {D : Type*} [MeasurableSpace D] (γ : ℝ) (F : Set (D → ℝ))
    (fhat : D → ℝ) (p : ProbabilityMeasure D) : EReal :=
  ⨆ f ∈ F, decObjective γ f fhat p

end FoundationsRL.E2DStructured


