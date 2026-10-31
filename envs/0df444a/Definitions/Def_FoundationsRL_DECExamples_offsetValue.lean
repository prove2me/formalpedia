-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_offsetValue
-- name    : FoundationsRL_DECExamples_offsetValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:46.842986+00:00
-- url     : https://prove2.me/theorems/f8545db9-ab36-42fe-8311-7d7bcea10e56
-- title:
--   Payoff of the DEC game $\mathbb E_{\pi\sim p}[f(\pi_f)-f(\pi)-\gamma(f(\pi)-\widehat f(\pi))^2]$
-- statement:
--   For a distribution $p\in\Delta(\Pi)$, a model $f:\Pi\to\mathbb R$, a reference model $\widehat f:\Pi\to\mathbb R$ and a scale $\gamma$, the payoff of the Decision-Estimation Coefficient game is
--
--   $$
--   \mathbb E_{\pi\sim p}\Big[f(\pi_f)-f(\pi)-\gamma\cdot\big(f(\pi)-\widehat f(\pi)\big)^2\Big],
--   $$
--
--   where $\pi_f$ is a decision maximizing $f$. The first part is the regret of the decision $\pi$ under the model $f$, the second part is $\gamma$ times the information the decision reveals about $f$ relative to $\widehat f$.
--
--   **Formalization Note** $f(\pi_f)$ is written $\sup_{\pi'\in\Pi}f(\pi')$, because a maximizer need not exist on a non-compact decision space; the two agree whenever $\pi_f$ exists. The real supremum is Lean's junk value $0$ for a function unbounded above; every class in this mission is bounded.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65; certification inequality, §4.3, p. 69

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_expect

namespace FoundationsRL.DECExamples

/-- The payoff of the Decision-Estimation Coefficient game,
`E_{π∼p}[f(π_f) − f(π) − γ · (f(π) − f̂(π))²]`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, (4.15), p. 65.

**Formalization Note.** `f(π_f)` is `⨆ π', f π'`, because the maximizer `π_f` need not exist on a
non-compact decision space; the two agree when it does. The real supremum is the junk value `0` when
`f` is unbounded above, and every class in this mission is bounded. -/
noncomputable def offsetValue {D : Type*} (p : PMF D) (f fhat : D → ℝ) (γ : ℝ) : ℝ :=
  expect p (fun π => (⨆ π', f π') - f π - γ * (f π - fhat π) ^ 2)

end FoundationsRL.DECExamples


