-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_decAt
-- name    : FoundationsRL_DECExamples_decAt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:43.817384+00:00
-- url     : https://prove2.me/theorems/92dcb84f-570b-48a0-bdeb-0fec4e878d97
-- title:
--   Decision-Estimation Coefficient $\mathrm{dec}_\gamma(\mathcal F,\widehat f)$ at a reference model
-- statement:
--   For a class $\mathcal F$ of functions $\Pi\to\mathbb R$, a reference model $\widehat f$ and a scale $\gamma>0$, the **Decision-Estimation Coefficient** is the value of the game
--
--   $$
--   \mathrm{dec}_\gamma(\mathcal F,\widehat f)=\min_{p\in\Delta(\Pi)}\max_{f\in\mathcal F}\mathbb E_{\pi\sim p}\Big[f(\pi_f)-f(\pi)-\gamma\cdot\big(f(\pi)-\widehat f(\pi)\big)^2\Big].
--   $$
--
--   The learner picks a distribution over decisions, an adversary picks a model in the class, and the learner pays its regret minus $\gamma$ times the information it gathers about the model. Any distribution $p$ whose payoff is at most $B$ against every $f\in\mathcal F$ certifies $\mathrm{dec}_\gamma(\mathcal F,\widehat f)\le B$.
--
--   **Formalization Note** The min and max are an infimum and a supremum, since neither need be attained, computed in the extended reals $\overline{\mathbb R}$ (`EReal`), where they have no junk value (an empty class gives $-\infty$). $\Delta(\Pi)$ is `PMF`, the distributions with countable support; on a finite decision space these are all distributions, and on an infinite one the infimum over this subset is at least the infimum over all distributions, so an upper bound on this quantity bounds the book's. The published `FoundationsRL.Structured.decGf` is not reused: it requires a finite decision space and a supplied maximizer selector $\pi_f$, and takes real `sInf`/`sSup` with junk values.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_offsetValue

namespace FoundationsRL.DECExamples

/-- The Decision-Estimation Coefficient at a reference model,
`dec_γ(F, f̂) = min_{p ∈ Δ(D)} max_{f ∈ F} E_{π∼p}[f(π_f) − f(π) − γ · (f(π) − f̂(π))²]`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, (4.15), p. 65.

**Formalization Note.** `min` and `max` are `⨅` and `⨆`, since neither need be attained, and they are
taken in `EReal`, where they have no junk value: an empty class gives `⊥` and an empty decision space
gives `⊤`. The published `FoundationsRL.Structured.decGf` is not reused: it needs `Fintype` decisions
and a supplied selector `π_f`, and the Lipschitz setting has neither. -/
noncomputable def decAt {D : Type*} (F : Set (D → ℝ)) (fhat : D → ℝ) (γ : ℝ) : EReal :=
  ⨅ p : PMF D, ⨆ f ∈ F, (offsetValue p f fhat γ : EReal)

end FoundationsRL.DECExamples


