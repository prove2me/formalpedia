-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_expect
-- name    : FoundationsRL_DECExamples_expect
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:44.595545+00:00
-- url     : https://prove2.me/theorems/539dfad1-75d9-444f-bf66-427f49d50184
-- title:
--   Expectation $\mathbb E_{\pi\sim p}[g(\pi)]$ under a distribution on decisions
-- statement:
--   Let $\Pi$ be a decision space and $p\in\Delta(\Pi)$ a probability distribution on it. For $g:\Pi\to\mathbb R$ the expectation is
--
--   $$
--   \mathbb E_{\pi\sim p}[g(\pi)]=\sum_{\pi\in\Pi}p(\pi)\,g(\pi).
--   $$
--
--   Every quantity of the Decision-Estimation Coefficient (regret of a decision, information gain, the game payoff) is an expectation of this form.
--
--   **Formalization Note** $\Delta(\Pi)$ is Mathlib's `PMF`, the probability mass functions (distributions with countable support); the decision space carries no σ-algebra, and the reference model $\widehat f$ of Proposition 18 is an arbitrary function, so integrating against a Borel measure would take Lean's junk value $0$ on a non-measurable integrand. The sum is a `tsum`, which is the junk value $0$ when not summable; every integrand in this mission is bounded, so it is summable.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.2, (4.15), p. 65

import Mathlib

namespace FoundationsRL.DECExamples

/-- The expectation `E_{π∼p}[g(π)]` of `g : D → ℝ` under a distribution `p ∈ Δ(D)`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, (4.15), p. 65.

**Formalization Note.** `Δ(D)` is `PMF D`, the distributions with countable support: `D` carries no
σ-algebra here, and the reference model `f̂` of Proposition 18 is an arbitrary function, so a Bochner
integral over Borel measures would take its junk value on a non-measurable `f̂`. The sum is a `tsum`,
which is the junk value `0` when not summable; every `g` in this mission is bounded (or `p` has
finite support), so it is summable. -/
noncomputable def expect {D : Type*} (p : PMF D) (g : D → ℝ) : ℝ :=
  ∑' π, (p π).toReal * g π

end FoundationsRL.DECExamples


