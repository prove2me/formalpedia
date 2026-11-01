-- Prove2me | Definitions.Def_SambaPG_IsLeaderRule
-- name    : SambaPG_IsLeaderRule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:37:02.844737+00:00
-- url     : https://prove2.me/theorems/d7696841-db0c-49b6-af1f-cec8a7efb5db
-- title:
--   Choosing a leading arm of maximal probability
-- statement:
--   A **leader rule** is a map $(p,v)\mapsto \mathrm{lead}(p,v)\in\mathcal A$ such that the sets $\{(p,v):\mathrm{lead}(p,v)=a\}$ are measurable and $\mathrm{lead}(p,v)$ always maximizes $p$:
--
--   $$
--   p_a\le p_{\mathrm{lead}(p,v)}\qquad\text{for all arms }a .
--   $$
--
--   Fed with a uniform variable $v$, it chooses the leading arm $a_\star(t)=\operatorname{argmax}_a p_a(t)$ of SAMBA, breaking ties at random.
--
--   **Formalization Note** The paper does not specify the distribution of the random choice among maximizers, so every measurable maximizer rule is allowed; the uniform choice among maximizers is one instance.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, §3.4, p.7

import Mathlib

namespace SambaPG

/-- **Choosing the leading arm.**
Denisov & Walton, arXiv:2007.10229v3, §3.4, p.7: "`a⋆(t) = argmax_{a∈A} p_a(t)` … If the maximum
is not unique we select `a⋆(t)` at random amongst the set of maximizing arms."

`lead p v` is the leading arm when the probability vector is `p` and the tie-breaking
randomization is `v`. It is jointly measurable and always returns an arm of maximal probability.

**Formalization Note.** The paper does not fix the distribution of the random choice among
maximizers. Every measurable maximizer rule fed by an independent uniform `v` is allowed; the
uniform choice among maximizers is one instance. -/
def IsLeaderRule {A : Type*} (lead : (A → ℝ) → ℝ → A) : Prop :=
  (∀ a, MeasurableSet {x : (A → ℝ) × ℝ | lead x.1 x.2 = a}) ∧
    ∀ (p : A → ℝ) (v : ℝ) (a : A), p a ≤ p (lead p v)

end SambaPG


