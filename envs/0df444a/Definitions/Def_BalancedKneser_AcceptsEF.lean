-- Prove2me | Definitions.Def_BalancedKneser_AcceptsEF
-- name    : BalancedKneser_AcceptsEF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:48.1432+00:00
-- url     : https://prove2.me/theorems/cebb0c30-0536-4866-b2b2-9e1ef3ff34dd
-- title:
--   EFc acceptance: envy-free up to $c$ goods against the other bundle
-- statement:
--   Let $M$ be a finite set of goods and $u:2^M\to\mathbb R$ a valuation. An agent who receives the bundle $P\subseteq M$, while the other group receives $Q\subseteq M$, **accepts the allocation as EF$c$** if her envy disappears after deleting at most $c$ goods from the other bundle:
--   $$
--   u(P)\ \ge\ u(Q\setminus T)\qquad\text{for some } T\subseteq Q,\ |T|\le c .
--   $$
--   Otherwise she **rejects** it. The deleted goods $T$ may depend on the agent.
--
--   This is the acceptance test behind every balanced EF$c$ statement of the mission: Theorem 1.1 uses $c=1$ (EF1) and $c=2$ (EF2), and Theorem 2.1 treats general $c$.
--
--   **Formalization Note** A valuation is any function $\mathrm{Finset}\,M\to\mathbb R$; monotonicity and normalization $u(\emptyset)=0$ are hypotheses of the theorems that need them. The deleted set ranges over subsets of the other bundle $Q$.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §2, p.3 (PDF p.5): EFc acceptance

import Mathlib

namespace BalancedKneser

/-- **EFc acceptance** (Alipour–Jafari, *Balanced Fair Division and Generalized Kneser Graphs*,
arXiv:2611.04486v1, §2, p.3 (PDF p.5)). An agent with valuation `u` who receives the bundle `P`
accepts the allocation as EFc, with respect to the other bundle `Q`, if
`u(P) ≥ u(Q ∖ T)` for some `T ⊆ Q` with `|T| ≤ c`. Otherwise she rejects it.

Formalization Note: a valuation is any function `Finset M → ℝ`; monotonicity and normalization
are hypotheses of the theorems that use it, not part of this predicate. The deleted set `T`
ranges over subsets of the *other* bundle `Q`, as in the source. -/
def AcceptsEF {M : Type*} [DecidableEq M] (c : ℕ) (u : Finset M → ℝ) (P Q : Finset M) : Prop :=
  ∃ T ⊆ Q, T.card ≤ c ∧ u (Q \ T) ≤ u P

end BalancedKneser


