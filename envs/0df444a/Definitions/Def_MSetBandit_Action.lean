-- Prove2me | Definitions.Def_MSetBandit_Action
-- name    : MSetBandit_Action
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:37:58.088116+00:00
-- url     : https://prove2.me/theorems/d0f7f3c7-0f96-4631-acce-e9407d6c714f
-- title:
--   The action set $\mathcal X_{d,m}$ of $m$-sets
-- statement:
--   Fix integers $d$ and $m$. The **action set** is
--   $$
--   \mathcal X=\mathcal X_{d,m}=\{x\in\{0,1\}^d:\ \|x\|_1=m\},\qquad K=|\mathcal X|=\binom dm .
--   $$
--   Each action selects exactly $m$ of the $d$ items, and actions are identified with the $m$-element subsets $S\subseteq[d]$ (the $m$-sets) through the indicator vector $\mathbf 1_S$.
--
--   This is the decision set of the adversarial $m$-set bandit problem.
--
--   **Formalization Note** An action is an $m$-element subset of the item set $\{0,\dots,d-1\}$ (items are indexed from $0$). The type is finite with $\binom dm$ elements and carries the discrete $\sigma$-algebra. The standing assumptions $d\ge2$, $1\le m\le d-1$ are hypotheses of each theorem.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, Eq. (1), p.3

import Mathlib

namespace MSetBandit

/-- **The action set `X = X_{d,m}`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, Eq. (1), p.3:
`X := {x ∈ {0,1}^d : ‖x‖₁ = m}`, `K := |X| = C(d, m)`. "Each m-set `S ⊆ [d]` corresponds to the
indicator vector `1_S ∈ X`. We therefore use actions in `X` and m-sets interchangeably."

`Action d m` is the type of `m`-element subsets of the item set `Fin d`; the indicator vector of an
action is `MSetBandit.ind`.

**Formalization Note.** Items are indexed by `Fin d` (0-based) instead of `[d] = {1, …, d}`. The
type is finite (`Fintype.card (Action d m) = Nat.choose d m`) and carries Mathlib's discrete
σ-algebra (every subset measurable), inherited from `Finset (Fin d)`. The standing assumptions
`d ≥ 2`, `1 ≤ m ≤ d − 1` are hypotheses of each theorem, not part of the type. -/
abbrev Action (d m : ℕ) : Type := {S : Finset (Fin d) // S.card = m}

end MSetBandit


