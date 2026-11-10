-- Prove2me | Definitions.Def_FreeReplExchange_feasible
-- name    : FreeReplExchange_feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:17:28.8466+00:00
-- url     : https://prove2.me/theorems/592f2760-0651-404b-880e-1fb2235efe28
-- title:
--   Utility changes (8), feasible exchanges and feasible sets (Definition 1), the efficiency benchmark (11)–(12)
-- statement:
--   For a proposal $p=((i,r),(j,s))$ and an allocation $x$, agent $k$'s utility change from executing $p$ alone is
--   $$\Delta_k(p,x)=\tilde u_k(x[\{p\}])-\tilde u_k(x),$$
--   and $p$ is **mutually beneficial** at $x$ if $\Delta_i(p,x)\ge0$ and $\Delta_j(p,x)\ge0$. The **feasible exchanges** at $x$ for $P$ are
--   $$F(x,P)=\{p=((i,r),(j,s))\text{ well formed}: x_{i,s}=x_{j,r}=0,\ p\text{ mutually beneficial at }x\},$$
--   and the **feasible sets** are
--   $$\mathcal S(x,P)=\{S\subseteq F(x,P): R(p)\cap R(q)=\varnothing\text{ for all distinct }p,q\in S\}.$$
--   The efficiency benchmark is the largest number of filled slots in the comparison class $X(x^{(0)},P)=\{x^{(0)}[S]:S\in\mathcal S(x^{(0)},P)\}$:
--   $$\max_{x\in X(x^{(0)},P)}\ \sum_{i\in A}\sum_{r=1}^m x_{i,r}.$$
--
--   These objects state stability (feasible exchanges at the terminal allocation) and efficiency (the benchmark of (12)).
--
--   **Formalization Note** The maximum is a `Finset.sup` over the finite family $\mathcal S(x^{(0)},P)$, which contains $\varnothing$, so it is attained.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), p.16 (PDF p.18), eq. (8), Definition 1, eqs. (9), (10); p.18 (PDF p.20), eqs. (11), (12)

import Mathlib
import Definitions.Def_FreeReplExchange_util
import Definitions.Def_FreeReplExchange_Exchange

namespace FreeReplExchange

/-- `∆_k(p, x) := ũ_k(x[{p}]) − ũ_k(x)` (8), Yang–Kandasamy, *Pairwise Exchanges of Freely
Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…),
p.16 (PDF p.18): the change in agent `k`'s utility when `p` is executed alone at `x`. -/
noncomputable def delta {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (U : A → A → Fin m → ℝ) (x : A → Fin m → Bool) (k : A) (p : Exchange A m) : ℝ :=
  util U k (exec x {p}) - util U k x

/-- `p = ((i, r), (j, s))` is mutually beneficial at `x` if `∆_i(p, x) ≥ 0` and `∆_j(p, x) ≥ 0`
(p.16). -/
def MutBen {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ}
    (U : A → A → Fin m → ℝ) (x : A → Fin m → Bool) (p : Exchange A m) : Prop :=
  0 ≤ delta U x p.i p ∧ 0 ≤ delta U x p.j p

open Classical in
/-- Definition 1, (9), p.16: the feasible exchanges at `x` for `P`,
`F(x, P) = {p = ((i, r), (j, s)) well formed : x_{i,s} = x_{j,r} = 0, p mutually beneficial at x}`. -/
noncomputable def feasible {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (P : Finset A) (x : A → Fin m → Bool) :
    Finset (Exchange A m) :=
  Finset.univ.filter fun p =>
    WellFormed x0 P p ∧ x p.i p.s = false ∧ x p.j p.r = false ∧ MutBen U x p

open Classical in
/-- Definition 1, (10), p.16: the feasible sets
`S(x, P) = {S ⊆ F(x, P) : R(p) ∩ R(q) = ∅ for all distinct p, q ∈ S}`. -/
noncomputable def feasibleSets {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (P : Finset A) (x : A → Fin m → Bool) :
    Finset (Finset (Exchange A m)) :=
  (feasible x0 U P x).powerset.filter RecvDisjoint

/-- The right-hand side of (12), p.18: `max_{x ∈ X(x^(0), P)} Σ_{i∈A} Σ_r x_{i,r}`, where (11)
`X(x^(0), P) = {x^(0)[S] : S ∈ S(x^(0), P)}`.

**Formalization Note.** The maximum is the `Finset.sup` over the feasible sets at the initial
allocation; this family always contains `∅`, so it is nonempty and the supremum is attained. -/
noncomputable def maxFilled {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (P : Finset A) : ℕ :=
  (feasibleSets x0 U P x0).sup fun S => filledCount (exec x0 S)

end FreeReplExchange


