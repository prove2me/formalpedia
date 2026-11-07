-- Prove2me | Definitions.Def_SingleOrSample_IsSafe
-- name    : SingleOrSample_IsSafe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:19.903498+00:00
-- url     : https://prove2.me/theorems/bd8f4a83-2708-4482-b88a-9576fc9081cc
-- title:
--   The safe strategy $S_i$ at target $\tau$
-- statement:
--   The **marginal value** of a good $e$ given a set $A$ is $v(e\mid A)=v(A\cup\{e\})-v(A)$.
--
--   A strategy follows the **safe strategy** for the valuation $v$ at target $\tau>0$ if at every history with $t<n$ and remaining set $R$:
--
--   1. if $R$ has a good $e$ with $v(e)\ge\tau$, the agent takes a special round selecting a good of $R$ of maximum value;
--   2. otherwise the agent samples, and whenever $|G|\ge k(n-t)$ the next bucket consists of $k(n-t)$ goods of $G$ with the largest marginal values given the goods $A$ picked so far in the round:
--   $$v(y\mid A)\le v(x\mid A)\qquad\text{for all } x\in B,\ y\in G\setminus B.$$
--
--   Theorem 4.1 is a guarantee for every strategy of this form.
--
--   **Formalization Note** This is a predicate on strategies, so all tie-breaking rules are allowed, including history-dependent ones. The target $\tau$ is on the scale of $v$, and $v$ is not normalized. For $\tau\le0$ the predicate imposes nothing: this covers an agent with $\mathrm{MMS}=0$, who "can be simply ignored" (footnote 3, p.30).
-- source:
--   Chawla, Huang, Kulkarni, Mehta, Shahkar, Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission, arXiv:2609.32286 (manuscript sha256 28cd3d7b…), Definition 7, p.13

import Mathlib
import Definitions.Def_SingleOrSample_Hist
import Definitions.Def_SingleOrSample_Strategy

namespace SingleOrSample

/-- The marginal value `v(e | A) = v(A ∪ {e}) − v(A)` (Chawla, Huang, Kulkarni, Mehta, Shahkar,
Single-or-Sample: Online Fair Allocation for Combinatorial Agents, STOC 2027 submission,
arXiv:2609.32286, manuscript sha256 28cd3d7b…, Definition 7, p.13). -/
def marginal {m : ℕ} (v : Finset (Fin m) → ℝ) (A : Finset (Fin m)) (e : Fin m) : ℝ :=
  v (A ∪ {e}) - v A

/-- `σ` follows the **safe strategy** `S_i` for the valuation `v` at target `τ` (Definition 7, p.13): for
every history with `t < n` and `R` its remaining set,
1. if `R` has an item of value at least `τ`, the agent takes a special round selecting an item of `R` of
   maximum value;
2. otherwise the agent samples, and whenever `|G| ≥ k(n − t)` the next bucket consists of `k(n − t)` items
   of `G` with the largest marginal values given the items picked so far: every item of the bucket has
   marginal value at least that of every item of `G` outside it.

**Formalization Note.** This is a predicate, so every tie-breaking is allowed, also a history-dependent
one (the page's `argmax` and "largest" leave ties open). `τ` is on the scale of `v`, which is not
normalized: in the goal it is `(1/24)·MMS v`. The guard `0 < τ` leaves an agent unconstrained when
`τ ≤ 0`; this covers `MMS = 0`, the agent of footnote 3, p.30, who "can be simply ignored". -/
def IsSafe {m : ℕ} (n k : ℕ) (τ : ℝ) (v : Finset (Fin m) → ℝ) (σ : Strategy m) : Prop :=
  0 < τ → ∀ h : Hist m, specialCount h < n →
    ((∃ e ∈ remaining h, τ ≤ v {e}) →
      ∃ e ∈ remaining h, σ.choose h = some e ∧ ∀ g ∈ remaining h, v {g} ≤ v {e}) ∧
    ((∀ e ∈ remaining h, v {e} < τ) →
      σ.choose h = none ∧
      ∀ picks : List (Finset (Fin m) × Fin m),
        k * (n - specialCount h) ≤ (pending h picks).card →
          σ.bucket h picks ⊆ pending h picks ∧
          (σ.bucket h picks).card = k * (n - specialCount h) ∧
          ∀ x ∈ σ.bucket h picks, ∀ y ∈ pending h picks \ σ.bucket h picks,
            marginal v (items picks) y ≤ marginal v (items picks) x)

end SingleOrSample


