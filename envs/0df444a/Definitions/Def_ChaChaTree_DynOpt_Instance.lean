-- Prove2me | Definitions.Def_ChaChaTree_DynOpt_Instance
-- name    : ChaChaTree_DynOpt_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:20:59.300404+00:00
-- url     : https://prove2.me/theorems/85e474a3-ccf4-4bf9-9b3b-d4ee22ae1fc7
-- title:
--   Instances, next/previous points, switches, turns and time reverse (§4.1)
-- statement:
--   An **instance** on $[N] \times [T]$ is a finite set $P$ of points $(x,t)$ with $x \in [N]$, $t \in [T]$, and at most one point at any time (`IsInstance N T P`). For a point $p$, $p.x$ is its key (`p.1`) and $p.y$ its time (`p.2`). The instance of an access sequence is $P(X) = \{(x_t, t) \mid t \in [m]\}$ (`pointsOf X`).
--
--   * $\mathrm{nxt}_P(p)$: the point of $P$ of minimum time $> p.y$; $\mathrm{nd}_P(p)$: the point with key $\neq p.x$ of minimum time $> p.y$ (the **next different** point); $\mathrm{pre}(p)$, $\mathrm{pd}(p)$: the previous and previous different points. Each is a relation (`IsNxt`, `IsNd`, `IsPre`, `IsPd`); $\bot$ ("no such point") is the absence of a witness.
--   * $p$ is a **switch** if $\mathrm{pre}(p) \neq \bot$ and $\mathrm{pre}(p).x \neq p.x$; $\mathrm{switches}(P)$ counts them.
--   * $(p,q)$ with $p.y < q.y$ is **left** if $q.x < p.x$ and **right** if $q.x > p.x$; $(p,q,u)$ with $p.y<q.y<u.y$ is a **turn** if $(p,q)$ is left and $(q,u)$ right or vice versa.
--   * $p$ **completes a turn** if $p' = \mathrm{pre}(p)$ and $p'' = \mathrm{pd}(p')$ exist and $(p'', p', p)$ is a turn; $\mathrm{turns}(P)$ counts these points.
--   * The **time reverse** is $P^R = \{(x, T+1-t) \mid (x,t) \in P\}$ (`timeReverse T P`).
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), §4.1, p. 11 (PDF 12)

import Mathlib

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-! # Instances (§4.1): point sets, next/previous points, switches, turns, time reverse

Čech et al., *Dynamic Optimality to within O(log log log n)*, STOC 2027 submission (manuscript,
sha256 9316fbfd…), §4.1, p. 11 (PDF 12).

A point is `p : ℕ × ℕ` with key `p.1` (the paper's `p.x`) and time `p.2` (`p.y`). The paper's `⊥`
("no such point") is the absence of a witness: `nxt`, `nd`, `pre`, `pd` are relations
`IsNxt P p q` ("`q = nxt(p)`"), which hold for at most one `q` because times are distinct. -/

/-- An **instance** on `[N] × [T]`: a finite set of points `(x, t)` with `x ∈ [N]`, `t ∈ [T]`,
and at most one point at any given time. -/
def IsInstance (N T : ℕ) (P : Finset (ℕ × ℕ)) : Prop :=
  P ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 T ∧ ∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → p = q

/-- The instance of an access sequence `X = (x₁, …, x_m)`: `P(X) = {(x_t, t) | t ∈ [m]}`
(times are one-based). -/
def pointsOf (X : List ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range X.length).image fun t => (X.getD t 0, t + 1)

/-- `q = nxt_P(p)`: the point of `P` of minimum time `> p.y`. -/
abbrev IsNxt (P : Finset (ℕ × ℕ)) (p q : ℕ × ℕ) : Prop :=
  q ∈ P ∧ p.2 < q.2 ∧ ∀ r ∈ P, p.2 < r.2 → q.2 ≤ r.2

/-- `q = nd_P(p)`: the next *different* point, the point of `P` with key `≠ p.x` of minimum
time `> p.y`. -/
abbrev IsNd (P : Finset (ℕ × ℕ)) (p q : ℕ × ℕ) : Prop :=
  q ∈ P ∧ p.2 < q.2 ∧ q.1 ≠ p.1 ∧ ∀ r ∈ P, p.2 < r.2 → r.1 ≠ p.1 → q.2 ≤ r.2

/-- `q = pre_P(p)`: the point of `P` of maximum time `< p.y`. -/
abbrev IsPre (P : Finset (ℕ × ℕ)) (q p : ℕ × ℕ) : Prop :=
  q ∈ P ∧ q.2 < p.2 ∧ ∀ r ∈ P, r.2 < p.2 → r.2 ≤ q.2

/-- `q = pd_P(p)`: the previous *different* point, the point of `P` with key `≠ p.x` of maximum
time `< p.y`. -/
abbrev IsPd (P : Finset (ℕ × ℕ)) (q p : ℕ × ℕ) : Prop :=
  q ∈ P ∧ q.2 < p.2 ∧ q.1 ≠ p.1 ∧ ∀ r ∈ P, r.2 < p.2 → r.1 ≠ p.1 → r.2 ≤ q.2

/-- `p` is a **switch** in `P`: `pre(p) ≠ ⊥` and `pre(p).x ≠ p.x`. -/
abbrev IsSwitch (P : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : Prop :=
  ∃ q ∈ P, IsPre P q p ∧ q.1 ≠ p.1

/-- `switches(P)`: the number of switches of `P`. -/
def switches (P : Finset (ℕ × ℕ)) : ℕ :=
  (P.filter fun p => IsSwitch P p).card

/-- The pair `(p, q)` is **left**: `p.y < q.y` and `q.x < p.x`. -/
abbrev IsLeftPair (p q : ℕ × ℕ) : Prop := p.2 < q.2 ∧ q.1 < p.1

/-- The pair `(p, q)` is **right**: `p.y < q.y` and `q.x > p.x`. -/
abbrev IsRightPair (p q : ℕ × ℕ) : Prop := p.2 < q.2 ∧ p.1 < q.1

/-- `(p, q, u)` with `p.y < q.y < u.y` is a **turn**: `(p, q)` left and `(q, u)` right, or
`(p, q)` right and `(q, u)` left. -/
abbrev IsTurn (p q u : ℕ × ℕ) : Prop :=
  p.2 < q.2 ∧ q.2 < u.2 ∧
    ((IsLeftPair p q ∧ IsRightPair q u) ∨ (IsRightPair p q ∧ IsLeftPair q u))

/-- `p` **completes a turn** in `P`: `p' = pre(p)` and `p'' = pd(p')` both exist and
`(p'', p', p)` is a turn. -/
abbrev CompletesTurn (P : Finset (ℕ × ℕ)) (p : ℕ × ℕ) : Prop :=
  ∃ p' ∈ P, IsPre P p' p ∧ ∃ p'' ∈ P, IsPd P p'' p' ∧ IsTurn p'' p' p

/-- `turns(P)`: the number of points of `P` that complete a turn. -/
def turns (P : Finset (ℕ × ℕ)) : ℕ :=
  (P.filter fun p => CompletesTurn P p).card

/-- The **time reverse** `P^R := {(x, T + 1 − t) | (x, t) ∈ P}` of an instance on `[N] × [T]`. -/
def timeReverse (T : ℕ) (P : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  P.image fun p => (p.1, T + 1 - p.2)

end ChaChaTree.DynOpt


