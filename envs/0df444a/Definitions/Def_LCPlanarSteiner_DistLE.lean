-- Prove2me | Definitions.Def_LCPlanarSteiner_DistLE
-- name    : LCPlanarSteiner_DistLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:36.35138+00:00
-- url     : https://prove2.me/theorems/24033ebe-d9d6-4fde-af3f-db86e6e55942
-- title:
--   Distance bound $\mathrm{dist}_S(s,t) \le x$
-- statement:
--   For a set $S$ of arcs, vertices $s, t$ and a rational $x$,
--   $$
--   \mathrm{dist}_S(s, t) \le x
--   $$
--   means that some directed walk from $s$ to $t$ using only arcs of $S$ has length at most $x$. When no such walk exists the distance is $+\infty$ and the bound fails for every $x$.
--
--   This is how every distance bound of the paper is stated: purchased arrivals, strict witnesses, and the invariant (3).
--
--   **Formalization Note** No distance value is formed. A bound of the form $A \le \mathrm{dist}_F(r,b) + y$ is written as "$A \le \ell(W) + y$ for every walk $W$ from $r$ to $b$ in $F$".
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §3.1, p.5 (labels $a(b) = \mathrm{dist}_F(r,b)$); §4, p.9

import Mathlib
import Definitions.Def_LCPlanarSteiner_IsWalk
import Definitions.Def_LCPlanarSteiner_plen

namespace LCPlanarSteiner

/-- **`dist_S(s, t) ≤ x`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §3.1, p.5: "actual labels
a(b) = dist_F(r, b)"; §4, p.9: `dist_{H′}(s_i, v)`.

`DistLE G S s t x`: there is a directed walk from `s` to `t` using only arcs of `S` whose length is
at most `x`; that is, the shortest-path distance from `s` to `t` in the subgraph `S` is `≤ x`
(it is `+∞` when no walk exists, and then the statement is false for every `x`).

**Formalization Note.** The distance is never taken as a value (no infimum over an empty set is
formed): every bound `dist ≤ x` is this existential. A bound of the form "`A ≤ dist + y`" is written
as "for every walk `W`, `A ≤ ℓ(W) + y`". -/
def DistLE (G : Net) (S : Finset ℕ) (s t : ℕ) (x : ℚ) : Prop :=
  ∃ p : List ℕ, IsWalk G s t p ∧ (∀ e ∈ p, e ∈ S) ∧ plen G p ≤ x

end LCPlanarSteiner


