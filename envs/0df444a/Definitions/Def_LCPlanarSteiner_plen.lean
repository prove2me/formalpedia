-- Prove2me | Definitions.Def_LCPlanarSteiner_plen
-- name    : LCPlanarSteiner_plen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:19.596108+00:00
-- url     : https://prove2.me/theorems/8917d1b2-4cec-4696-9135-5ce4860d702d
-- title:
--   Length and cost of a walk
-- statement:
--   For a walk $p = (e_1, \dots, e_k)$,
--   $$
--   \ell(p) = \sum_{j=1}^{k} \ell_{e_j},\qquad c(p) = \sum_{j=1}^{k} c_{e_j},
--   $$
--   summed along the walk, so an arc traversed twice counts twice. On a simple path $c(p)$ is the cost of its arc set.
--
--   **Formalization Note** The cost of a purchased set of arcs, where shared arcs are paid once, is the separate definition `pcost`.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §1, p.2 (lengths and costs); Lemma 3.2, p.5 ($c(Q) \le \Gamma$)

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **Length `ℓ(p)` and cost `c(p)` of a walk.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §1, p.2 (lengths `ℓ_e`, costs `c_e`);
Lemma 3.2, p.5 (`c(Q) ≤ Γ`).

`plen G p = Σ_{e ∈ p} ℓ_e` and `lcost G p = Σ_{e ∈ p} c_e`, summed along the list (an arc traversed
twice counts twice; on a simple path this is the cost of its arc set).

**Formalization Note.** These are list sums. The cost of a purchased arc *set*, where shared arcs
are paid once, is `pcost`. -/
def plen (G : Net) (p : List ℕ) : ℚ := (p.map G.lng).sum

/-- Cost of a walk, summed along the list. -/
def lcost (G : Net) (p : List ℕ) : ℚ := (p.map G.cst).sum

end LCPlanarSteiner


