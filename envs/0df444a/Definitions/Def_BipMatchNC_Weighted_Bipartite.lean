-- Prove2me | Definitions.Def_BipMatchNC_Weighted_Bipartite
-- name    : BipMatchNC_Weighted_Bipartite
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:11:21.442572+00:00
-- url     : https://prove2.me/theorems/459c1c59-8327-4745-b28c-d673e96b521e
-- title:
--   Weighted bipartite graphs: perfect and left-saturating matchings, their weights, and the node-potential dual LP (§2.1, §3.3)
-- statement:
--   Let $L$ and $R$ be finite sets of left and right vertices, $E(u,v)\in\{0,1\}$ the edge indicator and $w(u,v)\in\mathbb N$ the weight of the edge $(u,v)$ (values off the edges play no role). A **perfect matching** (for $|L|=|R|$) is a bijection $e:L\to R$ all of whose pairs $(u,e(u))$ are edges; a **left-saturating matching** is an injective $f:L\to R$ all of whose pairs are edges. The weight of a matching is
--   $$w(M)=\sum_{u\in L}w(u,f(u)),$$
--   and $\max$ PM weight is the largest weight of a perfect matching ($0$ if there is none).
--
--   The **dual LP (node potentials)** of the maximum weight left-saturating matching LP asks for $y:L\to\mathbb R$, $z:R\to\mathbb R$ with
--   $$y_u+z_v\ge w(u,v)\ \text{ for every edge }(u,v),\qquad z_v\ge0,$$
--   minimizing $\sum_{u\in L}y_u+\sum_{v\in R}z_v$. For a balanced graph the constraint $z_v\ge0$ can be skipped; the corresponding feasibility notion has $y$ and $z$ free. An edge is **tight** for $(y,z)$ if $y_u+z_v=w(u,v)$.
--
--   **Formalization Note.** `IsPerfectMatchingOn E e` for `e : L ≃ R`, `IsLeftSaturatingOn E f`, `matchingWeight w f`, `maxPerfectMatchingWeight E w`, `IsDualFeasible` (printed LP, with $z\ge0$), `IsBalancedDualFeasible` (no sign constraint on $z$), `dualValue` and `IsTight` (which includes being an edge). Weights are natural numbers and dual values real numbers.
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 4 (PDF 5) §2.1 and pp. 15–16 (PDF 16–17), §3.3 (primal and dual LP)

import Mathlib

namespace BipMatchNC.Weighted

/-! General weighted bipartite graphs on finite vertex sets `L` (left) and `R` (right), with edge
indicator `E : L → R → Bool` and natural edge weights `w : L → R → ℕ` (only the values on edges
matter): matchings, their weights, and the node-potential dual LP (§2.1, p. 4 and §3.3, p. 15). -/

variable {L R : Type*}

/-- A **perfect matching** of a bipartite graph with `|L| = |R|`, as a bijection `e : L ≃ R` all of
whose pairs `(u, e u)` are edges (§2.1, p. 4: it covers every vertex). -/
def IsPerfectMatchingOn (E : L → R → Bool) (e : L ≃ R) : Prop :=
  ∀ u, E u (e u) = true

/-- A **left-saturating matching** (§2.1, p. 4): an injective `f : L → R` all of whose pairs
`(u, f u)` are edges; it covers every vertex of `L`. -/
def IsLeftSaturatingOn (E : L → R → Bool) (f : L → R) : Prop :=
  Function.Injective f ∧ ∀ u, E u (f u) = true

/-- The weight `w(M) = Σ_{e ∈ M} w(e)` of the matching `{(u, f u) : u ∈ L}` (§2.1, p. 4). -/
def matchingWeight [Fintype L] (w : L → R → ℕ) (f : L → R) : ℕ :=
  ∑ u, w u (f u)

/-- The maximum weight of a perfect matching (`0` when there is none; every statement using it
provides a perfect matching). -/
def maxPerfectMatchingWeight [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : L → R → Bool) (w : L → R → ℕ) : ℕ :=
  (Finset.univ.filter fun e : L ≃ R => ∀ u, E u (e u) = true).sup fun e => matchingWeight w e

/-- A **feasible solution of the dual LP** ("node potentials", §3.3, p. 15):
`y_u + z_v ≥ w(u, v)` for every edge `(u, v)`, `y_u ∈ ℝ`, `z_v ≥ 0`. -/
def IsDualFeasible (E : L → R → Bool) (w : L → R → ℕ) (y : L → ℝ) (z : R → ℝ) : Prop :=
  (∀ v, 0 ≤ z v) ∧ ∀ u v, E u v = true → (w u v : ℝ) ≤ y u + z v

/-- A feasible dual solution for a **balanced** bipartite graph: "the dual constraint `z_v ≥ 0` can
be skipped in the case of a balanced bipartite graph" (§3.3, p. 15), so only
`y_u + z_v ≥ w(u, v)` on edges is required, with `y` and `z` free. -/
def IsBalancedDualFeasible (E : L → R → Bool) (w : L → R → ℕ) (y : L → ℝ) (z : R → ℝ) : Prop :=
  ∀ u v, E u v = true → (w u v : ℝ) ≤ y u + z v

/-- The dual objective `Σ_{u ∈ L} y_u + Σ_{v ∈ R} z_v` (§3.3, p. 15). -/
def dualValue [Fintype L] [Fintype R] (y : L → ℝ) (z : R → ℝ) : ℝ :=
  ∑ u, y u + ∑ v, z v

/-- An edge `(u, v)` is **tight** for the dual solution `(y, z)` if `y_u + z_v = w(u, v)`
(§3.3, p. 16). -/
def IsTight (E : L → R → Bool) (w : L → R → ℕ) (y : L → ℝ) (z : R → ℝ) (u : L) (v : R) : Prop :=
  E u v = true ∧ y u + z v = (w u v : ℝ)

end BipMatchNC.Weighted


