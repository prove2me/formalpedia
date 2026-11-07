-- Prove2me | Definitions.Def_LCPlanarSteiner_StrictForest
-- name    : LCPlanarSteiner_StrictForest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:05:35.00622+00:00
-- url     : https://prove2.me/theorems/be3d4a62-821f-4d69-8c7a-d31eac4e26a8
-- title:
--   Strict forests: every demand within length $h$
-- statement:
--   For a demand list $((s_1, t_1), \dots, (s_q, t_q))$, a bound $h$ and a set $S$ of arcs, $S$ is a **strict forest** when
--   $$
--   \mathrm{dist}_S(s_i, t_i) \le h \qquad \text{for every demand } i .
--   $$
--   The strict integral optimum $\mathrm{OPT}^F_h$ is the least cost $c(S)$ of a strict forest, and $\mathrm{OPT}^F_{h,w}$ the least cost of one whose underlying graph has treewidth at most $w$ ($+\infty$ if there is none). The instance is strictly feasible when all arcs together form a strict forest.
--
--   **Formalization Note** A bound $c(F) \le K\cdot \mathrm{OPT}^F_h$ is stated as $c(F) \le K\cdot c(S)$ for every strict forest $S$; the minimum is over finitely many arc sets, so the two are equivalent. Self-pairs are served by the empty walk.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §1, p.2

import Mathlib
import Definitions.Def_LCPlanarSteiner_DistLE

namespace LCPlanarSteiner

/-- **A strict forest: every demand has an original path of length at most `h` inside `S`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §1, p.2: "Directed Steiner forest
instead has an indexed list of q pairs (s_i, t_i), each requiring an original path of length at
most h. Write OPT_h and OPT^F_h for these strict integral optima."

`StrictForest G dem h S`: for every pair `(s, t)` in the demand list `dem`, `dist_S(s, t) ≤ h`.
The optimum `OPT^F_h` is the least `c(S)` over such arc sets `S`.

**Formalization Note.** A bound `c(F) ≤ K · OPT^F_h` is stated as `c(F) ≤ K · c(S)` for every strict
forest `S` (the minimum is over finitely many arc sets, so this is the same). Self-pairs `s = t` are
served by the empty walk. -/
def StrictForest (G : Net) (dem : List (ℕ × ℕ)) (h : ℚ) (S : Finset ℕ) : Prop :=
  ∀ d ∈ dem, DistLE G S d.1 d.2 h

end LCPlanarSteiner


