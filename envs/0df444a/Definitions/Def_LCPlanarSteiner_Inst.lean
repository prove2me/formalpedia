-- Prove2me | Definitions.Def_LCPlanarSteiner_Inst
-- name    : LCPlanarSteiner_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:29.702907+00:00
-- url     : https://prove2.me/theorems/3dbd67ac-f7d3-4a53-892a-746cc181509a
-- title:
--   Instances of length-constrained directed Steiner forest
-- statement:
--   An **instance** consists of a graph $G$ with costs and lengths, a common length bound $h$, an accuracy $\varepsilon$ and an indexed list of $q$ demand pairs $(s_i, t_i)$; pairs may repeat or be self-pairs. It is **valid** when
--   1. $G$ is well-formed;
--   2. $h \ge 0$ and $0 < \varepsilon \le 1$, both rational;
--   3. $q \ge 1$, and every endpoint $s_i, t_i$ is a vertex.
--
--   This is the input of Theorem 1.2.
--
--   **Formalization Note** Validity is a hypothesis of the guarantee only; the algorithm must still return an output on every instance. $h = 0$ is allowed.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §1, p.2

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **An instance of length-constrained directed Steiner forest.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §1, p.2: "Directed Steiner forest
instead has an indexed list of q pairs (s_i, t_i), each requiring an original path of length at
most h … The accuracy 0 < ε ≤ 1 is rational."

An instance is the graph `net` (vertices, arcs with rational cost and length), the common length
bound `h`, the accuracy `ε`, and the indexed list `dem` of demand pairs `(s_i, t_i)`; `q` is its
length. Pairs may repeat and may be self-pairs.

`Valid I`: the graph is well-formed, `h ≥ 0`, `0 < ε ≤ 1`, `q ≥ 1`, and every demand endpoint is a
vertex.

**Formalization Note.** `Valid` is a hypothesis of the guarantee only; the algorithm is a function
on all instances. `h = 0` is allowed (p.16: "For h = 0, restrict to zero-length edges and use
nominal horizon one"). -/
structure Inst where
  /-- the graph with costs and lengths -/
  net : Net
  /-- the common length bound `h` -/
  h : ℚ
  /-- the accuracy `ε` -/
  ε : ℚ
  /-- the indexed demand pairs `(s_i, t_i)` -/
  dem : List (ℕ × ℕ)

/-- A valid instance: well-formed graph, `h ≥ 0`, `0 < ε ≤ 1`, `q ≥ 1`, endpoints are vertices. -/
def Inst.Valid (I : Inst) : Prop :=
  I.net.WF ∧ 0 ≤ I.h ∧ 0 < I.ε ∧ I.ε ≤ 1 ∧ I.dem ≠ [] ∧
    ∀ d ∈ I.dem, d.1 < I.net.n ∧ d.2 < I.net.n

end LCPlanarSteiner


