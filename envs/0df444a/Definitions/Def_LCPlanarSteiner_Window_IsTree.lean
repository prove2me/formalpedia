-- Prove2me | Definitions.Def_LCPlanarSteiner_Window_IsTree
-- name    : LCPlanarSteiner_Window_IsTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:24.797548+00:00
-- url     : https://prove2.me/theorems/b6280c4b-5945-4983-b9bf-b3a5dd211ec2
-- title:
--   Spanning trees of a window and their root paths
-- statement:
--   A spanning tree of a window rooted at $\rho$ is given by a **parent arc** and a **depth** for every retained vertex $v$: the parent arc is an arc of the window (or the pendant arc) with $v$ at one end, together with its orientation (from the parent to $v$, or from $v$ to the parent); the parent is $\rho$ or a retained vertex of smaller depth. Each retained vertex then has one parent arc and every parent chain ends at $\rho$, so the parent arcs form a spanning tree of the window.
--
--   The **root path** of $v$ is the list of oriented tree arcs from $\rho$ down to $v$.
--
--   **Formalization Note** Orientation flags record the direction of each arc along the root path, so a directed piece is a run of arcs with equal flags.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.2 and its proof, p.12

import Mathlib
import Definitions.Def_LCPlanarSteiner_Window

namespace LCPlanarSteiner

/-- **A spanning tree of a window, rooted at `ρ`, and its root paths.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.2, p.12: "A spanning tree of M has at most three directed pieces of length at most h
on each root path." Proof, p.12: "each vertex has one parent chain to an earlier layer".

A tree is given by a parent arc `pa v = (a, fwd)` and a depth `dp v` for each retained vertex `v`.
The arc `a` is `some e` (an arc of `A`) or `none` (the pendant arc); `fwd = true` means the arc is
directed from the parent to `v`, `fwd = false` from `v` to the parent.

`Window.IsTree G W pa dp`: for every `v ∈ V` the parent arc is an arc of `M` with `v` at the stated
end, and the parent is `ρ` or a retained vertex of smaller depth. Each retained vertex has exactly
one parent arc and parent chains decrease in depth, so the parent arcs form a spanning tree of `M`
rooted at `ρ`.

`parentV G W pa v` is the parent of `v` (`none` = `ρ`). `RootPath G W pa v l`: `l` is the root path
of `v`, the list of oriented tree arcs from `ρ` down to `v`.

**Formalization Note.** Orientation flags record the direction of each tree arc along the root
path, so a "directed piece" is a run of arcs with equal flags. -/
def parentV (G : Net) (W : Window) (pa : ℕ → Option ℕ × Bool) (v : ℕ) : Option ℕ :=
  match pa v with
  | (some e, true) => W.img (G.tl e)
  | (some e, false) => W.img (G.hd e)
  | (none, _) => none

/-- The parent arcs and depths form a spanning tree of the window rooted at `ρ`. -/
def Window.IsTree (G : Net) (W : Window) (pa : ℕ → Option ℕ × Bool) (dp : ℕ → ℕ) : Prop :=
  ∀ v ∈ W.V,
    (match pa v with
      | (some e, true) => e ∈ W.A ∧ G.hd e = v
      | (some e, false) => e ∈ W.A ∧ G.tl e = v
      | (none, fwd) => fwd = true ∧ W.pend = some v) ∧
    (∀ u, parentV G W pa v = some u → u ∈ W.V ∧ dp u < dp v)

/-- `l` is the root path of `v`: oriented tree arcs from `ρ` to `v`. -/
inductive RootPath (G : Net) (W : Window) (pa : ℕ → Option ℕ × Bool) :
    ℕ → List (Option ℕ × Bool) → Prop
  | top (v : ℕ) : v ∈ W.V → parentV G W pa v = none → RootPath G W pa v [pa v]
  | step (v u : ℕ) (l : List (Option ℕ × Bool)) : v ∈ W.V → parentV G W pa v = some u →
      RootPath G W pa u l → RootPath G W pa v (l ++ [pa v])

end LCPlanarSteiner


