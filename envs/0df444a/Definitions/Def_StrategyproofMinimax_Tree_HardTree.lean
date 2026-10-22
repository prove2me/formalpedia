-- Prove2me | Definitions.Def_StrategyproofMinimax_Tree_HardTree
-- name    : StrategyproofMinimax_Tree_HardTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T21:59:58.365746+00:00
-- url     : https://prove2.me/theorems/a300c1e9-deab-4ee6-9bda-5a21bfa54dcd
-- title:
--   The tree G(m, k) of Appendix B: two m-ary trees of depth k joined at their roots, edge lengths 1, 1, 2, 4, …
-- statement:
--   Fix $m,k\in\mathbb N$. The tree $G(m,k)$ is built as follows. An edge of length $1$ joins the vertices $l^0$ ("left") and $r^0$ ("right"). The vertex $l^0$ is joined to $m$ **left vertices on level 1** by edges of length $1$, and in general each left vertex on level $d$ is joined to $m$ left vertices on level $d+1$ by edges of length $2^d$, up to level $k$, whose vertices are leaves. The right side below $r^0$ is built in the same way. The network is continuous: its points are the vertices and every point inside an edge, and the distance between two points is the length of the shortest path between them. In particular a left vertex on level $d$ is at distance
--   $$d(l^0,l^d)=1+2+\dots+2^{d-1}=2^d-1$$
--   from $l^0$.
--
--   A vertex is named by its side $s\in\{\text{left},\text{right}\}$ and a word $w$ over the alphabet $\{0,\dots,m-1\}$ of length $d\le k$ (its level); the children of $(s,w)$ are $(s,wj)$. So $l^0=(\text{left},\varnothing)$, $r^0=(\text{right},\varnothing)$, and the left vertices on level 1 are $(\text{left},j)$, $j<m$.
--
--   This is the network on which Theorem 4.1 exhibits the lower bound.
--
--   **Formalization Note.** $G(m,k)$ is realised isometrically inside $\ell^1(E)$, with one coordinate per edge $e\in E$: the vertex $(s,w)$ has coordinate $2^j$ on the edge into its ancestor at level $j+1$ ($j<|w|$), a right vertex also has coordinate $1$ on the central edge, and all other coordinates are $0$. `HardTree m k` is the union of the closed segments between the endpoints of each edge (plus the vertices of level $\le k$), with the subspace metric of the $\ell^1$ norm; on this embedded tree the $\ell^1$ distance is the shortest-path length. Its σ-algebra is the Borel one. `vertex s w` is the vertex $(s,w)$ (a word longer than $k$ is truncated to length $k$; no statement uses one).
-- source:
--   Alon, Feldman, Procaccia, Tennenholtz, Strategyproof Approximation of the Minimax on Networks, Math. Oper. Res. 35(3) (2010), p. 524, Appendix B (construction of G); p. 515, Section 2 (continuous network, shortest-path distance)

import Mathlib

namespace StrategyproofMinimax.Tree

/-- The two halves of the tree of Appendix B: the `left` vertices hang below `l⁰`, the `right`
vertices below `r⁰`. -/
inductive Side
  | left
  | right
  deriving DecidableEq

/-- Edge labels of the tree `G(m, k)`. A vertex is a side `s` and a word `w` over `Fin m`; its
level is `w.length`, the root of side `s` (`l⁰` or `r⁰`) is the empty word, and the children of
`(s, w)` are `(s, w ++ [j])`, `j : Fin m`. The label `none` is the central edge `l⁰ – r⁰`, and
`some (s, w)` with `w ≠ []` is the edge from the parent `(s, w.dropLast)` to `(s, w)`. -/
abbrev Edge (m : ℕ) : Type := Option (Side × List (Fin m))

/-- The ambient space: `ℓ¹` functions on the edge labels, one real coordinate per edge. -/
abbrev Ambient (m : ℕ) : Type := lp (fun _ : Edge m => ℝ) 1

/-- Position of the vertex `(s, w)` in the ambient space. The edge from level `j` to level
`j + 1` has length `2ʲ` (p. 524), so the vertex `(s, w)` has coordinate `2ʲ` on the edge
`some (s, w.take (j + 1))` for every `j < w.length`; a right vertex also has coordinate `1`
(the length of the central edge) on `none`; every other coordinate is `0`. -/
noncomputable def vpos {m : ℕ} (s : Side) (w : List (Fin m)) : Ambient m :=
  (match s with
    | .left => 0
    | .right => lp.single 1 none (1 : ℝ)) +
  ∑ j ∈ Finset.range w.length, lp.single 1 (some (s, w.take (j + 1))) ((2 : ℝ) ^ j)

/-- The tree `G(m, k)` of Appendix B (p. 524) as a subset of the ambient space: the vertices of
level at most `k`, the central edge `[l⁰, r⁰]` of length `1`, and for every vertex `(s, w)` of
level `1 ≤ w.length ≤ k` the whole segment from its parent to it, of length `2^(w.length - 1)`.
(The vertex set is also the set of segment endpoints; it is listed so that `vertex` needs no
proof.) Edge interiors are included: agents and the facility may be anywhere on `G`. -/
def TreeSet (m k : ℕ) : Set (Ambient m) :=
  {p | ∃ (s : Side) (w : List (Fin m)), w.length ≤ k ∧ p = vpos s w} ∪
    segment ℝ (vpos .left []) (vpos .right []) ∪
    ⋃ (s : Side) (w : List (Fin m)) (_ : w ≠ [] ∧ w.length ≤ k),
      segment ℝ (vpos s w.dropLast) (vpos s w)

/-- The network `G = G(m, k)` of the proof of Theorem 4.1, with the metric induced by the
`ℓ¹` norm, which on this embedded tree is the length of the shortest path (p. 515), and the Borel
σ-algebra. -/
def HardTree (m k : ℕ) : Type := TreeSet m k

noncomputable instance (m k : ℕ) : MetricSpace (HardTree m k) :=
  inferInstanceAs (MetricSpace (TreeSet m k))

noncomputable instance (m k : ℕ) : MeasurableSpace (HardTree m k) := borel _

instance (m k : ℕ) : BorelSpace (HardTree m k) := ⟨rfl⟩

/-- The vertex `(s, w)` of `G(m, k)`: `vertex .left []` is `l⁰`, `vertex .right []` is `r⁰`, and
`vertex .left w` for a word of length `d ≤ k` is a left vertex on level `d`. (A word longer than
`k` is truncated to its first `k` letters; no statement uses such a word.) -/
noncomputable def vertex {m k : ℕ} (s : Side) (w : List (Fin m)) : HardTree m k :=
  ⟨vpos s (w.take k), Or.inl (Or.inl ⟨s, w.take k, List.length_take_le k w, rfl⟩)⟩

end StrategyproofMinimax.Tree


