-- Prove2me | Definitions.Def_ConeL2G_properColorings
-- name    : ConeL2G_properColorings
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:40.184963+00:00
-- url     : https://prove2.me/theorems/ced00430-46b6-4b63-ac99-8bd732e8b216
-- title:
--   Proper list colorings $\Omega_H$
-- statement:
--   Let $H$ be a finite graph on a vertex set $V$ and let every vertex $i$ carry a finite list $L_i$ of colors. The set of **proper list colorings** is
--   $$\Omega_H=\Big\{x\in\prod_{i\in V}L_i:\ x_i\neq x_j\ \text{for every edge } ij\in E(H)\Big\}.$$
--
--   In a local statement of the paper, $H$ is a subgraph of the ambient graph $G$ whose outside vertices have been given a fixed partial proper coloring, and $L_i$ is the list left at $i$ after removing the colors of outside neighbours.
--
--   **Formalization Note** Colors live in a palette $\mathrm{Fin}\,K$ that contains all lists; the adjacency condition is the platform predicate `MarkovMixing.IsProperColoring`. The palette size $K$ plays no role (the paper's $q$ is the minimum list size, not a palette size).
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 1, p.1 and Section 2.1, p.7

import Mathlib
import Definitions.Def_mm_coupling

namespace ConeL2G

open Finset

/-- **Proper list colorings** `Ω_H`. Li–Oveis Gharan, *Local-to-Global Theorems Based on Cones
with Applications to Graph Coloring*, arXiv:2610.37721, Section 1, p.1, and Section 2.1, p.7:
"`Ω_H = {x ∈ ∏ᵢ Lᵢ : xᵢ ≠ xⱼ ∀ ij ∈ E(H)}`".

For a finite graph `H` on `V` whose vertices carry lists `L i` of colors, `properColorings H L`
is the finite set of assignments `x` with `x i ∈ L i` for every vertex `i` and `x i ≠ x j` for
every edge `ij` (the adjacency part is the platform predicate `MarkovMixing.IsProperColoring`).

**Formalization Note.** Colors are elements of a palette `Fin K`; any finite family of finite
lists embeds in some `Fin K`, and `K` plays no role beyond containing the lists (the paper's `q`
is the minimum list size, not a palette size). In a local statement of the paper the lists are
those left after pinning the vertices outside `H` (Section 2.1, p.7). -/
def properColorings {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {K : ℕ} (L : V → Finset (Fin K)) : Finset (V → Fin K) :=
  univ.filter (fun x => (∀ i, x i ∈ L i) ∧ MarkovMixing.IsProperColoring H x)

end ConeL2G


