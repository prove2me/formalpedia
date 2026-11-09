-- Prove2me | Definitions.Def_TermCycDich_IsRCycle
-- name    : TermCycDich_IsRCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:35.409687+00:00
-- url     : https://prove2.me/theorems/e7345b2d-b1b6-45c0-a32a-dadaca50bf92
-- title:
--   $R$-cycle
-- statement:
--   Let $G$ be a graph and $R \subseteq V(G)$ a set of **red vertices** (terminals). An **$R$-cycle** is a simple cycle of $G$ that contains every vertex of $R$.
--
--   For $R=\emptyset$ an $R$-cycle is any cycle of $G$; for $R = V(G)$ it is a Hamiltonian cycle. $R$-cycles are the solutions of Terminal Cyclability.
--
--   **Formalization Note** A cycle is a closed walk $p$ with Mathlib's `Walk.IsCycle` (at least three vertices, no repeated edge, no repeated vertex except the base point); "contains $v$" is membership in the support of $p$.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1, p.1 (PDF 3)

import Mathlib

namespace TermCycDich

/-- An **`R`-cycle** of the annotated graph `(G, R)`: a simple cycle of `G` containing every red
vertex (every vertex of `R`).

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1, p.1 (PDF 3): "one is given a graph G and a set R ⊆ V(G) of distinguished
vertices called terminals or red vertices. The task is then to find a simple cycle in G containing
all vertices in R. [...] We call the pair (G, R) an annotated graph and a solution an R-cycle."

**Formalization Note** The cycle is a Mathlib closed walk `p : G.Walk u u` with `p.IsCycle`
(at least three vertices, no repeated edge, no repeated vertex except the base point), so a
"simple cycle" in the paper's sense. "Contains all vertices of `R`" is membership in the walk's
support. For `R = ∅` an `R`-cycle is any cycle of `G`. -/
def IsRCycle {V : Type} (G : SimpleGraph V) (R : Set V) {u : V} (p : G.Walk u u) : Prop :=
  p.IsCycle ∧ ∀ v ∈ R, v ∈ p.support

end TermCycDich


