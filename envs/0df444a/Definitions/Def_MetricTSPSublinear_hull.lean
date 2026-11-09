-- Prove2me | Definitions.Def_MetricTSPSublinear_hull
-- name    : MetricTSPSublinear_hull
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:28:00.192465+00:00
-- url     : https://prove2.me/theorems/f327e48d-bc42-45e9-b7b9-dcd42f0ad5bf
-- title:
--   The minimal subtree $T\langle S\rangle$ spanning $S$
-- statement:
--   For a tree $T$ on $V$ and $S\subseteq V$, $T\langle S\rangle$ denotes the **minimal subtree of $T$ spanning $S$**: the union of the paths of $T$ between points of $S$. Its weight $w(T\langle S\rangle)$ is the sum of the weights of its edges.
--
--   Lemma 4.4 compares $w(T\langle S\rangle)$ with the cut LP value $K(S)$.
--
--   **Formalization Note.** $T\langle S\rangle$ is recorded by its edge set. For $|S|\le1$ it has no edge and weight $0$.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_MetricTSPSublinear_treeDist

open scoped Classical

namespace MetricTSPSublinear

/-- **The minimal subtree `T⟨S⟩` spanning `S`.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.10 (PDF p.12): "Given a subset of vertices S ⊆ V(T), we use T⟨S⟩ to denote the minimal
subtree spanning S."

`hull E S` is the set of edges of the tree `E` that lie on the path between two points of `S`; its weight
`w(T⟨S⟩)` is `DoublingMST.treeWeight d (hull E S)`.

**Formalization Note.** The minimal subtree spanning `S` is the union of the tree paths between points of `S`, so it
is recorded by its edge set. For `|S| ≤ 1` it has no edge and weight `0`. -/
noncomputable def hull {n : ℕ} (E : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  E.filter (fun e => ∃ u ∈ S, ∃ v ∈ S, e ∈ pathEdges E u v)

end MetricTSPSublinear


