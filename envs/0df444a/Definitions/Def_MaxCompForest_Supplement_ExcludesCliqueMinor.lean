-- Prove2me | Definitions.Def_MaxCompForest_Supplement_ExcludesCliqueMinor
-- name    : MaxCompForest_Supplement_ExcludesCliqueMinor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:13:39.827324+00:00
-- url     : https://prove2.me/theorems/01ce6e62-5f25-4ce0-8706-71742605ed59
-- title:
--   Excluding $K_h$ as a minor
-- statement:
--   A graph $H$ **excludes $K_h$ as a minor** if there are no $h$ pairwise disjoint vertex sets $C_1,\dots,C_h$ such that each $H[C_i]$ is connected and any two of them are joined by an edge of $H$. Equivalently, $K_h$ cannot be obtained from $H$ by deleting and contracting edges and deleting vertices. Planar graphs exclude $K_5$.
--
--   **Formalization Note** The minor is given by its branch sets. For a multigraph the definition is applied to its underlying simple graph.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 5.3, p.30 (PDF p.32); Theorem J.1, p.59 (PDF p.61)

import Mathlib
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V : Type*}

/-- **`H` excludes `K_h` as a minor**: there are no `h` pairwise disjoint vertex sets, each inducing a connected
subgraph, any two of which are joined by an edge.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 5.3 p.30, Theorem J.1 p.59.

**Formalization Note.** A `K_h` minor is given by its branch sets (a clique minor model). A multigraph's minors
are those of its underlying simple graph; statements apply this to `G.toSimpleGraph`. Connectivity of the induced
subgraph includes nonemptiness of each branch set. -/
def ExcludesCliqueMinor (H : SimpleGraph V) (h : ℕ) : Prop :=
  ¬ ∃ K : Finset (Finset V), K.card = h ∧
    (∀ C ∈ K, (H.induce (C : Set V)).Connected) ∧
    (∀ C ∈ K, ∀ D ∈ K, C ≠ D → Disjoint C D) ∧
    (∀ C ∈ K, ∀ D ∈ K, C ≠ D → ∃ u ∈ C, ∃ v ∈ D, H.Adj u v)

end MaxCompForest.Supplement


