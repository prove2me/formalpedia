-- Prove2me | Definitions.Def_SupplyCorr_MonotoneSet
-- name    : SupplyCorr_MonotoneSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:26:24.880458+00:00
-- url     : https://prove2.me/theorems/32324622-3def-4b68-a9f6-970396eca1d4
-- title:
--   Monotone and maximal monotone subsets of $\mathbb R^N\times\mathbb R^N$ (Definition 4)
-- statement:
--   Let $N\ge 0$ and write vectors of $\mathbb R^N$ with the scalar product $p\cdot z$. A subset $G\subseteq\mathbb R^N\times\mathbb R^N$ of pairs $(z,p)$ (a production plan and a price vector) is **monotone** provided
--
--   $$(z-z')\cdot(p-p')\ge 0\qquad\text{whenever }(z,p),(z',p')\in G.$$
--
--   A monotone set $G$ is **maximal monotone** if it is maximal in the family of all monotone subsets of $\mathbb R^N\times\mathbb R^N$ ordered by inclusion: every monotone $G'\supseteq G$ equals $G$.
--
--   These are the standard notions of monotone operator theory, stated for subsets of $\mathbb R^N\times\mathbb R^N$ with the Euclidean pairing; the supply-correspondence model builds on them.
--
--   **Formalization Note** $\mathbb R^N$ is `Fin N → ℝ` with the dot product, for every $N$. The comparison in maximality ranges over every monotone subset, not only graphs of subdifferentials.
-- source:
--   Krishnamoorthy–Kushnir, A Simple Characterization of Supply Correspondences, arXiv:2205.10472v1, Definition 4, p.4

import Mathlib

open Matrix

namespace SupplyCorr

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Definition 4, p.4: a subset `G` of `ℝᴺ × ℝᴺ`
is *monotone* provided `(z − z′) · (p − p′) ≥ 0` whenever `(z, p), (z′, p′) ∈ G`.

Formalization Note: `ℝᴺ` is `Fin N → ℝ` with the dot product `⬝ᵥ`, for every `N : ℕ`
(the paper's standing assumption `N ≥ 2` is not used). A pair is written `(z, p)`, in the
paper's order. -/
def IsMonotoneSet {N : ℕ} (G : Set ((Fin N → ℝ) × (Fin N → ℝ))) : Prop :=
  ∀ a ∈ G, ∀ b ∈ G, 0 ≤ (a.1 - b.1) ⬝ᵥ (a.2 - b.2)

/-- Krishnamoorthy–Kushnir, arXiv:2205.10472v1, Definition 4, p.4: a monotone set is
*maximal monotone* if it is maximal in the family of monotone subsets of `ℝᴺ × ℝᴺ`, ordered by
inclusion.

Formalization Note: the comparison ranges over every monotone subset of `ℝᴺ × ℝᴺ` (not only
graphs of subdifferentials or of correspondences with nonempty values). -/
def IsMaximalMonotoneSet {N : ℕ} (G : Set ((Fin N → ℝ) × (Fin N → ℝ))) : Prop :=
  IsMonotoneSet G ∧ ∀ G' : Set ((Fin N → ℝ) × (Fin N → ℝ)), IsMonotoneSet G' → G ⊆ G' → G' = G

end SupplyCorr


