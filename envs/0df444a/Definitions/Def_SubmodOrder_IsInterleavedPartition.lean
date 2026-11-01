-- Prove2me | Definitions.Def_SubmodOrder_IsInterleavedPartition
-- name    : SubmodOrder_IsInterleavedPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:56.987221+00:00
-- url     : https://prove2.me/theorems/3d46cc5c-7865-4e99-92b0-9b4bf434d255
-- title:
--   Interleaved partition
-- statement:
--   Let $\pi$ be an order of the ground set and $A$ a set. Sets $O_1,E_1,O_2,E_2,\dots,O_m,E_m$ form an **interleaved partition** of $A$ if they cover $A$ and alternate without crossing in the order $\pi$: in the sequence
--
--   $$
--   O_1,\ E_1,\ O_2,\ E_2,\ \dots,\ O_m,\ E_m
--   $$
--
--   every element of an earlier set has a smaller $\pi$-index than every element of a later set. The sets are then pairwise disjoint, and some of them may be empty. With these blocks one writes $E(j)=\bigcup_{\ell\le j}E_\ell$, $E(0)=\emptyset$.
--
--   Interleaved partitions carry the upper bounds of Lemma 1 and Corollary 2, which drive the analysis of all the algorithms of the paper.
--
--   **Formalization Note** Blocks are indexed by `Fin m` (0-based), and `Eprefix E j` is the union of the first $j$ blocks $E$. The paper adds "Formally, … $r_\pi(O_\ell)<l_\pi(E_\ell)\le r_\pi(E_\ell)<r_\pi(O_{\ell+1})$", which bounds only the rightmost element of $O_{\ell+1}$ and lets it reach to the left of $E_\ell$; under that formula Lemma 1 is false (the counterexample is recorded on Lemma 1), so the prose "alternate and never cross each other" is formalized. Empty blocks are allowed, as the proof of Theorem 2 needs.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, p.19, "Interleaved partitions"; p.19, "E(j) = ⋃_{ℓ≤j} Eℓ … with E(0) := ∅"

import Mathlib

namespace SubmodOrder

/-- `E(j) = ⋃_{ℓ ≤ j} E_ℓ` (Udwani, arXiv:2107.02743v5, p.19), with `E(0) = ∅`.

**Formalization Note.** Blocks are indexed by `Fin m`, i.e. 0-based: the paper's `E_ℓ`
(`ℓ ∈ [m]`) is `E ⟨ℓ - 1, _⟩`. `Eprefix E j` is the union of the first `j` blocks, so the
paper's `E(j)` is `Eprefix E j`, `E(m)` is `Eprefix E m`, and for the 0-based block `ℓ` the
paper's `E(ℓ − 1)` is `Eprefix E ℓ`. -/
def Eprefix {α : Type*} [DecidableEq α] {m : ℕ} (E : Fin m → Finset α) (j : ℕ) : Finset α :=
  (Finset.univ.filter fun i : Fin m => i.val < j).biUnion E

/-- `{O₁, E₁, O₂, …, O_m, E_m}` is an interleaved partition of `A` with respect to the order `π`
(Udwani, arXiv:2107.02743v5, p.19: "an interleaved partition {O1, E1, O2, · · · , Om, Em} of A is
given by sets {Oℓ}ℓ∈[m] and {Eℓ}ℓ∈[m] that alternate and never cross each other in the order
π.").

The blocks cover `A`, and in the sequence `O₁, E₁, O₂, E₂, …, O_m, E_m` every element of an
earlier block has a smaller `π`-index than every element of a later block.

**Formalization Note.** Blocks are indexed by `Fin m` (0-based). Empty blocks are allowed (the
proof of Theorem 2, p.21: "Note that some sets may be empty"). Disjointness of the blocks follows
from the strict comparisons. The paper's "Formally, … rπ(Oℓ) < lπ(Eℓ) ≤ rπ(Eℓ) < rπ(Oℓ+1)" only
bounds `rπ(Oℓ+1)` and lets `O_{ℓ+1}` reach left of `E_ℓ`; under it Lemma 1 is false, so the
prose ("alternate and never cross") is formalized. -/
def IsInterleavedPartition {α : Type*} [DecidableEq α] {n m : ℕ} (π : α ≃ Fin n)
    (O E : Fin m → Finset α) (A : Finset α) : Prop :=
  A = Finset.univ.biUnion (fun ℓ => O ℓ ∪ E ℓ) ∧
  (∀ ℓ₁ ℓ₂ : Fin m, ℓ₁ ≤ ℓ₂ → ∀ x ∈ O ℓ₁, ∀ y ∈ E ℓ₂, π x < π y) ∧
  (∀ ℓ₁ ℓ₂ : Fin m, ℓ₁ < ℓ₂ → ∀ x ∈ E ℓ₁, ∀ y ∈ O ℓ₂, π x < π y) ∧
  (∀ ℓ₁ ℓ₂ : Fin m, ℓ₁ < ℓ₂ → ∀ x ∈ O ℓ₁, ∀ y ∈ O ℓ₂, π x < π y) ∧
  (∀ ℓ₁ ℓ₂ : Fin m, ℓ₁ < ℓ₂ → ∀ x ∈ E ℓ₁, ∀ y ∈ E ℓ₂, π x < π y)

end SubmodOrder


