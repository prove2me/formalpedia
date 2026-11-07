-- Prove2me | Definitions.Def_MISInducedMinor_ThreeSeparatedCycles
-- name    : MISInducedMinor_ThreeSeparatedCycles
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:19.502105+00:00
-- url     : https://prove2.me/theorems/e0cbbc95-6265-4e25-8dae-74f14ee1502f
-- title:
--   Three nonadjacent cycles pairwise joined by paths avoiding the third
-- statement:
--   A graph $H$ **has three separated cycles** if it has three cycles $\Gamma_1,\Gamma_2,\Gamma_3$ such that
--
--   1. their vertex sets are pairwise disjoint, and no edge of $H$ joins two of them;
--   2. for all pairwise distinct $a,b,c\in\{1,2,3\}$ there is a path from a vertex of $\Gamma_a$ to a vertex of $\Gamma_b$ that avoids the closed neighbourhood $N_H[V(\Gamma_c)]$ of the third cycle.
--
--   This is the property of $H$ used in the proof of Lemma 3.1: no graph with it is an induced minor of the intermediate graph $G$, and the $5\times5$ grid has it.
--
--   **Formalization Note** A cycle is a closed walk satisfying Mathlib's `IsCycle`, represented by its vertex set. A walk replaces the path in item 2; every walk contains a path with the same ends whose vertices are among the walk's, so the two readings agree.
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), proof of Lemma 3.1, p.7

import Mathlib

set_option autoImplicit false

namespace MISInducedMinor

/-- `S` is the vertex set of a cycle of `H`: some closed walk `c` of `H` is a cycle (length at
least 3, no repeated vertex except its ends) and its vertices are exactly the elements of `S`. -/
def IsCycleVertexSet {W : Type*} (H : SimpleGraph W) (S : Set W) : Prop :=
  ∃ (v : W) (c : H.Walk v v), c.IsCycle ∧ ∀ x, x ∈ S ↔ x ∈ c.support

/-- `H` has **three vertex-disjoint and nonadjacent cycles `Γ₁, Γ₂, Γ₃` such that there is a
path between any two cycles avoiding the closed neighborhood of the third cycle**.
arXiv:2609.11285 (sha256 e378b906…), proof of Lemma 3.1, p.7.

The vertex sets `S 0, S 1, S 2` of the three cycles are pairwise disjoint, no edge of `H` joins
two of them, and for all pairwise distinct `a, b, c` there is a walk from a vertex of `S a` to a
vertex of `S b` none of whose vertices lies in `S c` or is adjacent to a vertex of `S c`.

**Formalization Note.** A walk in place of a path: every walk contains a path with the same
ends whose vertices are among the walk's, so the two readings agree. -/
def ThreeSeparatedCycles {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ S : Fin 3 → Set W,
    (∀ a, IsCycleVertexSet H (S a)) ∧
    (∀ a b, a ≠ b → Disjoint (S a) (S b)) ∧
    (∀ a b, a ≠ b → ∀ x ∈ S a, ∀ y ∈ S b, ¬ H.Adj x y) ∧
    (∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      ∃ x ∈ S a, ∃ y ∈ S b, ∃ p : H.Walk x y,
        ∀ z ∈ p.support, z ∉ S c ∧ ∀ s ∈ S c, ¬ H.Adj s z)

end MISInducedMinor


