-- Prove2me | Definitions.Def_UniformSubpower_Supplied_LatticeOracle
-- name    : UniformSubpower_Supplied_LatticeOracle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:19:59.686575+00:00
-- url     : https://prove2.me/theorems/c8895852-15a9-4030-9a55-c886c7f7ae5d
-- title:
--   Lower covers of join-irreducibles and programs over lattice and order operations with an operation counter
-- statement:
--   For a finite lattice $Q$, $J(Q)$ denotes the nonzero join-irreducible elements and $M(Q)$ the proper meet-irreducible elements. For $g \in Q$ put, as in formula (2) of the paper,
--   $$g_* = \bigvee \{ i \in J(Q) : i < g \};$$
--   for $g \in J(Q)$ this is the unique lower cover of $g$.
--
--   A **program over lattice and order operations** accesses a bounded lattice $L$ only through a store of elements addressed by handles $0, 1, 2, \dots$. A step either stops with a result (for enumeration, a list of handles), or appends to the store the join or the meet of two stored elements, or asks whether one stored element is below another and branches on the answer. **Running** a program from an initial store returns its result, the final store and the number of join, meet and comparison steps performed. A handle beyond the store reads as $\bot$.
--
--   **Formalization Note.** `lowerStar` is defined by a classical finite join; `LatProg.run` is noncomputable only because the comparison uses classical decidability. The counter charges one unit per lattice or order operation and nothing for bookkeeping, as the operation count of Theorem 4.1 does.
-- source:
--   Gkantzounis, Uniform Subpower Membership for Finite Mal'tsev Algebras, STOC 2027 submission (manuscript sha256 149e66b1…), pp. 13–14, §4.2–§4.3, formula (2)

import Mathlib

universe u

namespace UniformSubpower.Supplied

/-!
Finite-lattice notions of §4.2–§4.3 (Gkantzounis, pp. 13–14): the lower cover `j∗` of a
join-irreducible, formula (2), and a minimal oracle model of a program that accesses a lattice
only through its lattice and order operations, with a counter of those operations
(Theorem 4.1).
-/

/-- `g∗ = ⋁ {i ∈ J(Q) : i < g}`, formula (2), p. 14: the join of the nonzero join-irreducibles
strictly below `g` (`J(Q)` is Mathlib's `SupIrred`, which excludes `⊥`). For `g ∈ J(Q)` it is the
unique lower cover of `g`. -/
noncomputable def lowerStar {Q : Type u} [Lattice Q] [OrderBot Q] [Fintype Q] (g : Q) : Q := by
  classical
  exact (Finset.univ.filter (fun i : Q => SupIrred i ∧ i < g)).sup id

/-- A program over a lattice, given only through its lattice and order operations. The program
holds a store of lattice elements, addressed by handles `0, 1, 2, …`; it never sees an element.
* `done a` stops with the result `a` (for enumeration: a list of handles);
* `join i k p` appends the join of the elements with handles `i`, `k` to the store, then runs `p`;
* `meet i k p` appends their meet, then runs `p`;
* `le i k p` asks whether element `i` is below element `k` and continues with `p` of the answer.
-/
inductive LatProg (α : Type) : Type where
  | done : α → LatProg α
  | join : ℕ → ℕ → LatProg α → LatProg α
  | meet : ℕ → ℕ → LatProg α → LatProg α
  | le : ℕ → ℕ → (Bool → LatProg α) → LatProg α

/-- Running a program on a bounded lattice from an initial store: returns the result, the final
store, and the number of lattice and order operations performed (one per `join`, `meet`, `le`
step). A handle beyond the store reads as `⊥`. -/
noncomputable def LatProg.run {L : Type u} [Lattice L] [BoundedOrder L] {α : Type} :
    LatProg α → List L → α × List L × ℕ
  | .done a, st => (a, st, 0)
  | .join i k p, st =>
      let r := p.run (st ++ [st.getD i ⊥ ⊔ st.getD k ⊥])
      (r.1, r.2.1, r.2.2 + 1)
  | .meet i k p, st =>
      let r := p.run (st ++ [st.getD i ⊥ ⊓ st.getD k ⊥])
      (r.1, r.2.1, r.2.2 + 1)
  | .le i k p, st =>
      have : Decidable (st.getD i ⊥ ≤ st.getD k ⊥) := Classical.dec _
      let r := (p (decide (st.getD i ⊥ ≤ st.getD k ⊥))).run st
      (r.1, r.2.1, r.2.2 + 1)

/-- The elements named by a list of handles in a store. -/
def readHandles {L : Type u} [Lattice L] [BoundedOrder L] (st : List L) (hs : List ℕ) : List L :=
  hs.map (fun k => st.getD k ⊥)

end UniformSubpower.Supplied


