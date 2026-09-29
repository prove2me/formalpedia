-- Prove2me | Definitions.Def_r03_defs_5719a22c9e_R03CenterHall
-- name    : r03_defs_5719a22c9e_R03CenterHall
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:20.694945+00:00
-- url     : https://prove2.me/theorems/a94cc5a4-eaa6-4d39-aa84-3fb9247c8a9d
-- title:
--   R03 candidate definition: r03 defs 5719a22c9e R03CenterHall
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_5719a22c9e_R03CenterHall.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Definitions.Def_cubic_p3_partition_models

/-!
# R03 center--Hall equivalence

For a finite graph, a P3 factor is equivalent to a finite center set of one
third of the vertices whose external neighborhood satisfies the two-fold Hall
inequality.  The proof uses a duplicated-center Hall matching; no cubicity or
connectivity assumption is needed for this equivalence.
-/

namespace CubicP3Partition

universe u

noncomputable section

variable {V : Type u}

/-- A finite set has one third of the ambient vertices. -/
def p12CenterSize [Fintype V] (C : Finset V) : Prop :=
  3 * C.card = Fintype.card V

/-- The vertices outside `C` adjacent to at least one member of `A`. -/
noncomputable def p12ExternalNeighborFinset [Fintype V] (G : SimpleGraph V)
    (C A : Finset V) : Finset V := by
  classical
  exact A.biUnion (fun v => G.neighborFinset v \ C)

/-- The two-fold Hall condition for the center set `C`. -/
def p12CenterHall [Fintype V] (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∀ A : Finset V, A ⊆ C →
    2 * A.card ≤ (p12ExternalNeighborFinset G C A).card

/-- Neighborhoods of duplicated centers, used by the reverse Hall construction. -/
noncomputable def p12DuplicateNeighbors [Fintype V] (G : SimpleGraph V)
    (C : Finset V) (A : Finset (↥C × Fin 2)) : Finset V := by
  classical
  exact {w : V | ∃ z ∈ A, G.Adj z.1.1 w ∧ w ∉ C}

/-- Reindex positions as center, first leaf, second leaf. -/
def p12PositionEquiv (k : Nat) :
    (Fin k × Fin 3) ≃ Fin k ⊕ (Fin k × Fin 2) := by
  let toFun : Fin k × Fin 3 → Fin k ⊕ (Fin k × Fin 2) := fun z =>
    if h : z.2 = 1 then Sum.inl z.1
    else if h0 : z.2 = 0 then Sum.inr (z.1, 0)
    else Sum.inr (z.1, 1)
  let invFun : Fin k ⊕ (Fin k × Fin 2) → Fin k × Fin 3 := fun z =>
    match z with
    | Sum.inl i => (i, 1)
    | Sum.inr ⟨i, j⟩ => (i, Fin.cases 0 (fun _ => 2) j)
  refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
  · rintro ⟨i, j⟩
    fin_cases j
    · simp [toFun, invFun]
    · simp [toFun, invFun]
    · simp [toFun, invFun]
      apply Fin.ext
      decide
  · intro z
    rcases z with i | ⟨i, j⟩
    · simp [toFun, invFun]
    · fin_cases j
      · simp [toFun, invFun]
      · simp [toFun, invFun]
        apply congrArg (fun x => Sum.inr (i, x))
        apply Fin.ext
        decide

end

end CubicP3Partition


