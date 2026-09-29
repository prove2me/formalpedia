-- Prove2me | Definitions.Def_cubic_p3_partition_center_hall_aux
-- name    : cubic_p3_partition_center_hall_aux
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-16T10:15:28.425183+00:00
-- url     : https://prove2.me/theorems/ba798c12-d2c4-45c1-b9af-9a02227db79c
-- title:
--   Auxiliary duplicated-center and position models
-- statement:
--   Defines the duplicated-center neighbourhood and the finite position equivalence used in constructive Hall proofs for non-induced $P_3$-factors.
-- source:
--   Derived formal interface for the Prove2me mission ‘P3-Partitions of Cubic 3-Connected Graphs (OPG-46613)’, https://prove2.me/missions/P3-Partitions%20of%20Cubic%203-Connected%20Graphs%20%28OPG-46613%29.

import Definitions.Def_cubic_p3_partition_center_hall

namespace CubicP3Partition

universe u

noncomputable section

variable {V : Type u}

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


