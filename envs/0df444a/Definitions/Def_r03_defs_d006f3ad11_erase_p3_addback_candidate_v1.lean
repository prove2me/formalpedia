-- Prove2me | Definitions.Def_r03_defs_d006f3ad11_erase_p3_addback_candidate_v1
-- name    : r03_defs_d006f3ad11_erase_p3_addback_candidate_v1
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T09:53:45.48261+00:00
-- url     : https://prove2.me/theorems/f7d2f46d-1470-4dfb-9139-dc947ff41647
-- title:
--   R03 candidate definition: r03 defs d006f3ad11 erase p3 addback candidate v1
-- statement:
--   This is a source-faithful definition module supporting a conditional formalization of the cubic P3-partition problem. It contains data structures and predicates used by separately published theorem candidates; it does not assert that the open root problem is solved.
-- source:
--   VibeMathing candidate definition artifact: Definitions/Def_r03_defs_d006f3ad11_erase_p3_addback_candidate_v1.lean; candidate-only formalization for ProblemContract problem:opg-46613-p3-partition.

import Definitions.Def_cubic_p3_partition_models

namespace CubicP3Partition

universe u

noncomputable section

/-- The three deleted vertices and their complement form a finite sum decomposition. -/
def p7_addBackEquiv {V : Type u} {G : SimpleGraph V} [Fintype V]
    (L : P3Path G) :
    ({v : V // v ≠ L.left ∧ v ≠ L.center ∧ v ≠ L.right} ⊕ Fin 3) ≃ V := by
  classical
  let triple : Fin 3 → V := fun i =>
    match i.1 with
    | 0 => L.left
    | 1 => L.center
    | _ => L.right
  let encode : V →
      ({v : V // v ≠ L.left ∧ v ≠ L.center ∧ v ≠ L.right} ⊕ Fin 3) :=
    fun v =>
      if hleft : v = L.left then Sum.inr 0
      else if hcenter : v = L.center then Sum.inr 1
      else if hright : v = L.right then Sum.inr 2
      else Sum.inl ⟨v, ⟨hleft, hcenter, hright⟩⟩
  refine
    { toFun := Sum.elim Subtype.val triple
      invFun := encode
      left_inv := ?_
      right_inv := ?_ }
  · rintro (v | i)
    · simp only [Sum.elim_inl]
      by_cases hleft : v.1 = L.left
      · exact False.elim (v.2.1 hleft)
      · by_cases hcenter : v.1 = L.center
        · exact False.elim (v.2.2.1 hcenter)
        · by_cases hright : v.1 = L.right
          · exact False.elim (v.2.2.2 hright)
          · simp [encode, hleft, hcenter, hright]
    · fin_cases i <;>
        simp [triple, encode, Ne.symm L.left_ne_center, Ne.symm L.center_ne_right,
          Ne.symm L.left_ne_right]
  · intro v
    by_cases hleft : v = L.left
    · simp [encode, hleft, triple]
    · by_cases hcenter : v = L.center
      · simp [encode, hcenter, triple, Ne.symm L.left_ne_center]
      · by_cases hright : v = L.right
        · simp [encode, hright, triple, Ne.symm L.center_ne_right,
            Ne.symm L.left_ne_right]
        · simp [encode, hleft, hcenter, hright, triple]

/-- A P3 factor on the erased graph extends by the deleted path. -/
def p7_addBackP3Factor {V : Type u} {G : SimpleGraph V} [Fintype V]
    (L : P3Path G) (hFactor : P3Factor (eraseP3 G L)) : P3Factor G := by
  classical
  let k := hFactor.blockCount
  let split : (Fin (k + 1) × Fin 3) ≃
      (Fin k × Fin 3) ⊕ (Fin 1 × Fin 3) :=
    (Equiv.prodCongr (@finSumFinEquiv k 1).symm (Equiv.refl (Fin 3))).trans
      (Equiv.sumProdDistrib (Fin k) (Fin 1) (Fin 3))
  let localSum : (Fin k × Fin 3) ⊕ (Fin 1 × Fin 3) ≃
      ({v : V // v ≠ L.left ∧ v ≠ L.center ∧ v ≠ L.right} ⊕ Fin 3) :=
    Equiv.sumCongr hFactor.place (Equiv.uniqueProd (Fin 3) (Fin 1))
  let place : (Fin (k + 1) × Fin 3) ≃ V :=
    split.trans (localSum.trans (p7_addBackEquiv L))
  refine { blockCount := k + 1, place := place, edge01 := ?_, edge12 := ?_ }
  · intro i
    generalize hb : (@finSumFinEquiv k 1).symm i = b
    cases b with
    | inl j =>
        have h0 : place (i, 0) = (hFactor.place (j, 0) : V) := by
          simp [place, split, localSum, p7_addBackEquiv, hb]
        have h1 : place (i, 1) = (hFactor.place (j, 1) : V) := by
          simp [place, split, localSum, p7_addBackEquiv, hb]
        have h := hFactor.edge01 j
        change G.Adj (hFactor.place (j, 0)) (hFactor.place (j, 1)) at h
        rw [h0, h1]
        exact h
    | inr j =>
        have h0 : place (i, 0) = L.left := by
          simp [place, split, localSum, p7_addBackEquiv, hb]
        have h1 : place (i, 1) = L.center := by
          simp [place, split, localSum, p7_addBackEquiv, hb]
        rw [h0, h1]
        exact L.edge_left
  · intro i
    generalize hb : (@finSumFinEquiv k 1).symm i = b
    cases b with
    | inl j =>
        have h1 : place (i, 1) = (hFactor.place (j, 1) : V) := by
          simp [place, split, localSum, p7_addBackEquiv, hb]
        have h2 : place (i, 2) = (hFactor.place (j, 2) : V) := by
          simp [place, split, localSum, p7_addBackEquiv, hb]
        have h := hFactor.edge12 j
        change G.Adj (hFactor.place (j, 1)) (hFactor.place (j, 2)) at h
        rw [h1, h2]
        exact h
    | inr j =>
        have h1 : place (i, 1) = L.center := by
          simp [place, split, localSum, p7_addBackEquiv, hb]
        have h2 : place (i, 2) = L.right := by
          simp [place, split, localSum, p7_addBackEquiv, hb]
        rw [h1, h2]
        exact L.edge_right

end

end CubicP3Partition


