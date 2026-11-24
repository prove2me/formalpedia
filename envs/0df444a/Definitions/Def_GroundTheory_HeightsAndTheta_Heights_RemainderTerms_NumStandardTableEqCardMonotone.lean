-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_NumStandardTableEqCardMonotone
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:05:28.509703+00:00
-- url     : https://prove2.me/theorems/59e83704-646d-40f9-8f46-7046f30c50e1
-- title:
--   Num Standard Table Eq Card Monotone
-- statement:
--   Definitions and structural lemmas for Num Standard Table Eq Card Monotone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/NumStandardTableEqCardMonotone.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics
open MvPolynomial Finset
theorem mem_youngCells {m : ℕ} (lam : Fin m → ℕ) (x : Fin m × ℕ) :
    x ∈ RestTerms.youngCells lam ↔ x.2 < lam x.1 := by
  unfold RestTerms.youngCells
  simp only [mem_filter, mem_product, mem_univ, mem_range, true_and]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨lt_of_lt_of_le h (Finset.single_le_sum (fun i _ => Nat.zero_le (lam i))
      (mem_univ x.1)), h⟩
theorem mem_shapeCells {r : ℕ} (la : Fin r → ℕ) (x : ℕ × ℕ) :
    x ∈ IndefiniteRowSideFullHecke.RestTerms.shapeCells la ↔ ∃ h : x.1 < r, x.2 < la ⟨x.1, h⟩ := by
  unfold IndefiniteRowSideFullHecke.RestTerms.shapeCells
  simp only [mem_biUnion, mem_univ, true_and, mem_image, mem_range]
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a.2, hb⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x.1, h⟩, x.2, hx, rfl⟩
def cellIso {r : ℕ} (la : Fin r → ℕ) :
    RestTerms.youngCells la ≃o IndefiniteRowSideFullHecke.RestTerms.shapeCells la where
  toFun p := ⟨((p.1.1 : ℕ), p.1.2),
    (mem_shapeCells la _).2 ⟨p.1.1.2, (mem_youngCells la _).1 p.2⟩⟩
  invFun q := ⟨(⟨q.1.1, ((mem_shapeCells la _).1 q.2).1⟩, q.1.2),
    (mem_youngCells la _).2 ((mem_shapeCells la _).1 q.2).2⟩
  left_inv p := rfl
  right_inv q := rfl
  map_rel_iff' := by
    rintro ⟨⟨a, b⟩, hp⟩ ⟨⟨c, d⟩, hq⟩
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Prod.mk_le_mk, Fin.le_def]
end GroundTheory.Heights₂.Heights.RestTerms.YoungDiagramCombinatorics


