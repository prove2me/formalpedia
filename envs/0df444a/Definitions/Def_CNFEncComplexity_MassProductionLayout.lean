-- Prove2me | Definitions.Def_CNFEncComplexity_MassProductionLayout
-- name    : CNFEncComplexity_MassProductionLayout
-- status  : Definition
-- author  : @bersubs
-- created : 2026-11-15T06:35:45.392596+00:00
-- url     : https://prove2.me/theorems/04012e73-e414-4093-b105-2d70de292876
-- title:
--   Query and slot layout for mass-production CNFs
-- statement:
--   The first block holds the queries. Each slot then holds one word and an occupancy bit. The checker holds when every query agrees with some occupied slot.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614, Lemma 11, Section 3.4.

import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.Tuple.Basic

namespace CNFEncComplexity.MassProduction

def queryInputIndex {b n : ℕ} (i : Fin b) (j : Fin n) : Fin (b*n) :=
  finProdFinEquiv (i, j)

def queryIndex {b n : ℕ} (q : ℕ) (i : Fin b) (j : Fin n) :
    Fin (b*n+q*(n+1)) :=
  Fin.castAdd (q*(n+1)) (queryInputIndex i j)

def slotIndex (b : ℕ) {n q : ℕ} (r : Fin q) (j : Fin n) :
    Fin (b*n+q*(n+1)) :=
  Fin.natAdd (b*n) (finProdFinEquiv (r, j.castSucc))

def liveIndex (b n : ℕ) {q : ℕ} (r : Fin q) :
    Fin (b*n+q*(n+1)) :=
  Fin.natAdd (b*n) (finProdFinEquiv (r, Fin.last n))

def checkerPredicate (b n q : ℕ) (w : Fin (b*n+q*(n+1)) → Bool) : Bool :=
  decide (∀ i : Fin b, ∃ r : Fin q, w (liveIndex b n r) = true ∧
    ∀ j : Fin n, w (queryIndex q i j) = w (slotIndex b r j))

def packInput {b n q : ℕ} (x : Fin b → Fin n → Bool)
    (y : Fin q → Fin n → Bool) (live : Fin q → Bool) : Fin (b*n+q*(n+1)) → Bool :=
  Fin.addCases
    (fun i => x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
    (fun i => Fin.lastCases (live (finProdFinEquiv.symm i).1)
      (y (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2)

@[simp] theorem packInput_query {b n q : ℕ} (x : Fin b → Fin n → Bool)
    (y : Fin q → Fin n → Bool) (live : Fin q → Bool) (i : Fin b) (j : Fin n) :
    packInput x y live (queryIndex q i j) = x i j := by
  simp only [packInput, queryIndex, Fin.addCases_left, queryInputIndex, Equiv.symm_apply_apply]

@[simp] theorem packInput_slot {b n q : ℕ} (x : Fin b → Fin n → Bool)
    (y : Fin q → Fin n → Bool) (live : Fin q → Bool) (r : Fin q) (j : Fin n) :
    packInput x y live (slotIndex b r j) = y r j := by
  simp only [packInput, slotIndex, Fin.addCases_right, Equiv.symm_apply_apply, Fin.lastCases_castSucc]

@[simp] theorem packInput_live {b n q : ℕ} (x : Fin b → Fin n → Bool)
    (y : Fin q → Fin n → Bool) (live : Fin q → Bool) (r : Fin q) :
    packInput x y live (liveIndex b n r) = live r := by
  simp only [packInput, liveIndex, Fin.addCases_right, Equiv.symm_apply_apply, Fin.lastCases_last]

end CNFEncComplexity.MassProduction


