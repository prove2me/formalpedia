-- Prove2me | Definitions.Def_RequestProject_LemmaFourNecessity
-- name    : RequestProject_LemmaFourNecessity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:16:48.82137+00:00
-- url     : https://prove2.me/theorems/fa6eddd7-6259-4385-865f-90085ae1a12d
-- title:
--   Lemma Four Necessity
-- statement:
--   Definitions and structural lemmas for Lemma Four Necessity, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourNecessity.lean

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
set_option autoImplicit true
open scoped BigOperators
namespace FairSelling
def LemmaFourCashNoPrice (G : Type*) [Fintype G] [DecidableEq G] : Prop :=
  ∀ (w p : G → ℝ), (∀ g, 0 ≤ w g) → (∀ g, 0 ≤ p g) →
    (∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) →
    ∀ (K S : Finset G) (m : ℝ), Disjoint K S → 0 ≤ m → m ≤ ∑ g ∈ S, p g →
      S.card ≤ 1 → (K.card ≤ 1 ∨ m = 0) →
      vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p →
      (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
        (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m))
namespace LemmaFourCounterexample
def wn : Fin 6 → ℕ
  | 0 => 37
  | 1 => 13
  | 2 => 37
  | 3 => 13
  | 4 => 37
  | 5 => 13
noncomputable def w : Fin 6 → ℝ := fun g => (wn g : ℝ)
def p : Fin 6 → ℝ := fun _ => 0
def parts : Fin 3 → Finset (Fin 6)
  | 0 => {0, 1}
  | 1 => {2, 3}
  | 2 => {4, 5}
def K : Finset (Fin 6) := {0}
def S : Finset (Fin 6) := {2}
def R : Finset (Fin 6) := Finset.univ \ (K ∪ S)
def cwn : Option (Fin 6) → ℕ
  | none => 0
  | some g => if g ∈ R then wn g else 0
end LemmaFourCounterexample
end FairSelling


