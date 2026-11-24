-- Prove2me | Definitions.Def_RequestProject_MatchingPhase
-- name    : RequestProject_MatchingPhase
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T01:14:57.770801+00:00
-- url     : https://prove2.me/theorems/ccda3532-ed50-4c17-a8aa-3c9d8be9b171
-- title:
--   Matching Phase
-- statement:
--   Definitions and structural lemmas for Matching Phase, from yotam-gafni/FairAllocationWithOptionalSelling contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Fair allocation with optional selling and maximin-share bounds development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/MatchingPhase.lean

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
def IsCanonicalStrict (w p : G → ℝ) (τ : ℝ) (kept : Fin 3 → Finset G) (sold : Finset G)
    (money : Fin 3 → ℝ) (leftover : Fin 3) : Prop :=
  IsCanonical w p τ kept sold money leftover ∧ sold.card ≤ 2 ∧
    ∀ k, k ≠ leftover →
      money k = 0 ∨ ((kept k).card = 1 ∧ ∃ f ∈ sold, money k ≤ p f ∧ τ / 3 ≤ p f)
def SingleLossConfig (v : Fin 3 → G → ℝ) (p : G → ℝ) : Prop :=
  ∃ (x : Fin 3) (K S : Finset G) (m : ℝ),
    Disjoint K S ∧ 0 ≤ m ∧ m ≤ ∑ g ∈ S, p g ∧ S.card ≤ 1 ∧ (K.card ≤ 1 ∨ S = ∅) ∧
    (3 / 4 : ℝ) * MMS 3 (v x) p ≤ vbarSum (v x) p K + m ∧
    ∀ i, i ≠ x →
      ((3 / 4 : ℝ) * MMS 3 (v i) p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) (v i))
          (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m)))
      ∨ (vbarSum (v i) p K + m ≤ (3 / 4 : ℝ) * MMS 3 (v i) p ∧
          ∀ f ∈ S, (1 / 4 : ℝ) * MMS 3 (v i) p ≤ p f)
def LemmaFourCash (G : Type*) [Fintype G] [DecidableEq G] : Prop :=
  ∀ (w p : G → ℝ), (∀ g, 0 ≤ w g) → (∀ g, 0 ≤ p g) →
    (∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) →
    ∀ (K S : Finset G) (m : ℝ), Disjoint K S → 0 ≤ m → m ≤ ∑ g ∈ S, p g →
      S.card ≤ 1 → (K.card ≤ 1 ∨ S = ∅) → (∀ f ∈ S, (1 / 4 : ℝ) * MMS 3 w p ≤ p f) →
      vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p →
      (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ S)) w)
        (cashPrice (Finset.univ \ (K ∪ S)) p ((∑ g ∈ S, p g) - m))
def LemmaFourCashSold (G : Type*) [Fintype G] [DecidableEq G] : Prop :=
  ∀ (w p : G → ℝ), (∀ g, 0 ≤ w g) → (∀ g, 0 ≤ p g) →
    (∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p) →
    ∀ (K : Finset G) (f : G) (m : ℝ), f ∉ K → 0 ≤ m → m ≤ p f → K.card ≤ 1 →
      (1 / 4 : ℝ) * MMS 3 w p ≤ p f →
      vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p →
      (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ {f})) w)
        (cashPrice (Finset.univ \ (K ∪ {f})) p (p f - m))
end FairSelling


