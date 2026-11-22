-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
-- name    : LeanPool_FormalLearningTheory_Criterion_Online
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:23.767191+00:00
-- url     : https://prove2.me/theorems/611d6a91-df42-44b0-83ab-e8b24a3af6bb
-- title:
--   Online
-- statement:
--   Definitions and structural lemmas for Online, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Criterion/Online.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
noncomputable def OnlineLearner.mistakesFrom {X : Type u} {Y : Type v} [DecidableEq Y]
    (L : OnlineLearner X Y) (state : L.State) (c : Concept X Y) : List X → ℕ
  | [] => 0
  | x :: xs =>
    (if L.predict state x ≠ c x then 1 else 0) +
      L.mistakesFrom (L.update state x (c x)) c xs
noncomputable def OnlineLearner.mistakes {X : Type u} {Y : Type v} [DecidableEq Y]
    (L : OnlineLearner X Y) (c : Concept X Y) (seq : List X) : ℕ :=
  L.mistakesFrom L.init c seq
def MistakeBounded (X : Type u) (Y : Type v) [DecidableEq Y]
    (C : ConceptClass X Y) (M : ℕ) : Prop :=
  ∃ (L : OnlineLearner X Y),
    ∀ (c : Concept X Y), c ∈ C →
      ∀ (seq : List X), L.mistakes c seq ≤ M
def OnlineLearnable (X : Type u) (Y : Type v) [DecidableEq Y] (C : ConceptClass X Y) : Prop :=
  ∃ (M : ℕ), MistakeBounded X Y C M
noncomputable def OnlineLearner.cumulativeLoss {X : Type u} {Y : Type v}
    (L : OnlineLearner X Y) (loss : LossFunction Y) (seq : List (X × Y)) : ℝ :=
  (seq.foldl
    (fun stateAndLoss sample =>
      let prediction := L.predict stateAndLoss.1 sample.1
      (L.update stateAndLoss.1 sample.1 sample.2,
        stateAndLoss.2 + loss prediction sample.2))
    (L.init, 0)).2
noncomputable def fixedHypothesisLoss {X : Type u} {Y : Type v}
    (h : Concept X Y) (loss : LossFunction Y) (seq : List (X × Y)) : ℝ :=
  seq.foldl (fun acc p => acc + loss (h p.1) p.2) 0
def RegretBounded (X : Type u) (Y : Type v)
    (H : HypothesisSpace X Y) (loss : LossFunction Y) (bound : ℕ → ℝ) : Prop :=
  ∃ (L : OnlineLearner X Y),
    ∀ (seq : List (X × Y)),
      ∀ (h : Concept X Y), h ∈ H →
        L.cumulativeLoss loss seq - fixedHypothesisLoss h loss seq ≤ bound seq.length


