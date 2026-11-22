-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Learner_Monad
-- name    : LeanPool_FormalLearningTheory_Learner_Monad
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:42:40.89118+00:00
-- url     : https://prove2.me/theorems/ac286499-d5ca-4bee-a564-2736aad97d36
-- title:
--   Monad
-- statement:
--   Definitions and structural lemmas for Monad, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Monad.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Theorems.Thm_measurableBatchLearner_concat

set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
structure MeasLearner (X : Type u) [MeasurableSpace X] where
  /-- Underlying batch learner. -/
  learner : BatchLearner X Bool
  measurable : MeasurableBatchLearner X learner
noncomputable def MeasLearner.pure
    {X : Type u} [MeasurableSpace X]
    (h : Concept X Bool) (hm : Measurable h) : MeasLearner X where
  learner := {
    hypotheses := {h}
    learn := fun _ => h
    output_in_H := fun _ => Set.mem_singleton h
  }
  measurable := ⟨fun _m => hm.comp measurable_snd⟩
noncomputable def MeasLearner.bind
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    (hsel : ∀ m, Measurable (fun S : Fin m → X × Bool => @sel m S)) :
    MeasLearner X where
  learner := concatLearner (fun n => (family n).learner) sel
  measurable := measurableBatchLearner_concat _ sel hsel


