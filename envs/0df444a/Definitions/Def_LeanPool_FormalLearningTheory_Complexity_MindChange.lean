-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_Complexity_MindChange
-- name    : LeanPool_FormalLearningTheory_Complexity_MindChange
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:32:16.380801+00:00
-- url     : https://prove2.me/theorems/1ae2e56f-df27-41c6-907d-bf4b069f6445
-- title:
--   Mind Change
-- statement:
--   Definitions and structural lemmas for Mind Change, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/MindChange.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Data
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.SetTheory.Ordinal.Basic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v
def DataStream.prefix {X : Type u} {Y : Type v} (T : DataStream X Y) (t : ℕ) : List (X × Y) :=
  (List.range t).map T.observe
noncomputable def MindChangeCount (X : Type u) (L : GoldLearner X Bool)
    (c : Concept X Bool) (T : DataStream X Bool) : ℕ :=
  Set.ncard { t : ℕ | c = c ∧ L.conjecture (T.prefix t) ≠ L.conjecture (T.prefix (t + 1)) }
open Classical in
/-- Mind change ordinal: ordinal-valued complexity measure encoding both convergence
    and correctness. Returns a finite ordinal (< ω) when the learner converges correctly
    to concept c with finitely many mind changes. Returns ω otherwise (non-convergent,
    or convergent to wrong concept). This encoding makes `MindChangeOrdinal < ω` equivalent
    to correct convergence with finite mind changes  -  the key property for the mind change
    characterization theorem.

    Design rationale: encoding correctness at the definition level makes the backward
    direction of mind_change_characterization provable  -  `MindChangeOrdinal < ω` directly
    entails both convergence and correctness without needing to extract them separately. -/
noncomputable def MindChangeOrdinal (X : Type u) (L : GoldLearner X Bool)
    (c : Concept X Bool) (T : DataStream X Bool) : Ordinal :=
  let changes := { t : ℕ | L.conjecture (T.prefix t) ≠ L.conjecture (T.prefix (t + 1)) }
  if h : changes.Finite then
    if ∃ t₀, ∀ t ≥ t₀, L.conjecture (T.prefix t) = c
    then (h.toFinset.card : Ordinal)
    else Ordinal.omega0
  else Ordinal.omega0


