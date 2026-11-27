-- Prove2me | Definitions.Def_SizeRamsey_FiniteChecks
-- name    : SizeRamsey_FiniteChecks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:17:58.926563+00:00
-- url     : https://prove2.me/theorems/57e575f7-5200-521a-b7ef-f6aab9e380d5
-- title:
--   Finite Checks
-- statement:
--   Definitions and structural lemmas for Finite Checks, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/FiniteChecks.lean

module
public import Definitions.Def_SizeRamsey_Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey.Plan
instance {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (f : Fin 4 → V) :
    Decidable (IsC4Map G f) := by
  unfold IsC4Map
  infer_instance
instance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Decidable (HasC4 G) := by
  unfold HasC4
  infer_instance
instance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    Decidable (c4Transversal G S) := by
  unfold c4Transversal
  infer_instance
instance : DecidableRel wheel5.Adj := by
  unfold wheel5
  infer_instance
instance : DecidableRel k33MinusEdge.Adj := by
  unfold k33MinusEdge
  infer_instance
instance : DecidableRel octahedron.Adj := by
  unfold octahedron
  infer_instance
def QTrans {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a ≠ c → b ≠ d →
    a ∈ S ∨ b ∈ S ∨ c ∈ S ∨ d ∈ S
instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    Decidable (QTrans G S) := by
  unfold QTrans
  infer_instance
end SizeRamsey.Plan


