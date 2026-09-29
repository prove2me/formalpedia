-- Prove2me | Definitions.Def_r03_defs_67e8a31036_m6_OrientationWords
-- name    : r03_defs_67e8a31036_m6_OrientationWords
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-17T01:20:13.569389+00:00
-- url     : https://prove2.me/theorems/b750031a-cc7c-4577-9765-4b4457a32435
-- title:
--   R03 P3-factor definition module: r03_defs_67e8a31036_m6_OrientationWords
-- statement:
--   This module packages source-faithful finite-graph, matching, port, or bookkeeping structures used by reusable auxiliary theorems in the cubic P3-partition formalization. It contains definitions and structural interfaces only; it does not assert closure of the open root problem.
--
--   **Formalization Note** The code was extracted from the cited candidate artifact and its exact digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/m6_OrientationWords.lean; source SHA-256 54277b0fc780c895a0158e2447ba28d22cde9880e98714db680bb37bb024588e; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib.Data.Fintype.Pi

/- Candidate-only orientation-word algebra, NOT a graph or root theorem.
A nontrivial alternating component has k+1 virtual matching edges. A bit
chooses which adjacent ordinary edge receives its old center. Each ordinary
edge must receive exactly one center. k=0 includes a labelled parallel pair,
whose physical lift is a triangle. Common matching edges are not components.
The translation from graphs to this encoding requires separate review. -/
namespace R03OrientationWordsM6

def receive (a b : Bool) : Nat := (if a then 1 else 0) + (if b then 0 else 1)

def Feasible (k : Nat) (f : Fin (k+1) → Bool) : Prop :=
  (∀ i : Fin k, receive (f i.castSucc) (f i.succ) = 1) ∧
  receive (f (Fin.last k)) (f 0) = 1

instance feasibleDecidable (k : Nat) (f : Fin (k+1) → Bool) : Decidable (Feasible k f) := by
  unfold Feasible
  infer_instance

end R03OrientationWordsM6


