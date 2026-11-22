-- Prove2me | Definitions.Def_Csg_MatchingPennies
-- name    : Csg_MatchingPennies
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:42:23.137907+00:00
-- url     : https://prove2.me/theorems/02385333-9059-4fea-8361-634f06057fa3
-- title:
--   Matching Pennies
-- statement:
--   Definitions and structural lemmas for Matching Pennies, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
set_option autoImplicit true
namespace Csg
noncomputable def penniesMatrix : MatrixGame (Fin 2) (Fin 2) where
  A i j := if i = j then -1 else 1
noncomputable def unif2 : Fin 2 → ℝ := fun _ => 1 / 2
noncomputable def penniesCSG : CSG Unit (Fin 2) (Fin 2) where
  K _ _ _ := PMF.pure ()
  r _ i j := penniesMatrix.A i j
end Csg


