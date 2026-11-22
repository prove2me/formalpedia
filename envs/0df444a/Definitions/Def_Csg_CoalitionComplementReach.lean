-- Prove2me | Definitions.Def_Csg_CoalitionComplementReach
-- name    : Csg_CoalitionComplementReach
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:49:59.429199+00:00
-- url     : https://prove2.me/theorems/bb379566-9185-4db8-9b22-366a3781b535
-- title:
--   Coalition Complement Reach
-- statement:
--   Definitions and structural lemmas for Coalition Complement Reach, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplementReach.lean

import Definitions.Def_Csg_CoalitionComplement
import Definitions.Def_Csg_ReachOp
set_option autoImplicit true
namespace Csg
namespace NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players) (G : NCSG S Players A)
end NCSG
end Csg


