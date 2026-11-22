-- Prove2me | Definitions.Def_Comp_QualitativeLimitReach
-- name    : Comp_QualitativeLimitReach
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:56:20.917094+00:00
-- url     : https://prove2.me/theorems/3a24e371-15d4-4eb8-a7f6-b36d37dfdbe2
-- title:
--   Qualitative Limit Reach
-- statement:
--   Definitions and structural lemmas for Qualitative Limit Reach, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitReach.lean

import Definitions.Def_Comp_QualitativeLimitFinset
set_option autoImplicit true
namespace Comp
open Csg
namespace CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
def lpre1F (G : CsgQ S A1 A2) (w : S → Finset A1) (x : Finset S) : Finset S :=
  Finset.univ.filter fun s => G.bF (w s) x s = Finset.univ
end CsgQ
end Comp


