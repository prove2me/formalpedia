-- Prove2me | Definitions.Def_Comp_Shapley
-- name    : Comp_Shapley
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:44:23.583708+00:00
-- url     : https://prove2.me/theorems/1eaa0083-da41-4d9d-9188-586d47a015ba
-- title:
--   Shapley
-- statement:
--   Definitions and structural lemmas for Shapley, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Shapley.lean

import Definitions.Def_Comp_Search
set_option autoImplicit true
namespace Comp
open Csg
namespace DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
def shapleyGameQ (G : DiscountedCsgQ S A1 A2) (s : S) (v : S → ℚ) : MatrixGameQ A1 A2 where
  A a1 a2 := G.toCsgQ.r s a1 a2 + G.l * G.toCsgQ.expectQ s a1 a2 v
end DiscountedCsgQ
end Comp


