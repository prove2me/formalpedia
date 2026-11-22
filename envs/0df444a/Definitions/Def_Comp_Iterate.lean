-- Prove2me | Definitions.Def_Comp_Iterate
-- name    : Comp_Iterate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:32:23.263312+00:00
-- url     : https://prove2.me/theorems/7fc3ed04-2c43-42f0-9d61-1e4c1dacbed5
-- title:
--   Iterate
-- statement:
--   Definitions and structural lemmas for Iterate, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Iterate.lean

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
set_option autoImplicit true
namespace Comp
open Csg
namespace DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
def stepValues (G : DiscountedCsgQ S A1 A2) (Ss : List S) (As1 : List A1) (As2 : List A2)
    (v : S → ℚ) : List (Option ℚ) :=
  Ss.map fun s => ((G.shapleyGameQ s v).findValueCert As1 As2).map fun c => c.1
def stepWitnesses (G : DiscountedCsgQ S A1 A2) (Ss : List S) (As1 : List A1) (As2 : List A2)
    (v : S → ℚ) : List (Option (ℚ × List ℚ × List ℚ)) :=
  Ss.map fun s => ((G.shapleyGameQ s v).findValueCert As1 As2).map fun c =>
    (c.1, As1.map c.2.1, As2.map c.2.2)
end DiscountedCsgQ
end Comp


