-- Prove2me | Definitions.Def_Comp_QualitativeAlmostFinset
-- name    : Comp_QualitativeAlmostFinset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:56:14.031106+00:00
-- url     : https://prove2.me/theorems/b895b889-fbf7-49be-bddc-9c30ea42efcd
-- title:
--   Qualitative Almost Finset
-- statement:
--   Definitions and structural lemmas for Qualitative Almost Finset, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeAlmostFinset.lean

import Definitions.Def_Comp_QualitativeLimitFinset
set_option autoImplicit true
namespace Comp
open Csg
namespace CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
def apre1F (G : CsgQ S A1 A2) (x y : Finset S) : Finset S :=
  Finset.univ.filter fun s => G.bF (G.aF ∅ y s) x s = Finset.univ
def afStepF (G : CsgQ S A1 A2) (b y x : Finset S) : Finset S := G.apre1F x y ∪ b
end CsgQ
end Comp


