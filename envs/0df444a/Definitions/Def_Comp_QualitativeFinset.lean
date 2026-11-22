-- Prove2me | Definitions.Def_Comp_QualitativeFinset
-- name    : Comp_QualitativeFinset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:52:27.711554+00:00
-- url     : https://prove2.me/theorems/0d99b0aa-e225-405d-8543-2afddec8949b
-- title:
--   Qualitative Finset
-- statement:
--   Definitions and structural lemmas for Qualitative Finset, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean

import Definitions.Def_Comp_Qualitative
set_option autoImplicit true
namespace Comp
open Csg
namespace CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
def supportF (G : CsgQ S A1 A2) (s : S) (a1 : A1) (a2 : A2) : Finset S :=
  Finset.univ.filter fun s' => G.K s a1 a2 s' ≠ 0
def pre1F (G : CsgQ S A1 A2) (x : Finset S) : Finset S :=
  Finset.univ.filter fun s => ∃ a1, ∀ a2, G.supportF s a1 a2 ⊆ x
def gStepF (G : CsgQ S A1 A2) (safe x : Finset S) : Finset S := G.pre1F x ∩ safe
end CsgQ
end Comp


