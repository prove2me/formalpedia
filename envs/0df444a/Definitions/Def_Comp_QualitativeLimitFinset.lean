-- Prove2me | Definitions.Def_Comp_QualitativeLimitFinset
-- name    : Comp_QualitativeLimitFinset
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:54:47.364578+00:00
-- url     : https://prove2.me/theorems/8841dca6-5195-47b8-8a67-a88f3b986e38
-- title:
--   Qualitative Limit Finset
-- statement:
--   Definitions and structural lemmas for Qualitative Limit Finset, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean

import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_Reach
import Definitions.Def_Csg_QualitativeLimitSure
set_option autoImplicit true
namespace Comp
open Csg
namespace CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
def aF (G : CsgQ S A1 A2) (v2 : Finset A2) (y : Finset S) (s : S) : Finset A1 :=
  Finset.univ.filter fun a1 => ∀ a2, a2 ∈ v2 ∨ G.supportF s a1 a2 ⊆ y
def bF (G : CsgQ S A1 A2) (v1 : Finset A1) (x : Finset S) (s : S) : Finset A2 :=
  Finset.univ.filter fun a2 => ∃ a1 ∈ v1, (G.supportF s a1 a2 ∩ x).Nonempty
def lStepF (G : CsgQ S A1 A2) (x y : Finset S) (s : S) (w : Finset A1) : Finset A1 :=
  G.aF (G.bF w x s) y s
end CsgQ
end Comp


