-- Prove2me | Definitions.Def_Comp_Reach
-- name    : Comp_Reach
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T22:51:48.633104+00:00
-- url     : https://prove2.me/theorems/1c8c5520-1b6c-40ee-a5d7-27108ab25083
-- title:
--   Reach
-- statement:
--   Definitions and structural lemmas for Reach, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Reach.lean

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
set_option autoImplicit true
namespace Comp
open Csg
namespace CsgQ
section Cast
variable {S : Type*}
noncomputable def castIcc (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) :
    S → Set.Icc (0 : ℝ) 1 :=
  fun s => ⟨((v s : ℚ) : ℝ), by exact_mod_cast h0 s, by exact_mod_cast h1 s⟩
end Cast
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
def reachGameQ (G : CsgQ S A1 A2) (s : S) (v : S → ℚ) : MatrixGameQ A1 A2 where
  A a1 a2 := G.expectQ s a1 a2 v
theorem toCSG_r_zero (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) :
    ∀ s a1 a2, (G.toCSG h).r s a1 a2 = 0 := by
  intro s a1 a2
  change ((G.r s a1 a2 : ℚ) : ℝ) = 0
  rw [hr0 s a1 a2, Rat.cast_zero]
end CsgQ
end Comp


