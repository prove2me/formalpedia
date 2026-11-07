-- Prove2me | Definitions.Def_NaturalProofs_Prob
-- name    : NaturalProofs_Prob
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:24:05.390454+00:00
-- url     : https://prove2.me/theorems/ab51e098-a1c6-4b44-ba35-d2e26ec9467f
-- title:
--   Prob
-- statement:
--   Definitions and structural lemmas for Prob, from zzyzek / NaturalProof-Lean contributors's pinned NaturalProof-Lean development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace NaturalProofs
open Finset
def ind (b : Bool) : ℝ := if b then 1 else 0
noncomputable def prob {Ω : Type} [Fintype Ω] (p : Ω → Bool) : ℝ :=
  (∑ ω, ind (p ω)) / Fintype.card Ω
variable {Ω Ω' A B I X : Type} [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype B] [Fintype I]
  [Fintype X]
end NaturalProofs


