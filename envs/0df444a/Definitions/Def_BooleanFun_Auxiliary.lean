-- Prove2me | Definitions.Def_BooleanFun_Auxiliary
-- name    : BooleanFun_Auxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T18:58:19.867579+00:00
-- url     : https://prove2.me/theorems/9bd8f487-b1ea-4a19-b1e1-5981915d3fff
-- title:
--   Auxiliary
-- statement:
--   Definitions and structural lemmas for Auxiliary, from Joris Roos and contributors's pinned Boolean functions and Arrow’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-booleanfun/blob/3a75a656104e18dec6169c3f06f340ed9da43370/BooleanFun/Auxiliary.lean

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false
namespace BooleanFun
open Finset Pi
variable {α : Type*} {β : Type*}
variable {s : Finset α}
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}
variable {R : Type*} {M : Type*}
variable [Ring R] [AddCommGroup M] [Module R M]
section Singleton
end Singleton
section Ite
variable {α : Sort*} {P : Prop} [Decidable P] {a b c : α}
end Ite
noncomputable section OneOn
variable {p q : Prop}
open Classical
abbrev oneOn (p : Prop) : ℝ := ite (h := propDecidable p)  p 1 0
end OneOn
section PowStuff
end PowStuff
end BooleanFun


