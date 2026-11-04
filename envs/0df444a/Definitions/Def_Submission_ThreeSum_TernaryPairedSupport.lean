-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
-- name    : Submission_ThreeSum_TernaryPairedSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:41:07.155475+00:00
-- url     : https://prove2.me/theorems/0f3b625d-37b2-4aff-86fa-20b22057a55c
-- title:
--   Ternary Paired Support
-- statement:
--   Definitions and structural lemmas for Ternary Paired Support, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPairedSupport
open Finset
attribute [local instance] Classical.propDecidable
variable {K E V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
  [AddCommGroup W] [Module K W] [Fintype W]
  [Fintype E]
section Endpoints
variable {ι : Type*} [Fintype ι]
def taggedEndpoints (L R : ι → V) : Sum ι ι → V × (K × K) :=
  Sum.elim (fun i => (L i,(1,0))) (fun i => (R i,(0,1)))
end Endpoints
section PhysicalSupport
variable {P D : Type*} [Fintype P] [DecidableEq D]
def physicalSupport (mode : P → D) : Finset D := univ.image mode
end PhysicalSupport
end ThreeSum.TernaryPairedSupport


