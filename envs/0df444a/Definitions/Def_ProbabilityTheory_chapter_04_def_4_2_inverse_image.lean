-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_04_def_4_2_inverse_image
-- name    : ProbabilityTheory_chapter_04_def_4_2_inverse_image
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:59:01.630206+00:00
-- url     : https://prove2.me/theorems/64dc4e6d-7473-46eb-983d-ea3f05d8bbdc
-- title:
--   Chapter ?, generated supplement: supporting Lean bundle F000
-- statement:
--   Supporting Lean declarations for Chapter ?, source module `generated supplement`: `inverse_image`. The mathematical interpretation of this bundle needs review.
-- source:
--   Supplemental source module in importer v37; upstream repository https://github.com/wkshum/ProbabilityTheory/tree/e6387d4fd8005d627d2aec40d10f039ddb4e4b40

import Mathlib.Data.Set.Basic

universe u v

section InverseImageDefinition

variable {Ω : Type u} {Ω' : Type v}

def inverse_image (f : Ω → Ω') (A : Set Ω') : Set Ω :=
  {x : Ω | f x ∈ A}

notation f "⁻¹(" A ")" => inverse_image f A

example (f : Ω → Ω') (A : Set Ω') : Set Ω := f⁻¹( A )

example (f : Ω → Ω') (A : Set Ω') : inverse_image f A = f ⁻¹' A :=
  rfl

end InverseImageDefinition


