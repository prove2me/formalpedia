-- Prove2me | Definitions.Def_AaronsonAmbainis_TwoSided_Glue
-- name    : AaronsonAmbainis_TwoSided_Glue
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:25:33.51795+00:00
-- url     : https://prove2.me/theorems/292a26d6-ba9b-417d-a4d7-172099920c9a
-- title:
--   Glue
-- statement:
--   Definitions and structural lemmas for Glue, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
section NoFintype
variable {ι : Type*} [DecidableEq ι]
def glue (F : Finset ι) (z u : Cube ι) : Cube ι := fun i => if i ∈ F then u i else z i
lemma glue_glue_swap (F : Finset ι) (z u : Cube ι) :
    glue F (glue F z u) (glue F u z) = z := by
  funext i
  by_cases hF : i ∈ F <;> simp [glue, hF]
def glueEquiv (F : Finset ι) : (Cube ι × Cube ι) ≃ (Cube ι × Cube ι) where
  toFun p := (glue F p.1 p.2, glue F p.2 p.1)
  invFun q := (glue F q.1 q.2, glue F q.2 q.1)
  left_inv p := Prod.ext (glue_glue_swap F p.1 p.2) (glue_glue_swap F p.2 p.1)
  right_inv p := Prod.ext (glue_glue_swap F p.1 p.2) (glue_glue_swap F p.2 p.1)
end NoFintype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end AaronsonAmbainis


