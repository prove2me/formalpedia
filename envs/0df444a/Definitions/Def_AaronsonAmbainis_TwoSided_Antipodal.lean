-- Prove2me | Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
-- name    : AaronsonAmbainis_TwoSided_Antipodal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:25:12.335779+00:00
-- url     : https://prove2.me/theorems/c663c80b-d05c-4425-b110-207d4edee5a5
-- title:
--   Antipodal
-- statement:
--   Definitions and structural lemmas for Antipodal, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def wingSet (w x y : ι → ℝ) : Finset ι :=
  if ∑ j, w j * x j * y j = 0 then ∅
  else univ.filter fun j => (w j)⁻¹ < (∑ j, w j * x j * y j)⁻¹ * y j
end AaronsonAmbainis


