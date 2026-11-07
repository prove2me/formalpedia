-- Prove2me | Definitions.Def_AaronsonAmbainis_Bridge_Poly
-- name    : AaronsonAmbainis_Bridge_Poly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T23:02:50.013463+00:00
-- url     : https://prove2.me/theorems/5b9307aa-410d-4f0a-a8d9-d4fe57304e98
-- title:
--   Poly
-- statement:
--   Definitions and structural lemmas for Poly, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Poly.lean

import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
set_option autoImplicit true
namespace AaronsonAmbainis.Bridge
open Finset MvPolynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def zoPt (x : Cube ι) : ι → ℝ := fun i => if x i then 1 else 0
noncomputable def pmPt (x : Cube ι) : ι → ℝ := fun i => if x i then -1 else 1
end AaronsonAmbainis.Bridge


