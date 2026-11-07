-- Prove2me | Definitions.Def_AaronsonAmbainis_DetBij_Basic
-- name    : AaronsonAmbainis_DetBij_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:21:17.527225+00:00
-- url     : https://prove2.me/theorems/62273dff-e37d-4d18-bf58-69b00d0f5416
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetBij/Basic.lean

import Definitions.Def_AaronsonAmbainis_DetDefs
set_option autoImplicit true
namespace AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def agSet (x z : Cube ι) : Finset ι := univ.filter fun i => x i = z i
noncomputable def agExp (x z : Cube ι) : ι →₀ ℕ :=
  ∑ i, if x i = z i then Finsupp.single i 1 else 0
end AaronsonAmbainis.DetBij


