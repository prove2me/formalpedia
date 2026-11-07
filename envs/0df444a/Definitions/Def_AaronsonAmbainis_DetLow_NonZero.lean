-- Prove2me | Definitions.Def_AaronsonAmbainis_DetLow_NonZero
-- name    : AaronsonAmbainis_DetLow_NonZero
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:21:34.973567+00:00
-- url     : https://prove2.me/theorems/db5c4ea5-6284-4dc5-92ad-3639ce839e70
-- title:
--   Non Zero
-- statement:
--   Definitions and structural lemmas for Non Zero, from David Turturean / physical-superintelligence; see upstream NOTICE for AI disclosure and mathematical attributions's pinned Aaronson–Ambainis development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/DetLow/NonZero.lean

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
set_option autoImplicit true
namespace AaronsonAmbainis
namespace DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def evalAt (c : ℝ) : MvPolynomial ι ℤ →+* ℝ :=
  eval₂Hom (Int.castRingHom ℝ) (fun _ => c)
def agCount (x z : Cube ι) : ℕ := (univ.filter fun i => x i = z i).card
end DetLow
end AaronsonAmbainis


