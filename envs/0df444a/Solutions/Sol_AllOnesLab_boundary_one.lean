-- Prove2me | solution 1 for AllOnesLab.boundary_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:56:57.995354+00:00
-- url     : https://prove2.me/submissions/f5a8453b-628a-4e80-b180-25c423140926

import Definitions.Def_AllOnesLab_Hard
import Definitions.Def_AllOnesLab_Main
import Theorems.Thm_P2M_AllOnesLab_boundary_one__d72b5fb3d4b1


set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) :=
  boundary_one'
end AllOnesLab
