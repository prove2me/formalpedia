-- Prove2me | solution 1 for AllOnesGallardo.boundary_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:56.693115+00:00
-- url     : https://prove2.me/submissions/26c1ae25-815a-4659-b735-ccfb8d19841a

import Definitions.Def_AllOnesLab
import Definitions.Def_AllOnesComparator_Solution
import Theorems.Thm_AllOnesLab_boundary_one


set_option autoImplicit true
open Polynomial
open AllOnesGallardo
namespace AllOnesGallardo
theorem _root_.solution : Irreducible (allOnes 1) ∧ ¬ Irreducible (allOnesP 1) :=
  AllOnesLab.boundary_one
end AllOnesGallardo
