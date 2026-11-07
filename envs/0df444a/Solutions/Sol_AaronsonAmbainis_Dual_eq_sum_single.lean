-- Prove2me | solution 1 for AaronsonAmbainis.Dual.eq_sum_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:44:25.373126+00:00
-- url     : https://prove2.me/submissions/e3d8daca-4620-4b02-ac67-5d894815b873

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Dual_Functional

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset
variable {β : Type*} [Fintype β] [DecidableEq β]
namespace AaronsonAmbainis.Dual
theorem _root_.solution (v : β → ℝ) : v = ∑ b, v b • (Pi.single b (1 : ℝ) : β → ℝ) := by
  funext c
  rw [Finset.sum_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro h
    exact absurd (Finset.mem_univ c) h
end AaronsonAmbainis.Dual
