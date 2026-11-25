-- Prove2me | solution 1 for AllOnesLab.trace_one_allOnes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:17.374808+00:00
-- url     : https://prove2.me/submissions/be2f114c-bd98-448d-b5e8-c3af194dbc11

import Definitions.Def_AllOnesLab_Basic
import Definitions.Def_AllOnesLab_Trace
import Theorems.Thm_AllOnesLab_allOnes_monic
import Theorems.Thm_AllOnesLab_allOnes_natDegree


set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) :
    Algebra.trace (ZMod 2) (AdjoinRoot (allOnes n)) 1 = (n : ZMod 2) := by
  have hm : (allOnes n).Monic := allOnes_monic n
  have hrank : Module.finrank (ZMod 2) (AdjoinRoot (allOnes n)) = n := by
    rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim, allOnes_natDegree]
  have h := Algebra.trace_algebraMap (R := ZMod 2) (S := AdjoinRoot (allOnes n)) 1
  rw [map_one, hrank] at h
  rw [h, nsmul_eq_mul, mul_one]
end AllOnesLab
