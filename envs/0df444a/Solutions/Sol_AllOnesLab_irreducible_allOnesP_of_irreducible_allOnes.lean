-- Prove2me | solution 1 for AllOnesLab.irreducible_allOnesP_of_irreducible_allOnes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:24.122211+00:00
-- url     : https://prove2.me/submissions/71766985-6f1a-46e8-8dd4-79913567ce86

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard
import Theorems.Thm_AllOnesLab_irreducible_comp_P
import Theorems.Thm_AllOnesLab_allOnesP_eq_comp
import Theorems.Thm_AllOnesLab_allOnesP_monic
import Theorems.Thm_AllOnesLab_allOnesP_natDegree
import Theorems.Thm_AllOnesLab_allOnes_monic
import Theorems.Thm_AllOnesLab_allOnes_natDegree
import Theorems.Thm_AllOnesLab_even_of_irreducible_allOnes
import Theorems.Thm_AllOnesLab_trace_one_allOnes
import Theorems.Thm_AllOnesLab_trace_root_allOnes


set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n)
    (h : Irreducible (allOnes n)) : Irreducible (allOnesP n) := by
  haveI hfact : Fact (Irreducible (allOnes n)) := ⟨h⟩
  haveI hfin : Module.Finite (ZMod 2) (AdjoinRoot (allOnes n)) :=
    (allOnes_monic n).finite_adjoinRoot
  have hrank : Module.finrank (ZMod 2) (AdjoinRoot (allOnes n)) = n := by
    have h' := (AdjoinRoot.powerBasis' (allOnes_monic n)).finrank
    rw [AdjoinRoot.powerBasis'_dim, allOnes_natDegree] at h'
    exact h'
  -- Step 1: `Tr(α + 1) = Tr(α) + Tr(1) = 1 + n = 1`, since `n` is even.
  have hev : ((n : ℕ) : ZMod 2) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod 2) 2 n).2 (even_of_irreducible_allOnes n hn h).two_dvd
  have htr : Algebra.trace (ZMod 2) (AdjoinRoot (allOnes n))
      (AdjoinRoot.root (allOnes n) + 1) = 1 := by
    rw [map_add, trace_root_allOnes n (by omega), trace_one_allOnes n, hev, add_zero]
  rw [allOnesP_eq_comp]
  refine irreducible_comp_P (AdjoinRoot.root (allOnes n)) AdjoinRoot.adjoinRoot_eq_top htr
    (allOnes n) ?_ ?_ ?_
  · rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · rw [← allOnesP_eq_comp]; exact allOnesP_monic n
  · rw [← allOnesP_eq_comp, allOnesP_natDegree, hrank]
end AllOnesLab
