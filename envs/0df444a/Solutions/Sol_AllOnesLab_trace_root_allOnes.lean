-- Prove2me | solution 1 for AllOnesLab.trace_root_allOnes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:14.706612+00:00
-- url     : https://prove2.me/submissions/f074b166-814e-4f63-b98b-f8aec35d3cc5

import Definitions.Def_AllOnesLab_Basic
import Definitions.Def_AllOnesLab_Trace
import Theorems.Thm_AllOnesLab_allOnes_monic
import Theorems.Thm_AllOnesLab_allOnes_natDegree
import Theorems.Thm_AllOnesLab_allOnes_nextCoeff

section
open Polynomial
namespace AllOnesLab
private lemma zmod_two_neg_one : -(1 : ZMod 2) = 1 := by decide
private lemma minpoly_root_of_monic {F : Type*} [Field F] {f : F[X]} (hf : f.Monic) :
    minpoly F (AdjoinRoot.root f) = f := by
  rw [AdjoinRoot.minpoly_root hf.ne_zero, hf.leadingCoeff, inv_one, map_one, mul_one]
end AllOnesLab
end

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    Algebra.trace (ZMod 2) (AdjoinRoot (allOnes n)) (AdjoinRoot.root (allOnes n)) = 1 := by
  have hm : (allOnes n).Monic := allOnes_monic n
  haveI hnt : Nontrivial (AdjoinRoot (allOnes n)) := by
    refine AdjoinRoot.nontrivial _ ?_
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, allOnes_natDegree]
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hpb := (AdjoinRoot.powerBasis' hm).trace_gen_eq_nextCoeff_minpoly
  rw [AdjoinRoot.powerBasis'_gen, minpoly_root_of_monic hm, allOnes_nextCoeff n hn,
    zmod_two_neg_one] at hpb
  exact hpb
end AllOnesLab
