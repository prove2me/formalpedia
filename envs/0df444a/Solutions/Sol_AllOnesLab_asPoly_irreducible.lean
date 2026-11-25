-- Prove2me | solution 1 for AllOnesLab.asPoly_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:49.558103+00:00
-- url     : https://prove2.me/submissions/fe876125-685b-48f8-b942-7116ac75da22

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard
import Theorems.Thm_AllOnesLab_asPoly_natDegree
import Theorems.Thm_AllOnesLab_asPoly_eval
import Theorems.Thm_AllOnesLab_trace_sq_add_self_eq_zero


set_option autoImplicit true
open Polynomial
open AllOnesLab
variable {K : Type*} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
namespace AllOnesLab
theorem _root_.solution (a : K) (ha : Algebra.trace (ZMod 2) K a ≠ 0) :
    Irreducible (asPoly a) := by
  haveI hchar : CharP K 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · simp [Finset.mem_Icc, asPoly_natDegree]
  · intro z hz
    rw [IsRoot, asPoly_eval] at hz
    have h2 : (2 : K) = 0 := by
      exact_mod_cast CharP.cast_eq_zero K 2
    have ha' : a = z ^ 2 + z := by linear_combination hz - (z ^ 2 + z) * h2
    rw [ha'] at ha
    exact ha (trace_sq_add_self_eq_zero z)
end AllOnesLab
