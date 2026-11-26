-- Prove2me | solution 1 for AlonTarsi.totalDegree_graphPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:18.311293+00:00
-- url     : https://prove2.me/submissions/3f6839e2-b135-4976-9d87-a08fe7b1c4f3

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial

set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}
namespace AlonTarsi
theorem _root_.solution (A : Finset (V × V)) : (graphPoly A).totalDegree ≤ #A := by
  unfold graphPoly
  refine (totalDegree_finsetProd _ _).trans ?_
  rw [Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (totalDegree_sub _ _).trans ?_
  simp [totalDegree_X]
end AlonTarsi
