-- Prove2me | solution 1 for AlonTarsi.degree_outExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:14.32748+00:00
-- url     : https://prove2.me/submissions/908d39cb-4930-4d8a-925e-9a53fdae0b12

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
theorem _root_.solution (A : Finset (V × V)) : (outExp A).degree = #A := by
  classical
  unfold outExp
  rw [map_sum]
  simp [Finsupp.degree_single]
end AlonTarsi
