-- Prove2me | solution 1 for AlonTarsi.outExp_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:29.794175+00:00
-- url     : https://prove2.me/submissions/23f68515-b251-44c7-82a4-8493b0b6e7bf

module
public import Mathlib
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
public import Theorems.Thm_AlonTarsi_sum_single_apply

set_option autoImplicit true
@[expose] public section
public section
open Finset MvPolynomial
open AlonTarsi
variable {V : Type*}
namespace AlonTarsi
theorem _root_.solution [DecidableEq V] (A : Finset (V × V)) (v : V) :
    outExp A v = #{a ∈ A | a.1 = v} :=
  sum_single_apply A Prod.fst v
end AlonTarsi
