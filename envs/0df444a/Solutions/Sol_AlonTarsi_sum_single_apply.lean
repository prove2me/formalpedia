-- Prove2me | solution 1 for AlonTarsi.sum_single_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:12:29.851877+00:00
-- url     : https://prove2.me/submissions/bf3b3579-c20f-4c94-9c32-49d37151fbc7

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
theorem _root_.solution [DecidableEq V] (s : Finset (V × V)) (g : V × V → V) (v : V) :
    (∑ a ∈ s, Finsupp.single (g a) 1 : V →₀ ℕ) v = #{a ∈ s | g a = v} := by
  rw [Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]
end AlonTarsi
