-- Prove2me | solution 1 for AlonTarsi.eval_graphPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:46.673843+00:00
-- url     : https://prove2.me/submissions/3cd04d92-0224-406e-88ba-50c7821f802f

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
theorem _root_.solution (A : Finset (V × V)) (x : V → ℤ) :
    eval x (graphPoly A) = ∏ a ∈ A, (x a.1 - x a.2) := by
  simp [graphPoly, map_prod]
end AlonTarsi
