-- Prove2me | solution 1 for AaronsonAmbainis.DetLow.evalMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:28:00.001991+00:00
-- url     : https://prove2.me/submissions/f43c1f05-e598-4d39-a315-49ab77f17363

import Definitions.Def_AaronsonAmbainis_DetLow_Basic
import Definitions.Def_AaronsonAmbainis_DetLow_NonZero
import Theorems.Thm_AaronsonAmbainis_DetLow_evalAt_agMon

set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.DetLow
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetLow
theorem _root_.solution (c : ℝ) (g : Cube ι → Bool) (x z : Ones g) :
    (evalAt c).mapMatrix (agMatrix g) x z = c ^ agCount x.1 z.1 :=
  evalAt_agMon c x.1 z.1
end AaronsonAmbainis.DetLow
