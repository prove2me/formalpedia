-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.detInequality_of_lowest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:45:40.61697+00:00
-- url     : https://prove2.me/submissions/88ad2519-a808-4150-878b-cdc0531f5729

import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Definitions.Def_AaronsonAmbainis_DetBij_Main
import Theorems.Thm_AaronsonAmbainis_DetBij_isWing_extWing
import Theorems.Thm_AaronsonAmbainis_DetBij_det_inequality_of_perm
import Theorems.Thm_AaronsonAmbainis_DetBij_exists_perm


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution :
    AaronsonAmbainis.LowestUnit → AaronsonAmbainis.LowestBound → AaronsonAmbainis.DetInequality := by
  intro hU hB
  unfold DetInequality
  intro ι _ _ g ℓ hℓ A hA d hd
  obtain ⟨σ, hσ, hcard⟩ := exists_perm hU hB g (extWing g A) (isWing_extWing g A hA)
  exact det_inequality_of_perm g ℓ hℓ A d hd σ hσ hcard
end AaronsonAmbainis.DetBij
