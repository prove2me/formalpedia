-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.variance_ev01_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:58.95228+00:00
-- url     : https://prove2.me/submissions/cdf555e2-7c61-4f9b-b38f-7041ec84bfdd

import Definitions.Def_AaronsonAmbainis_Bridge_Capstone
import Definitions.Def_AaronsonAmbainis_Bridge_Instance
import Theorems.Thm_AaronsonAmbainis_Bridge_ev01_X_eq_affine
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_affine
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_dict


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial
namespace AaronsonAmbainis.Bridge
theorem _root_.solution {N : ℕ} (i : Fin N) :
    variance (ev01 (MvPolynomial.X i : MvPolynomial (Fin N) ℝ) : Cube (Fin N) → ℝ) = 1 / 4 := by
  rw [ev01_X_eq_affine, variance_affine (1 / 2) (-1 / 2) (dict i), variance_dict]
  norm_num
end AaronsonAmbainis.Bridge
