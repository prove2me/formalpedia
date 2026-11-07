-- Prove2me | solution 1 for AaronsonAmbainis.markovEndpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:08:43.485917+00:00
-- url     : https://prove2.me/submissions/8f149cad-8d66-4f62-ad9a-3ce5975ad805

import Definitions.Def_AaronsonAmbainis_RowDefs
import Definitions.Def_AaronsonAmbainis_Row_Markov
import Theorems.Thm_AaronsonAmbainis_Row_neg_derivative_eval_zero_le

set_option autoImplicit true
open AaronsonAmbainis
open Polynomial
namespace AaronsonAmbainis
theorem _root_.solution : MarkovEndpoint := by
  intro D p hdeg hbnd
  have h1 := Row.neg_derivative_eval_zero_le D p hdeg hbnd
  have h2 := Row.neg_derivative_eval_zero_le D (-p) (by simpa using hdeg)
    (fun s hs0 hs2 => by simpa using hbnd s hs0 hs2)
  rw [derivative_neg, eval_neg, neg_neg] at h2
  exact abs_le.mpr ⟨by linarith, h2⟩
end AaronsonAmbainis
