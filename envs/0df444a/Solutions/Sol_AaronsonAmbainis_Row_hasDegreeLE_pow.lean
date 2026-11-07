-- Prove2me | solution 1 for AaronsonAmbainis.Row.hasDegreeLE_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:21:44.628537+00:00
-- url     : https://prove2.me/submissions/e97ebef5-8cc7-4f99-ae89-5b78327fd17d

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_congr
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_const
import Theorems.Thm_AaronsonAmbainis_Row_hasDegreeLE_mul
import Theorems.Thm_AaronsonAmbainis_Row_sgn_false
import Theorems.Thm_AaronsonAmbainis_Row_sgn_true
attribute [local simp] AaronsonAmbainis.Row.sgn_false
attribute [local simp] AaronsonAmbainis.Row.sgn_true



set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {β : Type*} [Fintype β]
namespace AaronsonAmbainis.Row
theorem _root_.solution {f : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) (n : ℕ) :
    HasDegreeLE (fun w => f w ^ n) (n * k) := by
  induction n with
  | zero => exact hasDegreeLE_congr (hasDegreeLE_const 1 _) (fun w => by simp)
  | succ n ih =>
    have h := hasDegreeLE_mul ih hf
    have h' : n * k + k = (n + 1) * k := by ring
    rw [← h']
    exact hasDegreeLE_congr h (fun w => by rw [pow_succ])
end AaronsonAmbainis.Row
