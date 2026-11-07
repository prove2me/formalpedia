-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.aa_hyps_dict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:31.608368+00:00
-- url     : https://prove2.me/submissions/e0c9eae1-471e-4d57-bb74-7212b26ba5ea

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_abs_le_one
import Theorems.Thm_AaronsonAmbainis_Bridge_dict_hasDegreeLE_one
import Theorems.Thm_AaronsonAmbainis_Bridge_variance_dict
import Theorems.Thm_AaronsonAmbainis_Bridge_inflR_dict_self

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution (j : ι) :
    (∀ x, |dict j x| ≤ 1) ∧ HasDegreeLE (dict j) 1 ∧ 0 < variance (dict j) ∧
      variance (dict j) = 1 ∧ inflR (dict j) j = 1 :=
  ⟨dict_abs_le_one j, dict_hasDegreeLE_one j, by rw [variance_dict]; norm_num,
    variance_dict j, inflR_dict_self j⟩
end AaronsonAmbainis.Bridge
