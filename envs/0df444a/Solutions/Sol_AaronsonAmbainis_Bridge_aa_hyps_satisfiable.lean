-- Prove2me | solution 1 for AaronsonAmbainis.Bridge.aa_hyps_satisfiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:32:19.174922+00:00
-- url     : https://prove2.me/submissions/bc66fefd-8922-4d4c-8c34-08befd5f2bcc

import Definitions.Def_AaronsonAmbainis_Statements
import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Theorems.Thm_AaronsonAmbainis_Bridge_aa_hyps_dict

set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.Bridge
theorem _root_.solution :
    ∃ f : Cube (Fin 1) → ℝ, (∀ x, |f x| ≤ 1) ∧ HasDegreeLE f 1 ∧ 0 < variance f ∧
      variance f = 1 ∧ inflR f 0 = 1 :=
  ⟨dict 0, aa_hyps_dict 0⟩
end AaronsonAmbainis.Bridge
