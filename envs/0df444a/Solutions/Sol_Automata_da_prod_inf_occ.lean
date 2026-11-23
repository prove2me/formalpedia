-- Prove2me | solution 1 for Automata.da_prod_inf_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:38:03.469286+00:00
-- url     : https://prove2.me/submissions/5a342006-3160-464f-8bc9-8b163333137b

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd
import Theorems.Thm_inf_occ_proj


set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)
variable [Finite I] [∀ i, Finite (M i).State]
namespace Automata
theorem _root_.solution (as : Stream' A) (i : I) :
    (· i) '' (InfOcc ((DA.Prod M).DetRun as)) =
    InfOcc ((· i) ∘ (DA.Prod M).DetRun as) := by
  apply inf_occ_proj
end Automata
