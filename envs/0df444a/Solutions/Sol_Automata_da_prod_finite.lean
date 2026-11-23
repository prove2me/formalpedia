-- Prove2me | solution 1 for Automata.da_prod_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:26:04.490691+00:00
-- url     : https://prove2.me/submissions/fb4e6761-f44d-476a-a58b-484d865eb22b

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)
variable [Finite I] [∀ i, Finite (M i).State]
namespace Automata
theorem _root_.solution :
    Finite (DA.Prod M).State := by
  exact Pi.finite
end Automata
