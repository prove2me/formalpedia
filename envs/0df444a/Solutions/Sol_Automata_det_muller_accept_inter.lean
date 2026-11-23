-- Prove2me | solution 1 for Automata.det_muller_accept_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:06.818335+00:00
-- url     : https://prove2.me/submissions/8ba8f969-635f-41bb-9d0a-9e33c5c3258d

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd
import Theorems.Thm_Automata_da_prod_inf_run
import Theorems.Thm_Automata_da_prod_inf_occ

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)
variable [Finite I] [∀ i, Finite (M i).State]
variable (accSet : (i : I) → Set (Set (M i).State))
namespace Automata
theorem _root_.solution (as : Stream' A) :
    (DA.Prod M).MullerAccept (DA.MullerAcc_Inter M accSet) as ↔
    ∀ i : I, (M i).MullerAccept (accSet i) as := by
  simp [DA.MullerAccept, DA.MullerAcc_Inter] ; constructor
  · intro h_acc i ; specialize h_acc i
    simpa [← da_prod_inf_run M as i, ← da_prod_inf_occ M as i]
  · intro h_acc i ; specialize h_acc i
    simpa [da_prod_inf_occ M as i, da_prod_inf_run M as i]
end Automata
