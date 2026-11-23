-- Prove2me | solution 1 for Automata.det_muller_accept_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:40:28.764807+00:00
-- url     : https://prove2.me/submissions/29d67deb-25af-4870-99f4-8f7da85d6826

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
    (DA.Prod M).MullerAccept (DA.MullerAcc_Union M accSet) as ↔
    ∃ i : I, (M i).MullerAccept (accSet i) as := by
  simp [DA.MullerAccept, DA.MullerAcc_Union] ; constructor
  · rintro ⟨i, h_acc⟩ ; use i
    simpa [← da_prod_inf_run M as i, ← da_prod_inf_occ M as i]
  · rintro ⟨i, h_acc⟩ ; use i
    simpa [da_prod_inf_occ M as i, da_prod_inf_run M as i]
end Automata
