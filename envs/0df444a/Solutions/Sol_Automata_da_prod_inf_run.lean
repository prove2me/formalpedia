-- Prove2me | solution 1 for Automata.da_prod_inf_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:25:39.546801+00:00
-- url     : https://prove2.me/submissions/b844b0e8-8bc1-44a1-84b9-0a22aaea72ca

import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_DetProd

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {I A : Type}
variable (M : I → DA A)
namespace Automata
theorem _root_.solution (as : Stream' A) (i : I) :
    (· i) ∘ (DA.Prod M).DetRun as = (M i).DetRun as := by
  ext k
  induction' k with k h_ind
  · simp [DA.DetRun] ; rfl
  · simp [DA.DetRun, ← h_ind] ; rfl
end Automata
