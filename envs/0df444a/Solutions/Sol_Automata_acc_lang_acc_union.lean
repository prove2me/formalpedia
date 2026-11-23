-- Prove2me | solution 1 for Automata.acc_lang_acc_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:44.408456+00:00
-- url     : https://prove2.me/submissions/24e4c1cc-60ee-4366-87d2-149ee31d4b7a

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}
namespace Automata
theorem _root_.solution {acc0 acc1 : Set M.State} :
    M.AcceptedLang (acc0 ∪ acc1) = M.AcceptedLang acc0 ∪ M.AcceptedLang acc1 := by
  ext al ; constructor
  · rintro ⟨n, as, ⟨ss, h_run, (h_acc0 | h_acc1)⟩, h_al⟩
    · left ; use n, as ; simp [h_al] ; use ss
    · right ; use n, as ; simp [h_al] ; use ss
  · rintro (⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩ | ⟨n, as, ⟨ss, h_run, h_acc⟩, h_al⟩)
    · use n, as ; simp [h_al] ; use ss ; simp [h_run, h_acc]
    · use n, as ; simp [h_al] ; use ss ; simp [h_run, h_acc]
end Automata
