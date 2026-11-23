-- Prove2me | solution 1 for Automata.na_FinRun_fixSuffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:32.993817+00:00
-- url     : https://prove2.me/submissions/150349f0-9afe-4ff9-a7ae-8912941538b1

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}
namespace Automata
theorem _root_.solution [Inhabited A] {n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (h : M.FinRun n as ss) : M.FinRun n (fixSuffix as n default) (fixSuffix ss (n + 1) (ss 0)) := by
  rcases h with ⟨h_init, h_next⟩
  constructor
  · simpa [fixSuffix]
  intro k h_k
  simp [fixSuffix, h_k, (by omega : k < n + 1)]
  exact h_next k h_k
end Automata
