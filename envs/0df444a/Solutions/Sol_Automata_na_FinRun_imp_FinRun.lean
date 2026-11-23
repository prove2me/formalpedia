-- Prove2me | solution 1 for Automata.na_FinRun_imp_FinRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:38.909444+00:00
-- url     : https://prove2.me/submissions/335460c7-9ff2-4ab2-8c27-04460c079ad7

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}
namespace Automata
theorem _root_.solution {m n : ℕ} {as : Stream' A} {ss : Stream' M.State}
    (hmn : m < n) (hr : M.FinRun n as ss) : M.FinRun m as ss :=
  ⟨hr.1, (hr.2 · <| ·.trans hmn)⟩
end Automata
