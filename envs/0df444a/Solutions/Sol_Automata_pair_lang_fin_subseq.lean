-- Prove2me | solution 1 for Automata.pair_lang_fin_subseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:44:43.569921+00:00
-- url     : https://prove2.me/submissions/a6854fc9-24a9-4b15-9720-5105c473d70a

import Definitions.Def_AutomataTheory_Automata_Hist
import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Pair
import Theorems.Thm_P2M_Stream__get_extract__ebf059d6908b


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] NA.addHist
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution {as : Stream' A} {ss : Stream' M.State} {m n : ℕ}
    (h_next : ∀ k, ss (k + 1) ∈ M.next (ss k) (as k)) (h_m_n : m ≤ n) :
    as.extract m n ∈ M.PairLang (ss m) (ss n) := by
  use (fun k ↦ ss (k + m))
  simp (disch := omega) [NA.PairPath, length_extract, get_extract', (show n - m + m = n by omega)]
  intro k h_k ; grind
end Automata
