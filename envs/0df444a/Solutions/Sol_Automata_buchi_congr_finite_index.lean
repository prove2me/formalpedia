-- Prove2me | solution 1 for Automata.buchi_congr_finite_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:50:50.760913+00:00
-- url     : https://prove2.me/submissions/681eb549-c0c8-41b3-89ba-b91e6004e519

import Definitions.Def_AutomataTheory_Automata_Pair
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Theorems.Thm_Automata_buchi_congr_param_surjective

set_option autoImplicit true
open Function Set Filter Stream'
open Automata
attribute [local instance_reducible] NA.BuchiCongr
open Classical
variable {A : Type}
variable {M : NA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution [Finite M.State] : Finite (M.BuchiCongr acc).QuotType := by
  exact Finite.of_surjective (M.BuchiCongrParam acc) buchi_congr_param_surjective
end Automata
