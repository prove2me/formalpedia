-- Prove2me | solution 1 for Automata.choueka_lang_omega_power_eq_omega_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:53:02.415353+00:00
-- url     : https://prove2.me/submissions/c427d2c1-07ee-44a6-933c-75ef371483e9

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Theorems.Thm_Automata_choueka_lang_omega_limit_subset_omega_power
import Theorems.Thm_Automata_choueka_lang_omega_power_subset_omega_limit
import Theorems.Thm_ConcatInf_IterStar_IterOmega
import Theorems.Thm_ConcatInf_mono
import Theorems.Thm_IterOmega_IterStar


set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}
namespace Automata
theorem _root_.solution [Inhabited A]
    {M : DA A} [Finite M.State] {acc : Set M.State}
    {V : Set (List A)} (h_lang : M.toNA.AcceptedLang acc = V∗) :
    V^ω = V∗ * (M.ChouekaLang acc)↗ω := by
  apply Subset.antisymm
  · apply choueka_lang_omega_power_subset_omega_limit h_lang
  · have h1 : (M.ChouekaLang acc)↗ω ⊆ (V∗)^ω := by
      rw [← h_lang] ; apply choueka_lang_omega_limit_subset_omega_power
    have h2 : V∗ * (M.ChouekaLang acc)↗ω ⊆ V∗ * (V∗)^ω := by
      exact ConcatInf_mono (by simp) h1
    rw [IterOmega_IterStar, ConcatInf_IterStar_IterOmega] at h2
    exact h2
end Automata
