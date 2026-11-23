-- Prove2me | solution 1 for Automata.da_acc_omega_lang
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:22:48.688904+00:00
-- url     : https://prove2.me/submissions/df275be5-16ea-4e88-a4b8-ab528111306e

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_InfOcc
import Definitions.Def_AutomataTheory_Automata_Det
import Theorems.Thm_Automata_da_inf_run_exists
import Theorems.Thm_Automata_da_fin_run_unique
import Theorems.Thm_Automata_na_FinRun_modulo
import Theorems.Thm_Automata_na_InfRun_iff_FinRun
import Theorems.Thm_P2M_Stream__extract_eq_extract_14275bcbb551
import Theorems.Thm_frequently_iff_strict_mono


set_option autoImplicit true
open Function Set Filter Stream'
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type} {M : DA A} {acc : Set M.State}
namespace Automata
theorem _root_.solution :
    M.toNA.AcceptedOmegaLang acc = (M.toNA.AcceptedLang acc)↗ω := by
  ext as ; constructor
  · rintro ⟨ss, h_run, h_inf⟩
    obtain ⟨φ, h_mono, h_acc⟩ := frequently_iff_strict_mono.mp h_inf
    apply frequently_iff_strict_mono.mpr
    use φ ; simp +instances [h_mono] ; intro m
    use (φ m), as ; constructor <;> [skip ; rfl]
    use ss ; simp +instances [h_acc]
    exact na_InfRun_iff_FinRun.mp h_run (φ m)
  · simp +instances only [instOmegaLimit, OmegaLimit, frequently_iff_strict_mono, mem_setOf_eq]
    rintro ⟨φ, h_mono, h_acc⟩
    use (M.DetRun as) ; constructor
    · apply da_inf_run_exists
    apply frequently_iff_strict_mono.mpr
    use φ ; simp +instances [h_mono] ; intro m
    obtain ⟨n, as', ⟨ss, h_run', h_acc'⟩, h_as'⟩ := h_acc m
    have h_as' := extract_eq_extract h_as' ; simp +instances at h_as'
    obtain ⟨rfl, h_as'⟩ := h_as'
    have h_run : M.toNA.FinRun (φ m) as ss := na_FinRun_modulo
      (M := M.toNA) (n := φ m) (as := as') (as' := as) (ss := ss) (ss' := ss) (by grind) (by grind) h_run'
    have := da_fin_run_unique h_run (φ m) (by omega)
    simp_all
end Automata
