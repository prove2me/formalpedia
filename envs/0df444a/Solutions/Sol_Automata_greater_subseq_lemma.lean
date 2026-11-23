-- Prove2me | solution 1 for Automata.greater_subseq_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:47:10.921798+00:00
-- url     : https://prove2.me/submissions/dac62008-4bac-4850-9fb1-426289fb500e

import Definitions.Def_AutomataTheory_Languages_RegLang
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma

set_option autoImplicit true
open Function Set Filter Stream'
open scoped Computability
open Classical
attribute [local implicit_reducible] Stream'
open Automata
attribute [local instance_reducible] DA.toNA
variable {A : Type}
namespace Automata
theorem _root_.solution (φ φ' : ℕ → ℕ) (hi : Injective φ') :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ n, φ (σ n) < φ' (σ (n + 1)) := by
  have h_step : ∀ n, ∃ m > n, φ n < φ' m := by
    intro n
    have h_inf : {m | m > n}.Infinite := by
      apply infinite_of_forall_exists_gt ; intro k
      use (k + n + 1) ; simp +instances
    have h_inf' := Infinite.image (injOn_of_injective hi) h_inf
    have h_fin : {m | m ≤ φ n}.Finite := by exact finite_le_nat (φ n)
    obtain ⟨k, ⟨m, h_m, rfl⟩, h_m'⟩ := Infinite.exists_notMem_finite h_inf' h_fin
    simp +instances at h_m h_m' ; use m
  choose f h_f h_φ using h_step
  use (fun k ↦ f^[k] 0) ; constructor
  · apply strictMono_nat_of_lt_succ ; simp +instances [iterate_succ_apply', h_f]
  · simp +instances [iterate_succ_apply', h_φ]
end Automata
