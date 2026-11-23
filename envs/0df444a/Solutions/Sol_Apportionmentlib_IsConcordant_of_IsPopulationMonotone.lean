-- Prove2me | solution 1 for Apportionmentlib.IsConcordant_of_IsPopulationMonotone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:41:26.509038+00:00
-- url     : https://prove2.me/submissions/367ab53e-3a9b-486f-8c5d-2f9279eae13b

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Rat.Floor
public import Definitions.Def_Apportionmentlib_Utils
public import Definitions.Def_Apportionmentlib_Basic

set_option autoImplicit false
@[expose] public section
public section
open BigOperators
open Apportionmentlib
namespace Apportionmentlib
theorem _root_.solution (rule : Rule) [h_anon : IsAnonymous rule]
    [h_mono : IsPopulationMonotone rule] : IsConcordant rule := by
  constructor
  intro n e i j h_votes App h_App
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  let e' : Election n := e.mkByPerm σ
  let App' := Vector.ofFn fun r => App[σ r]
  replace h_anon := h_anon.anonymous e σ App'
  have h_App' : App' ∈ rule.res e' := by
    rw [h_anon]
    use App
    exact ⟨h_App, by aesop⟩
  have h_p' : e'.votes[i] = e.votes[j] := by aesop
  have h_q' : e'.votes[j] = e.votes[i] := by aesop
  replace h_mono := h_mono.population_monotone e e' i j (by trivial)
  rw [h_p', h_q', ← pow_two, ← pow_two] at h_mono
  specialize h_mono (Nat.pow_lt_pow_left h_votes (by decide)) App h_App App' h_App'
  aesop
end Apportionmentlib
