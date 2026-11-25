-- Prove2me | Definitions.Def_BayesianPersuasion_Signals
-- name    : BayesianPersuasion_Signals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:57:42.206532+00:00
-- url     : https://prove2.me/theorems/4f98faf2-e6be-4b68-b405-ce4ab3d66a3b
-- title:
--   Signals
-- statement:
--   Definitions and structural lemmas for Signals, from Arthur Freitas Ramos, David Barros Hulak, and Ruy Jose Guerra Barretto de Queiroz; portions adapted from Daniel Lyng Econlib (Apache-2.0; see pinned LICENSE and source headers)'s pinned Optimal information and concavification in Bayesian persuasion development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Signals.lean

module
public import Definitions.Def_BayesianPersuasion_Primitives
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe uΩ uA
open Set Finset
namespace BayesianPersuasion
variable {Ω : Type uΩ} [Fintype Ω]
abbrev Signal (Ω : Type uΩ) [Fintype Ω] (n : ℕ) := Ω → Belief (Fin n)
def noInformationSignal : Signal Ω 1 := fun _ => ⟨fun _ => 1, by simp⟩
def FullSupport (p : Belief Ω) : Prop := ∀ ω, 0 < p.val ω
def BayesPlausible (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) : Prop := ∀ ω, ∑ s, w.val s * (b s).val ω = p.val ω
def signalMass (p : Belief Ω) {n : ℕ} (π : Signal Ω n) (s : Fin n) : ℝ :=
  ∑ ω, p.val ω * (π ω).val s
noncomputable def posteriorVector (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) : Ω → ℝ :=
  if signalMass p π s = 0 then p.val else fun ω => p.val ω * (π ω).val s / signalMass p π s
noncomputable def splittingVector (p : Belief Ω) {n : ℕ} (w : Belief (Fin n))
    (b : Fin n → Belief Ω) (ω : Ω) (s : Fin n) : ℝ := w.val s * (b s).val ω / p.val ω
namespace Proof
theorem signalMass_nonneg (p : Belief Ω) {n : ℕ} (π : Signal Ω n) (s : Fin n) :
    0 ≤ signalMass p π s :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (p.property.1 ω) ((π ω).property.1 s)
theorem signalMass_sum (p : Belief Ω) {n : ℕ} (π : Signal Ω n) :
    ∑ s, signalMass p π s = 1 := by
  unfold signalMass
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (π _).property.2, mul_one]
  exact p.property.2
theorem posteriorVector_isBelief (p : Belief Ω) {n : ℕ} (π : Signal Ω n) (s : Fin n) :
    (∀ ω, 0 ≤ posteriorVector p π s ω) ∧ ∑ ω, posteriorVector p π s ω = 1 := by
  classical
  unfold posteriorVector
  split_ifs with h
  · exact p.property
  · constructor
    · intro ω
      exact div_nonneg (mul_nonneg (p.property.1 ω) ((π ω).property.1 s))
        (signalMass_nonneg p π s)
    · rw [← Finset.sum_div]
      exact div_self h
end Proof
noncomputable def signalWeights (p : Belief Ω) {n : ℕ} (π : Signal Ω n) : Belief (Fin n) :=
  ⟨signalMass p π, Proof.signalMass_nonneg p π, Proof.signalMass_sum p π⟩
noncomputable def signalPosterior (p : Belief Ω) {n : ℕ} (π : Signal Ω n)
    (s : Fin n) : Belief Ω := ⟨posteriorVector p π s, Proof.posteriorVector_isBelief p π s⟩
namespace Proof
theorem splittingVector_isBelief (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) (ω : Ω) :
    (∀ s, 0 ≤ splittingVector p w b ω s) ∧ ∑ s, splittingVector p w b ω s = 1 := by
  constructor
  · intro s
    exact div_nonneg (mul_nonneg (w.property.1 s) ((b s).property.1 ω)) (hp ω).le
  · unfold splittingVector
    rw [← Finset.sum_div, hb ω, div_self (ne_of_gt (hp ω))]
end Proof
noncomputable def splittingSignal (p : Belief Ω) (hp : FullSupport p) {n : ℕ}
    (w : Belief (Fin n)) (b : Fin n → Belief Ω) (hb : BayesPlausible p w b) : Signal Ω n :=
  fun ω => ⟨splittingVector p w b ω, Proof.splittingVector_isBelief p hp w b hb ω⟩
namespace Proof
end Proof
end BayesianPersuasion


