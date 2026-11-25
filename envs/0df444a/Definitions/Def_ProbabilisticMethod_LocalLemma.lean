-- Prove2me | Definitions.Def_ProbabilisticMethod_LocalLemma
-- name    : ProbabilisticMethod_LocalLemma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:59:29.497079+00:00
-- url     : https://prove2.me/theorems/5802aefe-5341-5b44-855c-66523f06555c
-- title:
--   Local Lemma
-- statement:
--   Definitions and structural lemmas for Local Lemma, from Brian Sanders (Egly443/lean-probabilistic-method; see pinned Apache-2.0 LICENSE and source headers)'s pinned The finite probabilistic method for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset Real
namespace Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
section Basic
variable (U p)
variable {U p}
end Basic
section Weights
variable {β : Type*}
noncomputable def weightProb (Ω : Finset β) (w : β → ℝ) (P : β → Prop) [DecidablePred P] : ℝ :=
  ∑ a ∈ Ω with P a, w a
variable {Ω : Finset β} {w : β → ℝ}
end Weights
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
def Avoids (S : Finset ι) (a : β) : Prop := ∀ j ∈ S, ¬E j a
instance (S : Finset ι) : DecidablePred (Avoids E S) := fun _ =>
  inferInstanceAs (Decidable (∀ j ∈ S, _))
variable {E}
def LopsidedWeights (Ω : Finset β) (w : β → ℝ) (I : Finset ι) (E : ι → β → Prop)
    [∀ i, DecidablePred (E i)] (Γ : ι → Finset ι) : Prop :=
  ∀ i ∈ I, ∀ S ⊆ I, Disjoint S (Γ i) → i ∉ S →
    Ω.weightProb w (fun a => E i a ∧ Avoids E S a) ≤
      Ω.weightProb w (E i) * Ω.weightProb w (Avoids E S)
def Lopsided (U : Finset α) (p : ℝ) (I : Finset ι) (E : ι → Finset α → Prop)
    [∀ i, DecidablePred (E i)] (Γ : ι → Finset ι) : Prop :=
  ∀ i ∈ I, ∀ S ⊆ I, Disjoint S (Γ i) → i ∉ S →
    U.bernoulliProb p (fun A => E i A ∧ Avoids E S A) ≤
      U.bernoulliProb p (E i) * U.bernoulliProb p (Avoids E S)
section Weights
variable {Ω : Finset β} {w : β → ℝ}
end Weights
variable {E : ι → Finset α → Prop} [∀ i, DecidablePred (E i)]
end Finset


