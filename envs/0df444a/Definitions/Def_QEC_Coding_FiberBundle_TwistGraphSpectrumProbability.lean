-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
-- name    : QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T07:56:23.793627+00:00
-- url     : https://prove2.me/theorems/a1f7a3ef-cb75-4282-8ef3-719c7cc7dcd7
-- title:
--   Twist Graph Spectrum Probability
-- statement:
--   Definitions and structural lemmas for Twist Graph Spectrum Probability, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/TwistGraphSpectrumProbability.lean

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphFourier
import Mathlib.Probability.Moments.SubGaussian
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.TwistGraph
open scoped BigOperators ZMod ENNReal NNReal
local instance instMeasurableSpaceChoiceValue
    (ell : Nat) {r typeCount : Nat}
    (i : RandomTwist.ChoiceIndex r typeCount) :
    MeasurableSpace (RandomTwist.ChoiceValue ell i) := by
  cases i with
  | inl _ =>
      change MeasurableSpace Bool
      infer_instance
  | inr _ =>
      change MeasurableSpace (Fin (ell - 1))
      infer_instance
local instance instMeasurableSingletonClassChoiceValue
    (ell : Nat) {r typeCount : Nat}
    (i : RandomTwist.ChoiceIndex r typeCount) :
    MeasurableSingletonClass (RandomTwist.ChoiceValue ell i) := by
  cases i with
  | inl _ =>
      change MeasurableSingletonClass Bool
      infer_instance
  | inr _ =>
      change MeasurableSingletonClass (Fin (ell - 1))
      infer_instance
noncomputable def typeCharacterValue
    {ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (shiftIndex : Fin (ell - 1)) : Real :=
  2 *
    (ZMod.stdAddChar
      (((shiftIndex.val + 1 : Nat) : ZMod ell) * frequency)).re
noncomputable def sampledTypeCharacter
    {r typeCount ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (τ : Fin typeCount)
    (sample : RandomTwist.Sample r typeCount ell) : Real :=
  typeCharacterValue frequency (RandomTwist.typeTwist sample τ)
noncomputable def centeredSampledTypeCharacter
    {r typeCount ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (τ : Fin typeCount)
    (sample : RandomTwist.Sample r typeCount ell) : Real :=
  sampledTypeCharacter frequency τ sample -
    (-2 / (ell - 1 : Real))
noncomputable def centeredCharacterSum
    {r typeCount ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (sample : RandomTwist.Sample r typeCount ell) : Real :=
  ∑ τ : Fin typeCount,
    centeredSampledTypeCharacter frequency τ sample
def CenteredFrequencyBad
    {r typeCount ell : Nat}
    [NeZero ell]
    (frequency : ZMod ell)
    (sample : RandomTwist.Sample r typeCount ell) : Prop :=
  (typeCount : Real) / 50000 <
    |centeredCharacterSum frequency sample|
def CenteredSpectrumBad
    {r typeCount ell : Nat}
    [NeZero ell]
    (sample : RandomTwist.Sample r typeCount ell) : Prop :=
  ∃ frequency : ZMod ell,
    frequency ≠ 0 ∧ CenteredFrequencyBad frequency sample
end QEC.Coding.FiberBundle.TwistGraph


