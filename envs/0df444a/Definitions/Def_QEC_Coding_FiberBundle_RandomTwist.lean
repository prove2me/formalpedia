-- Prove2me | Definitions.Def_QEC_Coding_FiberBundle_RandomTwist
-- name    : QEC_Coding_FiberBundle_RandomTwist
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T20:34:36.443604+00:00
-- url     : https://prove2.me/theorems/601e0189-fad5-4cad-be90-5d7fb0a162c7
-- title:
--   Random Twist
-- statement:
--   Definitions and structural lemmas for Random Twist, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomTwist.lean

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase
import Mathlib.Probability.Distributions.Uniform
set_option autoImplicit false
namespace QEC.Coding.FiberBundle.RandomTwist
open scoped BigOperators
abbrev ChoiceIndex (r typeCount : Nat) :=
  Sum (Fin (3 * r) × Fin (4 * r)) (Fin typeCount)
def ChoiceValue (ell : Nat) {r typeCount : Nat} :
    ChoiceIndex r typeCount → Type
  | Sum.inl _ => Bool
  | Sum.inr _ => Fin (ell - 1)
instance instFintypeChoiceValue
    (ell : Nat) {r typeCount : Nat} :
    ∀ i : ChoiceIndex r typeCount, Fintype (ChoiceValue ell i)
  | Sum.inl _ => by
      change Fintype Bool
      infer_instance
  | Sum.inr _ => by
      change Fintype (Fin (ell - 1))
      infer_instance
abbrev Sample (r typeCount ell : Nat) :=
  ∀ i : ChoiceIndex r typeCount, ChoiceValue ell i
def checkType
    {r : Nat} (typeCount : Nat) [NeZero typeCount]
    (a : Fin (3 * r)) : Fin typeCount :=
  ⟨a.val % typeCount, Nat.mod_lt _ (NeZero.pos typeCount)⟩
def isTail
    {r typeCount ell : Nat}
    (sample : Sample r typeCount ell)
    (a : Fin (3 * r)) (b : Fin (4 * r)) : Bool :=
  sample (Sum.inl (a, b))
def typeTwist
    {r typeCount ell : Nat}
    (sample : Sample r typeCount ell)
    (τ : Fin typeCount) : Fin (ell - 1) :=
  sample (Sum.inr τ)
def connectionIndex
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (sample : Sample r typeCount ell)
    (b : Fin (4 * r)) (a : Fin (3 * r)) : Fin ell :=
  if isTail sample a b then
    ⟨(typeTwist sample (checkType typeCount a)).val + 1, by
      have h :=
        (typeTwist sample (checkType typeCount a)).isLt
      omega⟩
  else
    0
noncomputable def coordinatePMF
    (ell : Nat) [NeZero (ell - 1)]
    {r typeCount : Nat} :
    ∀ i : ChoiceIndex r typeCount, PMF (ChoiceValue ell i)
  | Sum.inl _ =>
      PMF.bernoulli (1 / 2 : NNReal) (by norm_num)
  | Sum.inr _ =>
      PMF.uniformOfFintype (Fin (ell - 1))
noncomputable def distribution
    (r typeCount ell : Nat)
    [NeZero (ell - 1)] :
    PMF (Sample r typeCount ell) :=
  RandomBase.independentProduct (coordinatePMF ell)
def fiberBundleData
    {r typeCount ell : Nat}
    [NeZero typeCount] [NeZero ell] [NeZero (ell - 1)]
    (baseSample : RandomBase.Sample r)
    (twistSample : Sample r typeCount ell) :
    Data
      (Fin (3 * r)) (Fin (4 * r))
      (ZMod (ell * ell)) (ZMod (ell * ell)) :=
  multipleRotationCycleData ell
    (RandomBase.boundary baseSample)
    (connectionIndex twistSample)
end QEC.Coding.FiberBundle.RandomTwist


