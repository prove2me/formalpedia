-- Prove2me | Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
-- name    : OAI_PiExponent_FibreContactAuxiliaryData
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-21T09:43:47.915834+00:00
-- url     : https://prove2.me/theorems/6abf3689-f6bc-4d0e-804e-e9e74c9bb21a
-- title:
--   Ordinary weighted polynomial jets and derivative words
-- statement:
--   Defines weighted support bounded by N, ordinary translated Taylor coefficients vanishing strictly below H, iterated partial derivatives indexed by words, and their additive jet costs.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Cast.Order

open scoped BigOperators

noncomputable section
namespace OAI.PiExponent.FormalInterpolation

/-- A support bound, with the closed degree cutoff. -/
def fibreContactSupportBound {n : Nat} (W : Fin n → Rat) (N : Nat)
    (F : MvPolynomial (Fin n) Complex) : Prop :=
  ∀ a ∈ F.support,
    (∑ i : Fin n, (a i : Real) * (W i : Real)) ≤ (N : Real)

/-- Ordinary Taylor coefficients vanish strictly below the given jet weight. -/
def fibreContactJetVanishing {n K : Nat} (c : Fin K → Fin n → Complex)
    (V : Fin n → Rat) (H : Real)
    (F : MvPolynomial (Fin n) Complex) : Prop :=
  ∀ (j : Fin K) (a : Fin n →₀ Nat),
    (∑ i : Fin n, (a i : Real) * (V i : Real)) < H →
      (MvPolynomial.aeval
        (fun i => MvPolynomial.C (c j i) + MvPolynomial.X i) F).coeff a = 0

/-- Successive ordinary partial derivatives; the empty word is the identity. -/
def fibreContactWord {n : Nat} (word : List (Fin n))
    (F : MvPolynomial (Fin n) Complex) : MvPolynomial (Fin n) Complex :=
  word.foldr (fun i P => MvPolynomial.pderiv i P) F

/-- The additive jet cost of a derivative word. -/
def fibreContactWordCost {n : Nat} (V : Fin n → Rat) (word : List (Fin n)) : Real :=
  (word.map (fun i => (V i : Real))).sum

end OAI.PiExponent.FormalInterpolation


