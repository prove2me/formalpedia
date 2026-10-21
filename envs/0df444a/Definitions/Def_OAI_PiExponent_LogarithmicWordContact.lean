-- Prove2me | Definitions.Def_OAI_PiExponent_LogarithmicWordContact
-- name    : OAI_PiExponent_LogarithmicWordContact
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-21T03:41:15.07519+00:00
-- url     : https://prove2.me/theorems/fa20dace-9f90-4665-b436-f231ecab2e20
-- title:
--   Weighted logarithmic jets and polynomial frame words
-- statement:
--   Defines polynomial weighted support bounds, strict weighted vanishing of the existing formal logarithmic jets, the logarithmic polynomial frame and its iterated words, and additive word costs. Existing ideal, jet, place, and contact definitions are reused unchanged.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators

noncomputable section
namespace OAI.PiExponent.FormalInterpolation

/-- Weighted support bound, with a real height and rational positive weights. -/
def logarithmicDegreeBound {d : Nat} (w : Fin d → Rat) (H : Real)
    (F : MvPolynomial (Fin d) Complex) : Prop :=
  ∀ a ∈ F.support, (∑ i, (w i : Real) * (a i : Real)) ≤ H

/-- Every formal logarithmic jet has no coefficient of weight strictly below H. -/
def logarithmicJetBound {m K : Nat} (c : Fin K → Fin m → Complex)
    (v : Fin (m + 1) → Rat) (H : Real)
    (F : MvPolynomial (Fin (m + 1)) Complex) : Prop :=
  ∀ j (a : Fin (m + 1) →₀ Nat),
    (∑ i, (v i : Real) * (a i : Real)) < H →
      MvPowerSeries.coeff a (formalJet (c j) F) = 0

/-- The polynomial logarithmic frame: Y*d/dY + sum_i d/dX_i, and d/dX_i. -/
def logarithmicFrameDerivative {m : Nat} (i : Fin (m + 1))
    (F : MvPolynomial (Fin (m + 1)) Complex) :
    MvPolynomial (Fin (m + 1)) Complex :=
  Fin.cases
    (MvPolynomial.X 0 * MvPolynomial.pderiv 0 F +
      ∑ j : Fin m, MvPolynomial.pderiv j.succ F)
    (fun j => MvPolynomial.pderiv j.succ F) i

def logarithmicFrameWord {m : Nat} :
    List (Fin (m + 1)) → MvPolynomial (Fin (m + 1)) Complex →
      MvPolynomial (Fin (m + 1)) Complex
  | [], F => F
  | i :: word, F => logarithmicFrameDerivative i (logarithmicFrameWord word F)

def logarithmicFrameCost {m : Nat} (v : Fin (m + 1) → Rat)
    (word : List (Fin (m + 1))) : Real :=
  (word.map (fun i => (v i : Real))).sum

end OAI.PiExponent.FormalInterpolation


