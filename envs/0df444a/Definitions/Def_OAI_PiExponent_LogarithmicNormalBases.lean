-- Prove2me | Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
-- name    : OAI_PiExponent_LogarithmicNormalBases
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-23T23:13:51.881366+00:00
-- url     : https://prove2.me/theorems/e40033ce-ad00-40e1-877a-6bb2917f1364
-- title:
--   Generic-point coordinate and logarithmic normal bases
-- statement:
--   For a prime polynomial ideal P, use the fraction field of its quotient. Each coordinate or frame direction gives a column whose entries are the corresponding derivatives of every equation in P, evaluated in that field. A selected finite index set is a normal basis when its columns are linearly independent and span the same space as all columns. These definitions encode generic normal directions without selecting a closed point or introducing curve-place hypotheses.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Derivation.Basic

open scoped BigOperators

noncomputable section
namespace OAI.PiExponent.FormalInterpolation

/-- Function field of the affine component defined by a prime ideal.
The abbreviation itself is also defined for nonprime ideals. -/
abbrev logarithmicPrimeField {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) :=
  FractionRing (MvPolynomial (Fin (m + 1)) Complex ⧸ P)

/-- A coordinate direction, tested on every equation of the component. -/
def coordinateNormalColumnAtPrime {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (i : Fin (m + 1)) : P → logarithmicPrimeField P :=
  fun F => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
    (logarithmicPrimeField P) (MvPolynomial.pderiv i (F : MvPolynomial _ Complex))

/-- A logarithmic frame direction, tested on every equation of the component. -/
def logarithmicNormalColumnAtPrime {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (i : Fin (m + 1)) : P → logarithmicPrimeField P :=
  fun F => algebraMap (MvPolynomial (Fin (m + 1)) Complex)
    (logarithmicPrimeField P) (logarithmicFrameDerivative i (F : MvPolynomial _ Complex))

/-- The selected coordinate columns are a basis of the span of all columns.
Thus this is a normal basis at the generic point, rather than at a
possibly singular closed point. -/
def coordinateNormalBasisAtPrime {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (A : Finset (Fin (m + 1))) : Prop :=
  LinearIndependent (logarithmicPrimeField P)
      (fun i : A => coordinateNormalColumnAtPrime P i) ∧
    Submodule.span (logarithmicPrimeField P)
        (Set.range (fun i : A => coordinateNormalColumnAtPrime P i)) =
      Submodule.span (logarithmicPrimeField P)
        (Set.range (coordinateNormalColumnAtPrime P))

/-- The selected logarithmic frame columns are a basis of the span of all
frame columns. On the open set Y ≠ 0 this span has the same rank as the
coordinate-column span. -/
def logarithmicNormalBasisAtPrime {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (B : Finset (Fin (m + 1))) : Prop :=
  LinearIndependent (logarithmicPrimeField P)
      (fun i : B => logarithmicNormalColumnAtPrime P i) ∧
    Submodule.span (logarithmicPrimeField P)
        (Set.range (fun i : B => logarithmicNormalColumnAtPrime P i)) =
      Submodule.span (logarithmicPrimeField P)
        (Set.range (logarithmicNormalColumnAtPrime P))

end OAI.PiExponent.FormalInterpolation


