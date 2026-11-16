-- Prove2me | Definitions.Def_Kyprianou_Ch05_RegularVariation
-- name    : Kyprianou_Ch05_RegularVariation
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:25:03.347493+00:00
-- url     : https://prove2.me/theorems/419e23d0-f26d-431e-9857-c7ae6f3dff7d
-- title:
--   Definition 5.12 and Laplace/renewal notation
-- statement:
--   Regular variation at zero and infinity with exact positive-function ratios, slowly varying factors, extended-real Laplace transform of a nonnegative measure and its cumulative measure. Theorem 5.12 is a definition, not an unproved theorem.
-- source:
--   Kyprianou (2006), first edition, Definition 5.12 (p. 126), renewal and q-potential notation on pp. 112-114.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Regular variation at infinity for a positive function, Definition 5.12. -/
def RegularlyVaryingAtInfinity (f : Real → Real) (rho : Real) : Prop :=
  (∀ x : Real, 0 < x → 0 < f x) ∧
  ∀ lambda : Real, 0 < lambda →
    Tendsto (fun x : Real => f (lambda * x) / f x)
      atTop (nhds (lambda ^ rho))

/-- Regular variation at zero for a positive function, Definition 5.12. -/
def RegularlyVaryingAtZero (f : Real → Real) (rho : Real) : Prop :=
  (∀ x : Real, 0 < x → 0 < f x) ∧
  ∀ lambda : Real, 0 < lambda →
    Tendsto (fun x : Real => f (lambda * x) / f x)
      (nhdsWithin (0 : Real) (Set.Ioi 0))
      (nhds (lambda ^ rho))

/-- Slowly varying factors have index zero. -/
def SlowlyVaryingAtInfinity (f : Real → Real) : Prop :=
  RegularlyVaryingAtInfinity f 0

/-- The nonnegative Laplace transform, with explicit extended-real integral. -/
noncomputable def positiveLaplace (U : Measure Real) (theta : Real) : ENNReal :=
  ∫⁻ x : Real, ENNReal.ofReal (Real.exp (-theta * x)) ∂U

/-- Renewal/potential mass of the closed interval from zero. -/
noncomputable def cumulativePotential (U : Measure Real) (x : Real) : ENNReal :=
  U (Set.Icc (0 : Real) x)

end Kyprianou.Ch05


