-- Prove2me | Definitions.Def_PdzPrelim
-- name    : PdzPrelim
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-17T01:34:42.441348+00:00
-- url     : https://prove2.me/theorems/4cc58030-51bc-49c8-a9a2-29f957f0bfae
-- title:
--   Real-algebraic-geometry vocabulary and elimination toolkit
-- statement:
--   The shared vocabulary and elimination machinery for the Pach–de Zeeuw real-algebraic-geometry layer: the Euclidean plane model, plane-curve zero sets and bounded-degree/irreducible predicates, the `Curry0` currying of a bivariate polynomial to a univariate polynomial over the coefficient ring, specializations, resultants, coefficient-root sets and common-zero fibers, plus the typeclass instances that make the coefficient ring behave (`IsPrincipalIdealRing`, `NormalizedGCDMonoid`). Everything the mission's theorems quantify over is defined here.
-- source:
--   Definitions supporting the formalization of Pach–de Zeeuw, Distinct distances on algebraic curves in the plane (arXiv:1308.0177), Theorem 2.1; definition bundle skeleton-subtracted from https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L21-L1629

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Pach--de Zeeuw algebraic preliminaries

This file houses the statement-level algebraic-geometry vocabulary used by the
later PDZ cards. The real work remains the algebraic proofs/adapters; the goal
here is to fix the Lean surface in the local project namespace.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

/-- The Euclidean plane `ℝ²` (real inner-product space of dimension 2). -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)



/-! ### Curve vocabulary

The plane-curve predicates these lemmas range over. (Inlined here in the
`PlaneCurve` namespace so the file is self-contained and mathlib-only.) -/

namespace PlaneCurve

/-- `C` is the real zero set of a nonzero bivariate polynomial of total degree
at most `k`. -/
def IsBoundedDegreeCurve (k : ℕ) (C : Set Point2) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ, p ≠ 0 ∧ p.totalDegree ≤ k ∧
    C = {x : Point2 | MvPolynomial.eval (fun i ↦ x i) p = 0}

/-- `C` is the real zero set of a nonzero **irreducible** bivariate polynomial of
total degree at most `k`. -/
def IsIrreducibleCurve (k : ℕ) (C : Set Point2) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ, p ≠ 0 ∧ p.totalDegree ≤ k ∧ Irreducible p ∧
    C = {x : Point2 | MvPolynomial.eval (fun i ↦ x i) p = 0}





end PlaneCurve

open EuclideanGeometry
open scoped Topology

/--
Two bounded-degree real plane curves have no shared infinite irreducible curve
component. This is not the Bezout conclusion: it does not assert that
`C₁ ∩ C₂` is finite or bounded.
-/
def NoCommonCurveComponent (C₁ C₂ : Set Point2) : Prop :=
  ¬ ∃ e : ℕ, ∃ C : Set Point2,
    PlaneCurve.IsIrreducibleCurve e C ∧ C.Infinite ∧ C ⊆ C₁ ∧ C ⊆ C₂

/-- Theorem 2.1, Bezout finite-intersection bound for plane curves. This is the
existential / finite-intersection consequence of Bézout's inequality (Theorem 2.1):
it asserts only that some degree-dependent bound `C` exists, a weaker statement than
the sharp `≤ d₁·d₂` count that is Theorem 2.1's full form. -/
def BezoutFiniteIntersectionStatement : Prop :=
  ∀ d₁ d₂ : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ C₁ C₂ : Set Point2,
      PlaneCurve.IsBoundedDegreeCurve d₁ C₁ →
      PlaneCurve.IsBoundedDegreeCurve d₂ C₂ →
      NoCommonCurveComponent C₁ C₂ →
      (C₁ ∩ C₂).Finite ∧ (C₁ ∩ C₂).ncard ≤ C









/-! ## Bezout helper layer -/

/-- The real zero set of a bivariate polynomial on the plane. -/
def PlaneCurveZeroSet (p : MvPolynomial (Fin 2) ℝ) : Set Point2 :=
  {x | MvPolynomial.eval (fun i => x i) p = 0}



/-- The polynomial has an infinite real zero set. -/
def HasInfiniteRealZeroSet (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  (PlaneCurveZeroSet p).Infinite

/-- A common irreducible factor with infinite real zero set. -/
def HasCommonInfiniteIrreducibleFactor
    (p q : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∃ h : MvPolynomial (Fin 2) ℝ,
    Irreducible h ∧ HasInfiniteRealZeroSet h ∧ h ∣ p ∧ h ∣ q





/-- The coefficient ring used in the Bézout proof: univariate real polynomials. -/
abbrev XCoeff := MvPolynomial (Fin 1) ℝ

/-- Fraction field of the coefficient ring used in the Bézout proof. -/
abbrev XFrac := FractionRing XCoeff

/-- View a bivariate polynomial as a univariate polynomial in the first variable. -/
noncomputable def Curry0
    (p : MvPolynomial (Fin 2) ℝ) : Polynomial XCoeff :=
  MvPolynomial.finSuccEquiv ℝ 1 p



/-- Evaluate a coefficient-ring polynomial at a real coefficient value. -/
def coeffEval (x : ℝ) : XCoeff →+* ℝ :=
  MvPolynomial.eval (fun _ : Fin 1 => x)

/-- Identify the coefficient ring with ordinary univariate real polynomials. -/
noncomputable def XCoeffEquiv : XCoeff ≃+* Polynomial ℝ :=
  (MvPolynomial.finSuccEquiv ℝ 0).toRingEquiv.trans
    (Polynomial.mapEquiv ((MvPolynomial.isEmptyAlgEquiv ℝ (Fin 0)).toRingEquiv))

/-- Transport the principal ideal ring structure from `Polynomial ℝ` to `XCoeff`. -/
noncomputable instance : IsPrincipalIdealRing XCoeff := by
  refine IsPrincipalIdealRing.of_surjective XCoeffEquiv.symm ?_
  exact XCoeffEquiv.symm.surjective

/-- Transport the normalization monoid structure from `Polynomial ℝ` to `XCoeff`. -/
noncomputable instance : NormalizationMonoid XCoeff := by
  letI : NormalizationMonoid (Polynomial ℝ) := Polynomial.normalizedGcdMonoid.toNormalizationMonoid
  refine
    { normUnit := fun x =>
        Units.map XCoeffEquiv.symm.toMonoidHom
          (NormalizationMonoid.normUnit (XCoeffEquiv x))
      normUnit_zero := by
        simp [XCoeffEquiv]
      normUnit_one := by
        simp [XCoeffEquiv]
      normUnit_mul_units := by
        intro a u ha
        have ha' : XCoeffEquiv a ≠ 0 := by
          intro h0
          exact ha (XCoeffEquiv.injective (by simpa using h0))
        have hunit :=
          NormalizationMonoid.normUnit_mul_units (α := Polynomial ℝ)
            (Units.map XCoeffEquiv.toMonoidHom u) ha'
        have hmap :
            Units.map XCoeffEquiv.symm.toMonoidHom
                (Units.map XCoeffEquiv.toMonoidHom u) = u := by
          have hmap_val :
              ((Units.map XCoeffEquiv.symm.toMonoidHom
                  (Units.map XCoeffEquiv.toMonoidHom u) : XCoeffˣ) : XCoeff) = ↑u := by
            change XCoeffEquiv.symm (XCoeffEquiv ↑u) = ↑u
            exact XCoeffEquiv.left_inv ↑u
          apply Units.ext
          exact hmap_val
        have hcongr :=
          congrArg (Units.map XCoeffEquiv.symm.toMonoidHom) hunit
        have hmapInv :
            Units.map XCoeffEquiv.symm.toMonoidHom
              ((Units.map XCoeffEquiv.toMonoidHom u)⁻¹) = u⁻¹ := by
          simpa [hmap]
        simp only [map_mul] at hcongr
        rw [hmapInv] at hcongr
        simpa [XCoeffEquiv, map_mul] using hcongr }

/-- `XCoeff` inherits a normalized GCD monoid structure from `Polynomial ℝ`. -/
noncomputable instance : NormalizedGCDMonoid XCoeff :=
  UniqueFactorizationMonoid.toNormalizedGCDMonoid XCoeff



/-- The eliminated coordinate of a point in the plane. -/
def elimCoord (z : Point2) : ℝ := z 0

/-- The coefficient coordinate of a point in the plane. -/
def coeffCoord (z : Point2) : ℝ := z 1

/-- Specialize the coefficient variable of a plane polynomial. -/
noncomputable def Specialized0 (x : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    Polynomial ℝ :=
  (Curry0 p).map (coeffEval x)

/-- The coefficient resultant of a plane polynomial pair. -/
noncomputable def ResultantCoeff (p q : MvPolynomial (Fin 2) ℝ) : XCoeff :=
  Polynomial.resultant (Curry0 p) (Curry0 q)

/-- The roots of a coefficient polynomial in `ℝ`. -/
def CoeffRootSet (r : XCoeff) : Set ℝ :=
  {x | MvPolynomial.eval (fun _ : Fin 1 => x) r = 0}

/-- The common-zero fiber at a fixed coefficient coordinate. -/
def FiberCommonZeros (x : ℝ) (p q : MvPolynomial (Fin 2) ℝ) : Set ℝ :=
  {y | Polynomial.eval y (Specialized0 x p) = 0 ∧
       Polynomial.eval y (Specialized0 x q) = 0}





















/-- A coefficient-line factor in the plane. -/
noncomputable def CoeffLineFactor (x : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x

/-- The zero set of a coefficient polynomial, viewed as a vertical line in the plane. -/
def CoeffLineZeroSet (a : MvPolynomial (Fin 1) ℝ) : Set Point2 :=
  {p | MvPolynomial.eval (fun _ : Fin 1 => p 1) a = 0}

















































/-- The multivariate polynomial ring over `ℝ` is normalized. -/
noncomputable instance : NormalizationMonoid (MvPolynomial (Fin 2) ℝ) :=
  UniqueFactorizationMonoid.strongNormalizationMonoid.toNormalizationMonoid


























/-- Bivariate real polynomials — the ambient ring for plane curves. -/
abbrev PlanePoly := MvPolynomial (Fin 2) ℝ














end PachDeZeeuw.Algebraic


