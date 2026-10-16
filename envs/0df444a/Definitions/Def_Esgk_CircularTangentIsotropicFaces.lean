-- Prove2me | Definitions.Def_Esgk_CircularTangentIsotropicFaces
-- name    : Esgk_CircularTangentIsotropicFaces
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:58:54.642912+00:00
-- url     : https://prove2.me/theorems/f76f52bd-ae73-4742-88fc-7a70050af30f
-- title:
--   Isotropic tangent charts and face polynomials
-- statement:
--   This constructs the two isotropic affine and homogenized chart substitutions, their monomial terms and leading exponents, and translated first- and second-variable face polynomials.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_CircularJTangentConjugation
import Definitions.Def_Esgk_PlaneCircularLocalChart
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


def bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces : ComplexPlanePoly →+* CircularChartPoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly)
    ![MvPolynomial.C Complex.I * circularChartU,
      2 - MvPolynomial.C Complex.I * circularChartU]

 
def bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces : ComplexPlanePoly →+* CircularChartPoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly)
    ![2 + MvPolynomial.C Complex.I * circularChartU,
      -MvPolynomial.C Complex.I * circularChartU]


def bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces
    (D : ℕ) (Q : ComplexPlanePoly) : CircularChartPoly :=
  ∑ d ∈ Finset.range (D + 1),
    circularChartZ ^ (D - d) *
      bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces (MvPolynomial.homogeneousComponent d Q)

def bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces
    (D : ℕ) (Q : ComplexPlanePoly) : CircularChartPoly :=
  ∑ d ∈ Finset.range (D + 1),
    circularChartZ ^ (D - d) *
      bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces (MvPolynomial.homogeneousComponent d Q)


def isotropicFaceExponent (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b


def bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) : CircularChartPoly :=
  MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
    (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
    circularChartZ ^ (D - e.degree)

def bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) : CircularChartPoly :=
  MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
    (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
    circularChartZ ^ (D - e.degree)


def bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces
    (e : Fin 2 →₀ ℕ) (c : ℂ) : Polynomial ℂ :=
  Polynomial.C c * (Polynomial.C Complex.I * Polynomial.X) ^ e 0 *
    (2 - Polynomial.C Complex.I * Polynomial.X) ^ e 1

def bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces
    (e : Fin 2 →₀ ℕ) (c : ℂ) : Polynomial ℂ :=
  Polynomial.C c * (2 + Polynomial.C Complex.I * Polynomial.X) ^ e 0 *
    (-Polynomial.C Complex.I * Polynomial.X) ^ e 1


def bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial :
    ComplexPlanePoly →+* Polynomial (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)).comp
      (Polynomial.C : ℂ →+* Polynomial ℂ))
    ![Polynomial.C Polynomial.X, Polynomial.X]

def bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial :
    ComplexPlanePoly →+* Polynomial (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : Polynomial ℂ →+* Polynomial (Polynomial ℂ)).comp
      (Polynomial.C : ℂ →+* Polynomial ℂ))
    ![Polynomial.X, Polynomial.C Polynomial.X]


def isotropicSecondFacePolynomial (p : ℕ) (Q : ComplexPlanePoly) : Polynomial ℂ :=
  (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q).coeff p

 
def isotropicFirstFacePolynomial (p : ℕ) (Q : ComplexPlanePoly) : Polynomial ℂ :=
  (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q).coeff p


def bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation (c : ℂ) : Polynomial ℂ →+* Polynomial ℂ :=
  Polynomial.compRingHom (Polynomial.X - Polynomial.C c)

def bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation (c : ℂ) :
    Polynomial (Polynomial ℂ) →+* Polynomial (Polynomial ℂ) :=
  (Polynomial.compRingHom
      (Polynomial.X - Polynomial.C (Polynomial.C (star c)))).comp
    (Polynomial.mapRingHom (bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation c))

def bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation (c : ℂ) :
    Polynomial (Polynomial ℂ) →+* Polynomial (Polynomial ℂ) :=
  (Polynomial.compRingHom
      (Polynomial.X - Polynomial.C (Polynomial.C c))).comp
    (Polynomial.mapRingHom (bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation (star c)))


end Esgk


