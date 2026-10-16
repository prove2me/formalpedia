-- Prove2me | Definitions.Def_Esgk_MaximallyCircularIsotropicBidegree
-- name    : Esgk_MaximallyCircularIsotropicBidegree
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T05:00:19.306095+00:00
-- url     : https://prove2.me/theorems/0d96b8b4-a28f-412d-94b0-dac96138ea63
-- title:
--   Isotropic charts and leading terms at circular points
-- statement:
--   This constructs the two isotropic chart homomorphisms, their homogenized forms, individual monomial terms, and the leading exponents used for circular-point bidegree analysis.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_DistanceNewtonFactorSaturation
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


def isotropicAffineCircularChartI : ComplexPlanePoly →+* CircularChartPoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly)
    ![MvPolynomial.C Complex.I * circularChartU,
      2 - MvPolynomial.C Complex.I * circularChartU]

 
def isotropicAffineCircularChartJ : ComplexPlanePoly →+* CircularChartPoly :=
  MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly)
    ![2 + MvPolynomial.C Complex.I * circularChartU,
      -MvPolynomial.C Complex.I * circularChartU]


def isotropicHomogenizedCircularChartI (D : ℕ) (Q : ComplexPlanePoly) :
    CircularChartPoly :=
  ∑ d ∈ Finset.range (D + 1),
    circularChartZ ^ (D - d) *
      isotropicAffineCircularChartI (MvPolynomial.homogeneousComponent d Q)


def isotropicHomogenizedCircularChartJ (D : ℕ) (Q : ComplexPlanePoly) :
    CircularChartPoly :=
  ∑ d ∈ Finset.range (D + 1),
    circularChartZ ^ (D - d) *
      isotropicAffineCircularChartJ (MvPolynomial.homogeneousComponent d Q)


def isotropicCircularChartITerm (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    CircularChartPoly :=
  MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
    (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
    circularChartZ ^ (D - e.degree)


def isotropicCircularChartJTerm (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    CircularChartPoly :=
  MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
    (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
    circularChartZ ^ (D - e.degree)


def isotropicILeadingExponent (D : ℕ) (e : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (e 0) + Finsupp.single 1 (D - e.degree)


def isotropicJLeadingExponent (D : ℕ) (e : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (e 1) + Finsupp.single 1 (D - e.degree)


end Esgk


