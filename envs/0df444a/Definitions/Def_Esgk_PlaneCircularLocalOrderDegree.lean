-- Prove2me | Definitions.Def_Esgk_PlaneCircularLocalOrderDegree
-- name    : Esgk_PlaneCircularLocalOrderDegree
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:57:04.607952+00:00
-- url     : https://prove2.me/theorems/a34f0ab2-6788-4fda-884a-6735dc8d0e99
-- title:
--   Local order at the circular points at infinity
-- statement:
--   This defines restrictions of plane polynomials to the line at infinity and the local order of a homogenized polynomial in a circular-point chart. The two distinguished orders use the circular points with affine chart coordinates $i$ and $-i$.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_MvPolynomialLocalOrder
import Definitions.Def_Esgk_PlaneCircularLocalChart
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.MvPowerSeries.Order

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

 
def realPlaneOneXRestriction : PlanePoly →+* Polynomial ℝ :=
  (MvPolynomial.aeval ![(1 : Polynomial ℝ), Polynomial.X]).toRingHom

 
def realPlaneInfinityRestriction (G : PlanePoly) : Polynomial ℝ :=
  realPlaneOneXRestriction (MvPolynomial.homogeneousComponent G.totalDegree G)

 
def complexPlaneInfinityRestriction (G : PlanePoly) : Polynomial ℂ :=
  (realPlaneInfinityRestriction G).map Complex.ofRealHom


def projectiveInfinityRestriction : ProjectivePlanePoly →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C ![1, Polynomial.X, 0]


def chartInfinityRestriction : CircularChartPoly →+* Polynomial ℂ :=
  (Polynomial.mapRingHom
    (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)).comp
      (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom


def planeCircularLocalOrder (c : ℂ) (G : PlanePoly) : ℕ :=
  (MvPolynomial.localOrder
    (projectiveCircularChart c (planeHomogenization G.totalDegree G))).toNat

 
def planeCircularLocalOrderI (G : PlanePoly) : ℕ :=
  planeCircularLocalOrder Complex.I G

 
def planeCircularLocalOrderJ (G : PlanePoly) : ℕ :=
  planeCircularLocalOrder (-Complex.I) G


end Esgk


