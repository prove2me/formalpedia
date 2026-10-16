-- Prove2me | Definitions.Def_Esgk_SelfCurveReflectionInvariance
-- name    : Esgk_SelfCurveReflectionInvariance
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:40.788802+00:00
-- url     : https://prove2.me/theorems/3b458d9c-b4eb-4416-b03d-1ba51fff5ec8
-- title:
--   Polynomial substitution by horizontal reflection
-- statement:
--   This constructs reflection in the horizontal axis on points and polynomials, with identities relating evaluation, irreducibility and zero sets. It also supplies the fact that two irreducible real plane polynomials with infinitely many common zeros are associated.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw.Algebraic


theorem associated_of_infinite_irreducible_zeroSet_intersection
    {h k : MvPolynomial (Fin 2) ℝ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hinf : (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Infinite) :
    Associated h k := by
  by_contra hnot
  exact hinf
    (irreducible_pair_intersection_bound h k hh hk le_rfl le_rfl hnot).1

 
theorem zeroSet_eq_of_associated {h k : MvPolynomial (Fin 2) ℝ}
    (hassoc : Associated h k) :
    PlaneCurveZeroSet h = PlaneCurveZeroSet k := by
  have hdiv_hk : h ∣ k := (hassoc.dvd_iff_dvd_left).2 dvd_rfl
  have hdiv_kh : k ∣ h := (hassoc.dvd_iff_dvd_left).1 dvd_rfl
  exact Set.Subset.antisymm
    (PlaneCurveZeroSet_subset_of_dvd hdiv_hk)
    (PlaneCurveZeroSet_subset_of_dvd hdiv_kh)


theorem zeroSet_eq_of_irreducible_of_infinite_subset
    {h k : MvPolynomial (Fin 2) ℝ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hinf : (PlaneCurveZeroSet h).Infinite)
    (hsub : PlaneCurveZeroSet h ⊆ PlaneCurveZeroSet k) :
    PlaneCurveZeroSet h = PlaneCurveZeroSet k := by
  have hinter : PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k =
      PlaneCurveZeroSet h := Set.inter_eq_left.mpr hsub
  have hinterinf : (PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Infinite := by
    rw [hinter]
    exact hinf
  have hassoc : Associated h k :=
    associated_of_infinite_irreducible_zeroSet_intersection
      (h := h) (k := k) hh hk hinterinf
  exact zeroSet_eq_of_associated hassoc

 
def xAxisReflectionPoint (x : Point2) : Point2 :=
  WithLp.toLp 2 ![x 0, -x 1]

 
theorem xAxisReflectionPoint_involutive :
    Function.Involutive xAxisReflectionPoint := by
  intro x
  ext i
  fin_cases i <;> simp [xAxisReflectionPoint]

 
noncomputable def xAxisReflectionVariables : Fin 2 → PlanePoly :=
  ![MvPolynomial.X 0, -MvPolynomial.X 1]

 
noncomputable def xAxisReflectionPolynomialHom : PlanePoly →ₐ[ℝ] PlanePoly :=
  MvPolynomial.bind₁ xAxisReflectionVariables

 
theorem xAxisReflectionPolynomial_involutive :
    Function.Involutive xAxisReflectionPolynomialHom := by
  intro p
  have hcomp :
      xAxisReflectionPolynomialHom.comp xAxisReflectionPolynomialHom =
        AlgHom.id ℝ PlanePoly := by
    ext i
    fin_cases i <;>
      simp [xAxisReflectionPolynomialHom, xAxisReflectionVariables]
  exact AlgHom.congr_fun hcomp p


noncomputable def xAxisReflectionPolynomialEquiv :
    PlanePoly ≃ₐ[ℝ] PlanePoly :=
  AlgEquiv.ofBijective xAxisReflectionPolynomialHom
    xAxisReflectionPolynomial_involutive.bijective

 
theorem xAxisReflectionPolynomial_irreducible_iff (p : PlanePoly) :
    Irreducible (xAxisReflectionPolynomialHom p) ↔ Irreducible p := by
  change Irreducible (xAxisReflectionPolynomialEquiv p) ↔ Irreducible p
  exact MulEquiv.irreducible_iff xAxisReflectionPolynomialEquiv.toMulEquiv


theorem eval_xAxisReflectionPolynomial (p : PlanePoly) (x : Point2) :
    MvPolynomial.eval (fun i ↦ x i) (xAxisReflectionPolynomialHom p) =
      MvPolynomial.eval (fun i ↦ xAxisReflectionPoint x i) p := by
  change
    MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun i ↦ x i)
        (MvPolynomial.bind₁ xAxisReflectionVariables p) =
      MvPolynomial.eval₂Hom (RingHom.id ℝ)
        (fun i ↦ xAxisReflectionPoint x i) p
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂Hom_congr rfl
  · funext i
    fin_cases i <;> simp [xAxisReflectionVariables, xAxisReflectionPoint]
  · rfl


theorem mem_zeroSet_xAxisReflectionPolynomial_iff
    {p : PlanePoly} {x : Point2} :
    x ∈ PlaneCurveZeroSet (xAxisReflectionPolynomialHom p) ↔
      xAxisReflectionPoint x ∈ PlaneCurveZeroSet p := by
  change
    MvPolynomial.eval (fun i ↦ x i) (xAxisReflectionPolynomialHom p) = 0 ↔
      MvPolynomial.eval (fun i ↦ xAxisReflectionPoint x i) p = 0
  rw [eval_xAxisReflectionPolynomial]


end Esgk


