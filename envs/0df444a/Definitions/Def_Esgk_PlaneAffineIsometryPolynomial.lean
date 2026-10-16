-- Prove2me | Definitions.Def_Esgk_PlaneAffineIsometryPolynomial
-- name    : Esgk_PlaneAffineIsometryPolynomial
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:47.619763+00:00
-- url     : https://prove2.me/theorems/888bab35-88f2-435a-86e7-8b0844a2ee46
-- title:
--   Polynomial substitution by affine isometries
-- statement:
--   This constructs coordinate polynomials and the induced substitution map for an affine isometry of the real plane. Substitution by the inverse isometry gives the inverse algebra map on plane polynomials.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

 
noncomputable def bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis : Module.Basis (Fin 2) ℝ Point2 :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

 
noncomputable def planeAffineCoordinatePolynomial
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) (i : Fin 2) : PlanePoly :=
  g.linearIsometryEquiv.toLinearEquiv.toLinearMap.toMvPolynomial
      bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis i +
    MvPolynomial.C ((g 0) i)

 
@[simp]
theorem eval_planeAffineCoordinatePolynomial
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) (z : Point2) (i : Fin 2) :
    MvPolynomial.eval (fun j ↦ z j) (planeAffineCoordinatePolynomial g i) = (g z) i := by
  have hlinear :=
    LinearMap.toMvPolynomial_eval_eq_apply bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis
      g.linearIsometryEquiv.toLinearEquiv.toLinearMap i (bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis.repr z)
  have hlinear' :
      MvPolynomial.eval (fun j ↦ z j)
          (g.linearIsometryEquiv.toLinearEquiv.toLinearMap.toMvPolynomial
            bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis i) =
        (g.linearIsometryEquiv z) i := by
    have hrepr : bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis.repr z = fun j ↦ z j := by
      funext j
      simp [bundle_Esgk_PlaneAffineIsometryPolynomial_point2Basis, OrthonormalBasis.coe_toBasis_repr_apply,
        EuclideanSpace.basisFun_repr]
    rw [hrepr] at hlinear
    exact hlinear
  have haffine : g z = g.linearIsometryEquiv z + g 0 := by
    simpa [AffineIsometryEquiv.linear_eq_linear_isometry] using
      g.toAffineEquiv.map_vadd (0 : Point2) z
  rw [planeAffineCoordinatePolynomial, map_add, MvPolynomial.eval_C, hlinear', haffine]
  rfl

 
noncomputable def planeAffinePolynomialHom
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) : PlanePoly →ₐ[ℝ] PlanePoly :=
  MvPolynomial.bind₁ (planeAffineCoordinatePolynomial g)


theorem eval_planeAffinePolynomialHom
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) (p : PlanePoly) (z : Point2) :
    MvPolynomial.eval (fun i ↦ z i) (planeAffinePolynomialHom g p) =
      MvPolynomial.eval (fun i ↦ g z i) p := by
  change
    MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun i ↦ z i)
        (MvPolynomial.bind₁ (planeAffineCoordinatePolynomial g) p) =
      MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun i ↦ g z i) p
  rw [MvPolynomial.eval₂Hom_bind₁]
  apply MvPolynomial.eval₂Hom_congr rfl
  · funext i
    exact eval_planeAffineCoordinatePolynomial g z i
  · rfl

 
theorem bind_planeAffineCoordinatePolynomial_symm
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) (i : Fin 2) :
    MvPolynomial.bind₁ (planeAffineCoordinatePolynomial g)
        (planeAffineCoordinatePolynomial g.symm i) =
      MvPolynomial.X i := by
  apply MvPolynomial.funext
  intro z
  let x : Point2 := WithLp.toLp 2 z
  calc
    MvPolynomial.eval z
        (MvPolynomial.bind₁ (planeAffineCoordinatePolynomial g)
          (planeAffineCoordinatePolynomial g.symm i)) =
        MvPolynomial.eval (fun j ↦ g x j)
          (planeAffineCoordinatePolynomial g.symm i) := by
            simpa [planeAffinePolynomialHom, x] using
              eval_planeAffinePolynomialHom g (planeAffineCoordinatePolynomial g.symm i) x
    _ = (g.symm (g x)) i := eval_planeAffineCoordinatePolynomial g.symm (g x) i
    _ = MvPolynomial.eval z (MvPolynomial.X i) := by simp [x]

 
theorem bind_symm_planeAffineCoordinatePolynomial
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) (i : Fin 2) :
    MvPolynomial.bind₁ (planeAffineCoordinatePolynomial g.symm)
        (planeAffineCoordinatePolynomial g i) =
      MvPolynomial.X i := by
  simpa using bind_planeAffineCoordinatePolynomial_symm g.symm i

 
theorem planeAffinePolynomialHom_comp_symm (g : Point2 ≃ᵃⁱ[ℝ] Point2) :
    (planeAffinePolynomialHom g).comp (planeAffinePolynomialHom g.symm) =
      AlgHom.id ℝ PlanePoly := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa [planeAffinePolynomialHom] using bind_planeAffineCoordinatePolynomial_symm g i

 
theorem planeAffinePolynomialHom_symm_comp (g : Point2 ≃ᵃⁱ[ℝ] Point2) :
    (planeAffinePolynomialHom g.symm).comp (planeAffinePolynomialHom g) =
      AlgHom.id ℝ PlanePoly := by
  apply MvPolynomial.algHom_ext
  intro i
  simpa [planeAffinePolynomialHom] using bind_symm_planeAffineCoordinatePolynomial g i

 
noncomputable def planeAffinePolynomialEquiv
    (g : Point2 ≃ᵃⁱ[ℝ] Point2) : PlanePoly ≃ₐ[ℝ] PlanePoly :=
  AlgEquiv.ofAlgHom (planeAffinePolynomialHom g) (planeAffinePolynomialHom g.symm)
    (planeAffinePolynomialHom_comp_symm g) (planeAffinePolynomialHom_symm_comp g)


end Esgk


