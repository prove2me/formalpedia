-- Prove2me | Definitions.Def_MazurReduction_PointTransport
-- name    : MazurReduction_PointTransport
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-06T10:28:16.656042+00:00
-- url     : https://prove2.me/theorems/d832ab9e-99db-4b44-965a-17eab4aea320
-- title:
--   Point transport for rational good reduction
-- statement:
--   Structural interfaces identify actual affine point groups across equality of Weierstrass curves and across an isomorphism of base fields. The module also supplies finiteness of the nonsingular point set over a finite ring. Its named downstream consumer is the full Mazur good-reduction torsion bound.
-- source:
--   Adapted with attribution from https://github.com/MichaelStollBayreuth/EllipticCurves/tree/3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f and the integration in MazurTheorem/EllipticCurves/Mathlib/EllipticCurvePoint.lean.

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Vasily Ilin

The structural point equivalences are adapted from
MichaelStollBayreuth/EllipticCurves, commit
3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f,
as integrated in MazurTheorem/EllipticCurves/Mathlib/EllipticCurvePoint.lean.
-/
import Mathlib

open WeierstrassCurve.Affine
namespace MazurReduction

/-- Boundary: transport actual point groups across equality of curves.
Named downstream consumer: the Mazur campaign good-reduction bound. -/
def curvePointCongr {K : Type*} [Field K] [DecidableEq K]
    {W₁ W₂ : WeierstrassCurve.Affine K} (h : W₁ = W₂) : W₁.Point ≃+ W₂.Point := by
  subst h
  exact AddEquiv.refl _

/-- Boundary: transport actual point groups across a base-field isomorphism.
Named downstream consumer: the Mazur campaign good-reduction bound. -/
noncomputable def pointBaseChangeEquiv
    {R F K : Type*} [CommRing R] [Field F] [Field K]
    [DecidableEq F] [DecidableEq K] [Algebra R F] [Algebra R K]
    (W : WeierstrassCurve.Affine R) (σ : F ≃ₐ[R] K) :
    (W⁄F).Point ≃+ (W⁄K).Point where
  toFun := Point.map (σ : F →ₐ[R] K)
  invFun := Point.map (σ.symm : K →ₐ[R] F)
  map_add' := (Point.map (σ : F →ₐ[R] K)).map_add
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      rw [Point.map_some, Point.map_some, Point.some.injEq]
      exact ⟨σ.symm_apply_apply x, σ.symm_apply_apply y⟩
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      rw [Point.map_some, Point.map_some, Point.some.injEq]
      exact ⟨σ.apply_symm_apply x, σ.apply_symm_apply y⟩

instance finitePointOfFiniteRing {R : Type*} [CommRing R] [Finite R]
    (W : WeierstrassCurve.Affine R) : Finite W.Point :=
  .of_equiv (Option {xy : R × R // W.Nonsingular xy.1 xy.2})
    (nonsingularPointEquiv W).symm

end MazurReduction


