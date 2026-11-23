-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:00.845297+00:00
-- url     : https://prove2.me/theorems/4d312e3f-d5b7-42a3-a19e-692608df2c7c
-- title:
--   Function Field Point
-- statement:
--   Definitions and structural lemmas for Function Field Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/FunctionFieldPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
section Generic
noncomputable def genX : W.toAffine.FunctionField :=
  algebraMap W.toAffine.CoordinateRing _ (CoordinateRing.mk W (C X))
noncomputable def genY : W.toAffine.FunctionField :=
  algebraMap W.toAffine.CoordinateRing _ (CoordinateRing.mk W Y)
theorem equation_gen : (W.baseChange W.toAffine.FunctionField).toAffine.Equation (genX W) (genY W) := by
  have h0 : CoordinateRing.mk W W.toAffine.polynomial = 0 := AdjoinRoot.mk_self
  have h1 := congrArg (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField) h0
  rw [equation_iff]
  simp only [Affine.polynomial, map_sub, map_add, map_mul, map_pow, map_zero] at h1
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, genX, genY]
  have e : ∀ a : F, algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (CoordinateRing.mk W (C (C a))) = algebraMap F W.toAffine.FunctionField a := fun a => rfl
  simp only [C_add, C_mul, map_add, map_mul, e] at h1
  linear_combination h1
end Generic
section Lift
variable {L : Type*} [Field L] [Algebra F L] {u v : L}
theorem eval₂_polynomial (h : (W.baseChange L).toAffine.Equation u v) :
    W.toAffine.polynomial.eval₂ (eval₂RingHom (algebraMap F L) u) v = 0 := by
  have e := (equation_iff _ _).mp h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at e
  simp only [Affine.polynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    coe_eval₂RingHom, eval₂_X, eval₂_C]
  linear_combination e
noncomputable def evalAt (h : (W.baseChange L).toAffine.Equation u v) :
    W.toAffine.CoordinateRing →ₐ[F] L where
  __ := AdjoinRoot.lift (eval₂RingHom (algebraMap F L) u) v (eval₂_polynomial W h)
  commutes' a := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply F F[X] W.toAffine.CoordinateRing, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    simp
theorem evalAt_algebraMap (h : (W.baseChange L).toAffine.Equation u v) (p : F[X]) :
    evalAt W h (algebraMap F[X] W.toAffine.CoordinateRing p) = aeval u p := by
  rw [AdjoinRoot.algebraMap_eq]
  change AdjoinRoot.lift (eval₂RingHom (algebraMap F L) u) v (eval₂_polynomial W h)
    (AdjoinRoot.of _ p) = _
  rw [AdjoinRoot.lift_of, coe_eval₂RingHom, aeval_def]
instance : Module.Finite F[X] W.toAffine.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W.toAffine)
instance : Algebra.IsIntegral F[X] W.toAffine.CoordinateRing := Algebra.IsIntegral.of_finite _ _
theorem evalAt_injective (h : (W.baseChange L).toAffine.Equation u v) (hu : Transcendental F u) :
    Function.Injective (evalAt W h) := by
  rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker (evalAt W h) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := F[X])
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
    rw [evalAt_algebraMap]
    exact ⟨fun hp => (transcendental_iff_injective.mp hu) (by rw [hp, map_zero]), fun hp => by
      rw [hp, map_zero]⟩
  intro a ha
  rw [← RingHom.mem_ker, hker] at ha
  exact ha
noncomputable def liftPoint (h : (W.baseChange L).toAffine.Equation u v)
    (hu : Transcendental F u) : W.toAffine.FunctionField →ₐ[F] L :=
  IsFractionRing.liftAlgHom (evalAt_injective W h hu)
end Lift
section GenericPoint
noncomputable def coefB : W.toAffine.FunctionField :=
  algebraMap F _ W.a₁ * genX W + algebraMap F _ W.a₃
noncomputable def coefC : W.toAffine.FunctionField :=
  genX W ^ 3 + algebraMap F _ W.a₂ * genX W ^ 2 + algebraMap F _ W.a₄ * genX W + algebraMap F _ W.a₆
noncomputable instance : DecidableEq W.toAffine.FunctionField := Classical.decEq _
variable [W.IsElliptic]
instance (A : Type*) [Field A] [Algebra F A] : (W.baseChange A).IsElliptic := by
  unfold WeierstrassCurve.baseChange; infer_instance
noncomputable def genericPoint : (W.baseChange W.toAffine.FunctionField).toAffine.Point :=
  .some (genX W) (genY W) (equation_iff_nonsingular.mp (equation_gen W))
end GenericPoint
end GroundTheory.Arith.Abelian


