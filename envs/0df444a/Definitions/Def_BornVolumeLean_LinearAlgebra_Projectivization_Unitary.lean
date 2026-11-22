-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Unitary
-- name    : BornVolumeLean_LinearAlgebra_Projectivization_Unitary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:56:01.547384+00:00
-- url     : https://prove2.me/theorems/71e12bec-0dab-40d5-aabb-eaf0ef62f14c
-- title:
--   Unitary
-- statement:
--   Definitions and structural lemmas for Unitary, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/Unitary.lean

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Topology
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Theorems.Thm_Projectivization_mapEquiv_continuous_of_finiteDim

set_option autoImplicit false
@[expose] public section
@[expose] public section
open Matrix
open scoped LinearAlgebra.Projectivization
namespace Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def toEuclideanLinearEquiv (A : Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℂ ι ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
  LinearEquiv.ofLinearMap
    (Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ))
    (Matrix.toEuclideanLin (star A.val : Matrix ι ι ℂ))
    (by
      show Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ) ∘ₗ
           Matrix.toEuclideanLin (star A.val : Matrix ι ι ℂ)
         = LinearMap.id
      rw [← Matrix.toLpLin_mul_same 2 (A.val : Matrix ι ι ℂ) (star A.val),
          show (A.val : Matrix ι ι ℂ) * star A.val
                = (1 : Matrix ι ι ℂ) from Unitary.coe_mul_star_self A,
          Matrix.toLpLin_one 2])
    (by
      show Matrix.toEuclideanLin (star A.val : Matrix ι ι ℂ) ∘ₗ
           Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ)
         = LinearMap.id
      rw [← Matrix.toLpLin_mul_same 2 (star A.val : Matrix ι ι ℂ) A.val,
          show (star A.val : Matrix ι ι ℂ) * A.val
                = (1 : Matrix ι ι ℂ) from Unitary.coe_star_mul_self A,
          Matrix.toLpLin_one 2])
lemma toEuclideanLinearEquiv_one :
    toEuclideanLinearEquiv (1 : Matrix.unitaryGroup ι ℂ)
      = LinearEquiv.refl ℂ (EuclideanSpace ℂ ι) := by
  apply LinearEquiv.toLinearMap_injective
  -- Goal: ↑(toEuclideanLinearEquiv 1) = ↑(LinearEquiv.refl ℂ ...)
  --      = LinearMap.id
  show Matrix.toEuclideanLin
        ((1 : Matrix.unitaryGroup ι ℂ).val : Matrix ι ι ℂ)
      = LinearMap.id
  rw [Matrix.UnitaryGroup.one_val]
  exact Matrix.toLpLin_one 2
lemma toEuclideanLinearEquiv_mul (A B : Matrix.unitaryGroup ι ℂ) :
    toEuclideanLinearEquiv (A * B)
      = toEuclideanLinearEquiv A * toEuclideanLinearEquiv B := by
  apply LinearEquiv.toLinearMap_injective
  -- LinearMap-level goal: toEuclideanLin (A*B).val = (toEuclideanLin A.val) ∘ₗ (toEuclideanLin
  -- B.val)
  -- The LinearEquiv * coerces to the LinearMap * = LinearMap.comp (= ∘ₗ).
  show Matrix.toEuclideanLin ((A * B).val : Matrix ι ι ℂ)
      = (Matrix.toEuclideanLin (A.val : Matrix ι ι ℂ)) ∘ₗ
        (Matrix.toEuclideanLin (B.val : Matrix ι ι ℂ))
  rw [Matrix.UnitaryGroup.mul_val, Matrix.toLpLin_mul_same]
noncomputable def toEuclideanLinearEquivHom :
    Matrix.unitaryGroup ι ℂ →*
      (EuclideanSpace ℂ ι ≃ₗ[ℂ] EuclideanSpace ℂ ι) where
  toFun := toEuclideanLinearEquiv
  map_one' := toEuclideanLinearEquiv_one
  map_mul' := toEuclideanLinearEquiv_mul
noncomputable instance instProjectivizationMulAction :
    MulAction (Matrix.unitaryGroup ι ℂ)
      (ℙ ℂ (EuclideanSpace ℂ ι)) :=
  MulAction.compHom _ toEuclideanLinearEquivHom
instance instProjectivizationContinuousConstSMul :
    ContinuousConstSMul (Matrix.unitaryGroup ι ℂ)
      (ℙ ℂ (EuclideanSpace ℂ ι)) where
  continuous_const_smul U :=
    Projectivization.mapEquiv_continuous_of_finiteDim
      (toEuclideanLinearEquivHom U)
end Matrix.UnitaryGroup


