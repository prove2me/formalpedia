-- Prove2me | Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
-- name    : QEC_Semantics_Core_ComputationalEmbedding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T09:05:24.291895+00:00
-- url     : https://prove2.me/theorems/fc398a6a-71d7-471c-ab06-339545e23e39
-- title:
--   Computational Embedding
-- statement:
--   Definitions and structural lemmas for Computational Embedding, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/ComputationalEmbedding.lean

import Definitions.Def_QEC_Semantics_Core_Definitions
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


set_option autoImplicit false
noncomputable section
namespace QEC.Semantics.ComputationalEmbedding
open scoped BigOperators
universe u v w
variable {A : Type u} {B : Type v} {C : Type w}
variable [Fintype A] [Fintype B] [Fintype C]
def linearMap (e : A ↪ B) : EuclideanSpace Complex A →ₗ[Complex] EuclideanSpace Complex B where
  toFun psi := ∑ a, psi a • EuclideanSpace.basisFun B Complex (e a)
  map_add' psi chi := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c psi := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [RingHom.id_apply]
    rw [smul_smul, mul_comm]
theorem linearMap_inner (e : A ↪ B) (psi chi : EuclideanSpace Complex A) :
    inner Complex (linearMap e psi) (linearMap e chi) = inner Complex psi chi := by
  have ho : Orthonormal Complex (fun a : A => EuclideanSpace.basisFun B Complex (e a)) :=
    (EuclideanSpace.basisFun B Complex).orthonormal.comp e e.injective
  change inner Complex (∑ a, psi a • EuclideanSpace.basisFun B Complex (e a))
    (∑ a, chi a • EuclideanSpace.basisFun B Complex (e a)) = _
  rw [ho.inner_sum psi chi Finset.univ]
  simp [PiLp.inner_apply, mul_comm]
def isometry (e : A ↪ B) : EuclideanSpace Complex A →ₗᵢ[Complex] EuclideanSpace Complex B :=
  (linearMap e).isometryOfInner (linearMap_inner e)
def compress (e : A ↪ B) (E : Operator (EuclideanSpace Complex B)) :
    Operator (EuclideanSpace Complex A) :=
  (LinearMap.adjoint (linearMap e)).comp (E.comp (linearMap e))
end QEC.Semantics.ComputationalEmbedding


