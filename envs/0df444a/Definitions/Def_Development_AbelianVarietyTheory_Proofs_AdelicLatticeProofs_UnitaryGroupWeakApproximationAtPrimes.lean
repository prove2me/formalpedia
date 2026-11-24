-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:30.630669+00:00
-- url     : https://prove2.me/theorems/ec30b23c-610b-4d02-9374-f82b147f978f
-- title:
--   Unitary Group Weak Approximation At Primes
-- statement:
--   Definitions and structural lemmas for Unitary Group Weak Approximation At Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/UnitaryGroupWeakApproximationAtPrimes.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
namespace GlobalTheory.UnRep.WeakApprox
def stab {R : Type} [CommRing R] {n : ℕ} (Λ : AddSubgroup (Fin n → R)) :
    Subring (Matrix (Fin n) (Fin n) R) where
  carrier := {M | ∀ z ∈ Λ, M *ᵥ z ∈ Λ}
  mul_mem' := fun {a b} ha hb z hz => by
    rw [← Matrix.mulVec_mulVec]; exact ha _ (hb z hz)
  one_mem' := fun z hz => by rwa [Matrix.one_mulVec]
  add_mem' := fun {a b} ha hb z hz => by
    rw [Matrix.add_mulVec]; exact add_mem (ha z hz) (hb z hz)
  zero_mem' := fun z _ => by rw [Matrix.zero_mulVec]; exact zero_mem _
  neg_mem' := fun {a} ha z hz => by rw [Matrix.neg_mulVec]; exact neg_mem (ha z hz)
noncomputable def skewPart {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R →+ Matrix (Fin n) (Fin n) R :=
  AddMonoidHom.mk' (fun A => A - (G * A.map σ * G⁻¹)ᵀ) fun A B => by
    rw [Matrix.map_add _ (map_add σ), mul_add, add_mul, Matrix.transpose_add]
    abel
end GlobalTheory.UnRep.WeakApprox


