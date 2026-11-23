-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsotropicBasisNonorthogonalTwoVectors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:19.438614+00:00
-- url     : https://prove2.me/theorems/129495d0-95c8-4aae-a3b4-55b124647f12
-- title:
--   Exists Isotropic Basis Nonorthogonal Two Vectors
-- statement:
--   Definitions and structural lemmas for Exists Isotropic Basis Nonorthogonal Two Vectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsotropicBasisNonorthogonalTwoVectors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.UTrans.IsoBasis
variable {E : Type} [Field E] {n : ℕ}
def hfL (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (y : Fin n → E) : (Fin n → E) →ₗ[E] E where
  toFun x := hf σ G x y
  map_add' u v := by simp [hf, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [hf, Finset.mul_sum, mul_assoc]
end GlobalTheory.UTrans.IsoBasis


