-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealDivisibleEqZero
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:03:40.559803+00:00
-- url     : https://prove2.me/theorems/9e987dfa-997f-4d97-9957-b3afdd873d8f
-- title:
--   Adelic Completion Fractional Ideal Divisible Eq Zero
-- statement:
--   Definitions and structural lemmas for Adelic Completion Fractional Ideal Divisible Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/AdelicCompletionFractionalIdealDivisibleEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedCompleteStatement
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
namespace GlobalTheory.AdLat
section TowerLimit
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
theorem lim_sg_smul (c : E ≃ₐ[F] E) (a : FiniteAdeleRing (𝓞 F) F) (z : RA F E) :
    sg (FiniteAdeleRing (𝓞 F) F) c (a • z) = a • sg (FiniteAdeleRing (𝓞 F) F) c z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b y => simp [sg, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
noncomputable def hermBil (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) :
    (Fin n → RA F E) →ₗ[FiniteAdeleRing (𝓞 F) F] (Fin n → RA F E) →ₗ[FiniteAdeleRing (𝓞 F) F] RA F E :=
  LinearMap.mk₂ _ (hermA c G)
    (fun x x' y => by simp [hermA, add_mul, Finset.sum_add_distrib])
    (fun a x y => by simp [hermA, Finset.smul_sum])
    (fun x y y' => by simp [hermA, mul_add, Finset.sum_add_distrib])
    (fun a x y => by simp [hermA, Finset.smul_sum, lim_sg_smul])
variable [NumberField E]
end TowerLimit
end GlobalTheory.AdLat


