-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmulMemOfIsIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmulMemOfIsIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:17.928795+00:00
-- url     : https://prove2.me/theorems/b64986da-1212-4a04-a206-c2fda4e4b0dd
-- title:
--   Smul Mem Of Is Integral
-- statement:
--   Definitions and structural lemmas for Smul Mem Of Is Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SmulMemOfIsIntegral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.FlagData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
theorem transvMat_mulVec (G : Matrix (Fin r) (Fin r) E) (ξ x : Fin r → E) (α : E) :
    FD.transvMat G ξ α *ᵥ x = x + (α * FD.herm G x ξ) • ξ := by
  funext a
  simp only [FD.transvMat, FD.herm, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul,
    Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring
theorem herm_add_smul_left (G : Matrix (Fin r) (Fin r) E) (x ξ y : Fin r → E) (c : E) :
    FD.herm G (x + c • ξ) y = FD.herm G x y + c * FD.herm G ξ y := by
  simp only [FD.herm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
theorem transvMat_mul_neg (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : FD.transvMat G ξ α * FD.transvMat G ξ (-α) = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    transvMat_mulVec, transvMat_mulVec, herm_add_smul_left, hξ, mul_zero, add_zero, neg_mul,
    neg_smul, neg_add_cancel_right]
noncomputable def transv (G : Matrix (Fin r) (Fin r) E) {ξ : Fin r → E} (hξ : FD.herm G ξ ξ = 0)
    (α : E) : GL (Fin r) E where
  val := FD.transvMat G ξ α
  inv := FD.transvMat G ξ (-α)
  val_inv := transvMat_mul_neg G hξ α
  inv_val := by simpa using transvMat_mul_neg G hξ (-α)
end GlobalTheory.FlagData


