-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsIntegralBasisHermitianMatricesDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:27.064694+00:00
-- url     : https://prove2.me/theorems/6b5af7ae-0725-4d0e-92f8-621795f9e49c
-- title:
--   Exists Integral Basis Hermitian Matrices Dual
-- statement:
--   Definitions and structural lemmas for Exists Integral Basis Hermitian Matrices Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsIntegralBasisHermitianMatricesDual.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.HermLat
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem cc_add (x y : E) : cc (x + y) = cc x + cc y := map_add _ _ _
theorem cc_zero : cc (0 : E) = 0 := map_zero _
theorem cc_smul (q : ℚ) (x : E) : cc (q • x) = q • cc x :=
  map_rat_smul (IsCMField.complexConj E) q x
def HermSub (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) :
    Submodule ℚ (Matrix (Fin N) (Fin N) E) where
  carrier := {X | ccT X = X}
  add_mem' {X Y} hX hY := by
    ext a b
    have h1 := congrFun (congrFun hX a) b
    have h2 := congrFun (congrFun hY a) b
    simp only [ccT, transpose_apply, map_apply, Matrix.add_apply] at h1 h2 ⊢
    rw [cc_add, h1, h2]
  zero_mem' := by
    ext a b
    simp [ccT, cc_zero]
  smul_mem' q X hX := by
    ext a b
    have h1 := congrFun (congrFun hX a) b
    simp only [ccT, transpose_apply, map_apply, Matrix.smul_apply] at h1 ⊢
    rw [cc_smul, h1]
def form (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) :
    LinearMap.BilinForm ℚ (HermSub E N) :=
  LinearMap.mk₂ ℚ (fun X Y => (1 / 2 : ℚ) * Algebra.trace ℚ E (X.1 * Y.1).trace)
    (fun X X' Y => by simp [add_mul, mul_add])
    (fun q X Y => by simp [mul_left_comm])
    (fun X Y Y' => by simp [mul_add])
    (fun q X Y => by simp [mul_left_comm])
end
end GlobalTheory.SW.HermLat


