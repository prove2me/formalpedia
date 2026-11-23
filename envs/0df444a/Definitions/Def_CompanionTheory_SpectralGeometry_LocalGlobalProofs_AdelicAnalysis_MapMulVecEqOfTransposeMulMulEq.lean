-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqOfTransposeMulMulEq
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqOfTransposeMulMulEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:30.656065+00:00
-- url     : https://prove2.me/theorems/45c5de23-01fa-4aee-b4a9-c4e83a676fa2
-- title:
--   Map Mul Vec Eq Of Transpose Mul Mul Eq
-- statement:
--   Definitions and structural lemmas for Map Mul Vec Eq Of Transpose Mul Mul Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulVecEqOfTransposeMulMulEq.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.Adelic.OrthHaar
section Equiv
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def mulVecEquiv (A : Matrix ι ι R) (h : IsUnit A.det) : (ι → R) ≃ₜ+ (ι → R) where
  toFun x := A *ᵥ x
  invFun x := A⁻¹ *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A h]
  right_inv x := by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A h]
  map_add' x y := Matrix.mulVec_add A x y
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id
end Equiv
section Measure
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open Classical in

noncomputable def scale (A : Matrix ι ι R) : ℝ≥0 :=
  if h : IsUnit A.det then addEquivAddHaarChar (mulVecEquiv A h) else 1
end Measure
end GlobalTheory.CompanionTheory.Adelic.OrthHaar


