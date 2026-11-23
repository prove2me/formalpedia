-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:38.07588+00:00
-- url     : https://prove2.me/theorems/b610f19f-9405-4344-8c73-11d1a1c6c457
-- title:
--   Parabolic Test Function Equivariant
-- statement:
--   Definitions and structural lemmas for Parabolic Test Function Equivariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicTestFunctionEquivariant.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.Eigen
section Alg
variable {F : Type} [Field F]
end Alg
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
def Supp (O : Subring F) (ϖ : F) {r d c : ℕ} (x : Matrix (Fin (r + d)) (Fin (r + c)) F) : Prop :=
  bAA x ∈ Jset (GLint O r) ∧ bDA x ∈ IIset O ϖ ∧ bAD x ∈ intMat O r c ∧ bDD x ∈ intMat O d c
end Local
end GlobalTheory.CompanionTheory.QL.Eigen


