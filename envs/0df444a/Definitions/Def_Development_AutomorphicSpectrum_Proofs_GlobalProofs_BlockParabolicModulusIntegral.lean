-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockParabolicModulusIntegral
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockParabolicModulusIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:19:31.385979+00:00
-- url     : https://prove2.me/theorems/e51d01a8-874c-4646-a831-f8da4a5b06d7
-- title:
--   Block Parabolic Modulus Integral
-- statement:
--   Definitions and structural lemmas for Block Parabolic Modulus Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlockParabolicModulusIntegral.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RelIndexBoxLatticesProduct
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBalls
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemBoxLatticeIffCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DiagonalConjugateCongruenceBox
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
namespace GlobalTheory.CompanionTheory.QL.ModB
variable {F : Type} [Field F]
def dg {n : ℕ} (v : Fin n → F) (hv : ∀ i, v i ≠ 0) : GL (Fin n) F where
  val := Matrix.diagonal v
  inv := Matrix.diagonal fun i => (v i)⁻¹
  val_inv := by simp [Matrix.diagonal_mul_diagonal, hv]
  inv_val := by simp [Matrix.diagonal_mul_diagonal, hv]
end GlobalTheory.CompanionTheory.QL.ModB


