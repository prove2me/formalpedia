-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
-- name    : Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:49.247184+00:00
-- url     : https://prove2.me/theorems/bc2163b0-bb7b-4500-ae76-ae74015154c6
-- title:
--   Parabolic Element Blocks
-- statement:
--   Definitions and structural lemmas for Parabolic Element Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicElementBlocks.lean

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
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
namespace GlobalTheory.CompanionTheory.QLB
section Alg
variable {F : Type} [Field F]
section Blocks
variable {r d c : ℕ} (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin c) F)
  (C : Matrix (Fin d) (Fin r) F) (D : Matrix (Fin d) (Fin c) F)
end Blocks
end Alg
end GlobalTheory.CompanionTheory.QLB


