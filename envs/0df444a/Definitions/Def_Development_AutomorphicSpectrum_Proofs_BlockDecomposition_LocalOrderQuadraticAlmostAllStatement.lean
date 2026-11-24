-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalOrderQuadraticAlmostAllStatement
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalOrderQuadraticAlmostAllStatement
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:42:14.056647+00:00
-- url     : https://prove2.me/theorems/0a11b86d-2c7a-41a9-87cd-1218096f4df2
-- title:
--   Local Order Quadratic Almost All Statement
-- statement:
--   Definitions and structural lemmas for Local Order Quadratic Almost All Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalOrderQuadraticAlmostAllStatement.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalOrderQuadraticAlmostAll
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain
open scoped TensorProduct


