-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalBinaryGramIntegralStatement
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalBinaryGramIntegralStatement
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:56.812785+00:00
-- url     : https://prove2.me/theorems/db0ac5b4-2c9f-4603-bda9-e17e5022e5fa
-- title:
--   Local Binary Gram Integral Statement
-- statement:
--   Definitions and structural lemmas for Local Binary Gram Integral Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalBinaryGramIntegralStatement.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalBinaryGramIntegral
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal


