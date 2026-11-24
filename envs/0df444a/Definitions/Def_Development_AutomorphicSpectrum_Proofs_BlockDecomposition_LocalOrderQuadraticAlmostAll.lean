-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalOrderQuadraticAlmostAll
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalOrderQuadraticAlmostAll
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:25:37.923795+00:00
-- url     : https://prove2.me/theorems/15a2209e-0611-4c6b-9da8-08d16a050edb
-- title:
--   Local Order Quadratic Almost All
-- statement:
--   Definitions and structural lemmas for Local Order Quadratic Almost All, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalOrderQuadraticAlmostAll.lean

import Mathlib
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
namespace GlobalTheory.CompanionTheory.SW.QuadRing
open GlobalTheory.CompanionTheory.SW.GoodRing
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
end GlobalTheory.CompanionTheory.SW.QuadRing


