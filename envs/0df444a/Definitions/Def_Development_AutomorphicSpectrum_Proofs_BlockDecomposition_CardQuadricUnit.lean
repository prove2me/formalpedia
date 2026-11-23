-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardQuadricUnit
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardQuadricUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:25.457047+00:00
-- url     : https://prove2.me/theorems/a451f088-5d93-4bec-8373-da059ee0c8de
-- title:
--   Card Quadric Unit
-- statement:
--   Definitions and structural lemmas for Card Quadric Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardQuadricUnit.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteFieldQuadraticFormPointCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.CompanionTheory.SW.QuadricUnit
open GlobalTheory.CompanionTheory.SW.QuadricCount
section OneVar
variable {k : Type} [Field k] [Fintype k] [DecidableEq k]
end OneVar
section Form
variable {k : Type} [Field k] [Fintype k] {ι : Type} [Fintype ι] [DecidableEq ι]
end Form
end GlobalTheory.CompanionTheory.SW.QuadricUnit


