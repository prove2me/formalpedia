-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateNineTermExact
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateNineTermExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:18.185393+00:00
-- url     : https://prove2.me/theorems/f9574e5d-3070-4a74-9118-c7205e204a1f
-- title:
--   Poitou Tate Nine Term Exact
-- statement:
--   Definitions and structural lemmas for Poitou Tate Nine Term Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PoitouTateNineTermExact.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NatCardDualEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardEqCardKerMulCardRange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDualStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristicStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
namespace GlobalTheory.CompanionTheory.PoitouTateCount
end GlobalTheory.CompanionTheory.PoitouTateCount


