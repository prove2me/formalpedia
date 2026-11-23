-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GreenbergWilesFormula
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GreenbergWilesFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:22.29138+00:00
-- url     : https://prove2.me/theorems/868dc1b3-c9bd-4f10-8696-cdf455a22c4a
-- title:
--   Greenberg Wiles Formula
-- statement:
--   Definitions and structural lemmas for Greenberg Wiles Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GreenbergWilesFormula.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalGlobalDual
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PoitouTateEulerCharacteristic
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SelmerGroupDualExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
namespace GlobalTheory.CompanionTheory.GaloisCoh
end GlobalTheory.CompanionTheory.GaloisCoh
end


