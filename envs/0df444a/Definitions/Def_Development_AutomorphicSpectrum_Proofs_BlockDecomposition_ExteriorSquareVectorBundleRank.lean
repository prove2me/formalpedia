-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorSquareVectorBundleRank
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorSquareVectorBundleRank
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:30.624913+00:00
-- url     : https://prove2.me/theorems/8d859123-8659-46e4-a88d-29f4a6e26565
-- title:
--   Exterior Square Vector Bundle Rank
-- statement:
--   Definitions and structural lemmas for Exterior Square Vector Bundle Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorSquareVectorBundleRank.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
namespace GlobalTheory.CompanionTheory.WedgeOf
end GlobalTheory.CompanionTheory.WedgeOf


