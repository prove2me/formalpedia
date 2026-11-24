-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:09.261191+00:00
-- url     : https://prove2.me/theorems/59bc0e8a-df33-42b7-a2d7-e6802fbb96ab
-- title:
--   Exists Prime Abs Norm Of Has Dirichlet Density
-- statement:
--   Definitions and structural lemmas for Exists Prime Abs Norm Of Has Dirichlet Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]
def ratPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) : ℕ := Ideal.absNorm (𝔭.asIdeal.under ℤ)
end ReciprocityTheory.Neutral.Bridge


