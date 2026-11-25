-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:55.166358+00:00
-- url     : https://prove2.me/theorems/14dc3878-83a2-52e0-8f01-44cbd095ed8c
-- title:
--   Hol Jet F
-- statement:
--   Definitions and structural lemmas for Hol Jet F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {Y : Scheme.{0}}
section Tan
variable {K : Type} [Field K] {ι : Type} [DecidableEq ι]
end Tan
variable {g : ℕ}
end ReciprocityTheory.ChartRestriction.G.PullbackSections


