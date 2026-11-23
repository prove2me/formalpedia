-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrequencyIndexing
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrequencyIndexing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:05.169024+00:00
-- url     : https://prove2.me/theorems/e64b555e-e8ab-46cd-91b2-d2c936ee0a45
-- title:
--   Frequency Indexing
-- statement:
--   Definitions and structural lemmas for Frequency Indexing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrequencyIndexing.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (ω : Module.Basis (Fin n) ℝ (ι → ℝ))
noncomputable def νk (k : Fin n → ℤ) : ι → ℝ :=
  fun τ => (∑ j, (k j : ℝ) * ω.repr (Pi.single τ 1) j) / 2
end ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing


