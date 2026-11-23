-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
-- name    : ReciprocityTheory_AnalyticForms_AnalyticCharts_MaDensCompEqZeroOfRankLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:21.998846+00:00
-- url     : https://prove2.me/theorems/baf94282-0a4f-4668-aa91-bc94268fad42
-- title:
--   Ma Dens Comp Eq Zero Of Rank Lt
-- statement:
--   Definitions and structural lemmas for Ma Dens Comp Eq Zero Of Rank Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/AnalyticCharts/MaDensCompEqZeroOfRankLt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm
open Complex Filter Topology
open scoped Matrix
noncomputable section
def leviC {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ) (a b : Fin e → ℂ) : ℂ :=
  ((H a b + H (I • a) (I • b) : ℝ) + I * ((H a (I • b) - H (I • a) b : ℝ))) / 4
end
end ReciprocityTheory.AnForm


