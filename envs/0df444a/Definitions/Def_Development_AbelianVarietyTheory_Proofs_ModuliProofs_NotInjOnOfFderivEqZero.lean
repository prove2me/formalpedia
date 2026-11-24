-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:50.522714+00:00
-- url     : https://prove2.me/theorems/79935600-38bd-4d5e-af24-d1e46e4b3ada
-- title:
--   Not Inj On Of Fderiv Eq Zero
-- statement:
--   Definitions and structural lemmas for Not Inj On Of Fderiv Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotInjOnOfFderivEqZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
namespace GlobalTheory.InjHol
def LocalStatement (n : ℕ) : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F],
    Module.finrank ℂ E = n → Module.finrank ℂ F = n → ∀ (f : E → F) (a : E), AnalyticAt ℂ f a →
      (∃ s ∈ 𝓝 a, InjOn f s) → Function.Injective (fderiv ℂ f a)
end GlobalTheory.InjHol


