-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:44:42.552023+00:00
-- url     : https://prove2.me/theorems/a74b0f7d-41cc-43d9-bba8-89e2ba21bf5c
-- title:
--   Tri Defs
-- statement:
--   Definitions and structural lemmas for Tri Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupBasics/TriDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace PI.AmpRootCommon.Tri
def TriShear : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ),
    (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume
end PI.AmpRootCommon.Tri


