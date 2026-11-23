-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_TriShear
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerShearHaar_TriShear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:02.577351+00:00
-- url     : https://prove2.me/theorems/b9297df7-13bd-424a-b7ee-889ca54495be
-- title:
--   Tri Shear
-- statement:
--   Definitions and structural lemmas for Tri Shear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LowerShearHaar/TriShear.lean

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
namespace PI.LowSplitHaarW
def TriShear : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ),
    (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume
end PI.LowSplitHaarW


