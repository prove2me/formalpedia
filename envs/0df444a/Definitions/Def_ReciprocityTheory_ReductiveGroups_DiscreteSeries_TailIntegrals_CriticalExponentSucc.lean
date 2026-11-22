-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_CriticalExponentSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:28.008804+00:00
-- url     : https://prove2.me/theorems/922c014d-59a0-4359-a39f-ef9ca9cd8a95
-- title:
--   Critical Exponent Succ
-- statement:
--   Definitions and structural lemmas for Critical Exponent Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/CriticalExponentSucc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_VolumeUnivFinZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Module
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace J2
abbrev TDom (p m : ℕ) := (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ
def chF (p m : ℕ) (ν : Fin (p + 1) → ℝ) (x : Xp p m) : ℝ≥0∞ :=
  ∏ l, ENNReal.ofReal (de x l ^ (-(s0N p m l + ν l)))
def tailF (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) (x : TDom p m) : ℝ≥0∞ :=
  ENNReal.ofReal (Lsq (tailPt x) 1 ^ ((-2 + α) / 2)) * ENNReal.ofReal (de (tailPt x) 1 ^ (-α)) *
    ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt x) i.succ ^ (-(s0N (p + 1) m i.succ + ν i)))
end J2
end ReciprocityTheory.ChartRestriction.DS.Xi


