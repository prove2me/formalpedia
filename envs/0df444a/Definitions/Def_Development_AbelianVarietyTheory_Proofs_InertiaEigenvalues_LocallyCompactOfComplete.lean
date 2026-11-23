-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:37.838508+00:00
-- url     : https://prove2.me/theorems/1210fdf0-63bc-4bf1-8acc-88169372a538
-- title:
--   Locally Compact Of Complete
-- statement:
--   Definitions and structural lemmas for Locally Compact Of Complete, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
namespace GlobalTheory.UnitLemma.Bridge
def fixedField {E : Type} [Field E] (c : E ≃+* E) : Subfield E :=
  RingHom.eqLocusField (c : E →+* E) (RingHom.id E)
noncomputable def absOfVal {E : Type} [Field E] (v : Valuation E (WithZero (Multiplicative ℤ))) :
    AbsoluteValue E ℝ where
  toFun x := WithZeroMulInt.toNNReal (e := 2) two_ne_zero (v x)
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by simp
  add_le' x y := by
    have hm := (WithZeroMulInt.toNNReal_strictMono (e := 2) one_lt_two).monotone
    rcases le_max_iff.1 (v.map_add x y) with h | h
    · exact (NNReal.coe_le_coe.2 (hm h)).trans (le_add_of_nonneg_right (NNReal.coe_nonneg _))
    · exact (NNReal.coe_le_coe.2 (hm h)).trans (le_add_of_nonneg_left (NNReal.coe_nonneg _))
end GlobalTheory.UnitLemma.Bridge
namespace GlobalTheory.UnitLemma
open Bridge
end GlobalTheory.UnitLemma


