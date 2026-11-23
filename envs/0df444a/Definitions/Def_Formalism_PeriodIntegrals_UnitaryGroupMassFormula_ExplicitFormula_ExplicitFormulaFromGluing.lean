-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_ExplicitFormulaFromGluing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:25.313987+00:00
-- url     : https://prove2.me/theorems/ec7c043e-4a2f-43b1-91e8-6c9ede662c06
-- title:
--   Explicit Formula From Gluing
-- statement:
--   Definitions and structural lemmas for Explicit Formula From Gluing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/ExplicitFormulaFromGluing.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EF
open Complex
def GluePerronTrunc : Prop :=
  PerronKernel → (∃ C, 0 < C ∧ PerronSumBound C) → ∃ C, 0 < C ∧ PerronTrunc C
def GluePerronL : Prop := (∃ C, 0 < C ∧ PerronTrunc C) → ∃ C, 0 < C ∧ PerronL C
def GlueRectResidue : Prop := RectCauchy → RectResidue
def GlueGoodHeight : Prop := PI.ZerosWindow → ∃ κ, 0 < κ ∧ GoodHeightExists κ
def GlueTruncChange : Prop := PI.ZerosWindow → ∃ C, 0 < C ∧ TruncChange C
def GlueZerosFinite : Prop := PI.ZerosWindow → ZerosFinite
def GlueLocalLemma : Prop :=
  LocalAbstract → (∃ A C, 0 < A ∧ 0 < C ∧ LGrowth A C) → ZeroLocus → PI.ZerosWindow →
    ∃ C, 0 < C ∧ LocalLemma C
def GlueHoriz : Prop :=
  PI.ZerosWindow → (∃ C, 0 < C ∧ LocalLemma C) → ZeroLocus → ∀ κ, 0 < κ → ∃ C, 0 < C ∧ LogDerivHoriz κ C
def GlueLeft : Prop :=
  PI.ZerosWindow → (∃ C, 0 < C ∧ LocalLemma C) → ZeroLocus → ∃ C, 0 < C ∧ LogDerivLeft C
def GlueRegAtZero : Prop :=
  PI.ZerosWindow → (∃ C, 0 < C ∧ LocalLemma C) → ∃ C, 0 < C ∧ RegAtZero C
def GlueContour : Prop := RectResidue → ZeroLocus → ZerosFinite → ContourIdentity
def GlueSides : Prop :=
  ∀ κ, 0 < κ → (∃ C, 0 < C ∧ LogDerivHoriz κ C) → (∃ C, 0 < C ∧ LogDerivLeft C) →
    ∃ C, 0 < C ∧ SidesBound κ C
def GlueShift : Prop :=
  ∀ κ, 0 < κ → RegularPart → ContourIdentity → (∃ C, 0 < C ∧ SidesBound κ C) →
    (∃ C, 0 < C ∧ RegAtZero C) → ∃ C, 0 < C ∧ ShiftBound κ C
end PI.EF


