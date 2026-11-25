-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_Development
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:54:49.869115+00:00
-- url     : https://prove2.me/theorems/df1f89d3-96c5-4ae5-9594-bcd126bd2cdf
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureInverseContraction/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_RightInvOfContract
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HaarSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstLeftInvMuInf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField
namespace PI.NMeasInv.UnitaryGroupMassFormula
def Contract : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    FrameRel I e f z → ∃ C : Set I.Ginf, IsCompact C ∧ ∀ n ∈ Ninf I e z, ∃ a : I.Ginf,
      (∀ x ∈ Ninf I e z, a * x * a⁻¹ ∈ Ninf I e z) ∧ (∀ x ∈ Ninf I e z, a⁻¹ * x * a ∈ Ninf I e z) ∧
      a * n * a⁻¹ ∈ C
end PI.NMeasInv.UnitaryGroupMassFormula


