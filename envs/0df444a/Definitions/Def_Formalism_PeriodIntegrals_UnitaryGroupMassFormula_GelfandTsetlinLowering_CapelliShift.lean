-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:39.941314+00:00
-- url     : https://prove2.me/theorems/914a09ac-9774-49db-a284-ae21d43c3cf7
-- title:
--   Capelli Shift
-- statement:
--   Definitions and structural lemmas for Capelli Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliShift.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliEqv
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
def capE {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (a b : Fin n) :
    Module.End ℂ (MvPolynomial (Fin N × Fin N) ℂ) :=
  pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) +
    if a = b then algebraMap ℂ _ (lam.detShift : ℂ) else 0
end PI.WGL


