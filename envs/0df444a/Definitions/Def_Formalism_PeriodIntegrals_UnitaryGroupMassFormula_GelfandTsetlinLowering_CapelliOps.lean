-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliOps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:57:39.59825+00:00
-- url     : https://prove2.me/theorems/67fe6850-d045-4de6-8038-665ce7c7e283
-- title:
--   Capelli Ops
-- statement:
--   Definitions and structural lemmas for Capelli Ops, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/CapelliOps.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWRaise
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
def pol (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) :
    MvPolynomial (Fin r × Fin m) R →ₗ[R] MvPolynomial (Fin r × Fin m) R :=
  ∑ s : Fin m, (LinearMap.mulLeft R (X (a, s))) ∘ₗ
    ((pderiv (b, s) : Derivation R (MvPolynomial (Fin r × Fin m) R) (MvPolynomial (Fin r × Fin m) R)).toLinearMap)
end PI.WGL


