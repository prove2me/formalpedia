-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SecondCoordinateVectorMemSpan
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:16:18.564496+00:00
-- url     : https://prove2.me/theorems/9c65ace8-6fa0-4975-a6f5-a8da6aaebb02
-- title:
--   Second Coordinate Vector Mem Span
-- statement:
--   Definitions and structural lemmas for Second Coordinate Vector Mem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/SecondCoordinateVectorMemSpan.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_ValNatCastLtOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_LocSplitChiOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteAdelicComparison_AdelicLatticeToLocalLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA
open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists
def hl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (X Y : Fin I.n → RV I v) : RV I v :=
  Formalism.UG.hform (sigV I v) (I.J.map (inclV I v)) X Y
section PrSpan
variable {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (P : Matrix (Fin n) (Fin n) K)
end PrSpan
end PI.UnitaryGroupMassFormula.ScXuExists.BrA
end


