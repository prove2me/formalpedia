-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightMonotonicity
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:53:50.247887+00:00
-- url     : https://prove2.me/theorems/16ebb0b7-fac5-4d21-9880-8e91370e707b
-- title:
--   Weight Monotonicity
-- statement:
--   Definitions and structural lemmas for Weight Monotonicity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightMonotonicity.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.DegreeMapArithmetic
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
section Dual
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Dual
section Weight
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Weight
end Formalism.FourierDecayAlt.P.DegreeMapArithmetic
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr DegreeMapArithmetic
end Formalism.FourierDecayAlt.P


