-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SpecAbstract
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SpecAbstract
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:29:45.177426+00:00
-- url     : https://prove2.me/theorems/b89bfb69-cd10-4558-b353-ac1d49ba451f
-- title:
--   Spec Abstract
-- statement:
--   Definitions and structural lemmas for Spec Abstract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SpecAbstract.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section SpecAux
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] {X : Type*}
end SpecAux
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors


