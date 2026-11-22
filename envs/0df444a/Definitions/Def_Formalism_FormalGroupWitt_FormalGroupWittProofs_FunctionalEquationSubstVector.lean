-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:04.225804+00:00
-- url     : https://prove2.me/theorems/0767856c-6a26-49d2-8726-c70d6b1c1bee
-- title:
--   Functional Equation Subst Vector
-- statement:
--   Definitions and structural lemmas for Functional Equation Subst Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/FunctionalEquationSubstVector.lean

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormSigmaLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Lemmata_MultivariateIntegrals_IntegralMv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
namespace Formalism.FG.KeyVAux
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
def Bd {τ : Type w} (C : ℝ) (F : MvPowerSeries τ K) : Prop :=
  ∀ d, ‖MvPowerSeries.coeff d F‖ ≤ C
end Formalism.FG.KeyVAux


