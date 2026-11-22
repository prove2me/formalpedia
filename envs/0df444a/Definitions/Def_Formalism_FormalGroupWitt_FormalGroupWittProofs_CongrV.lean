-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:31.218074+00:00
-- url     : https://prove2.me/theorems/58e755e9-49cc-402d-9553-6fbd0ed35a16
-- title:
--   Congr V
-- statement:
--   Definitions and structural lemmas for Congr V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
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
namespace Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
section Local
variable {R : Type u} [CommRing R] {τ : Type w}
def Zd (d : τ →₀ ℕ) (x : MvPowerSeries τ R) : Prop := ∀ e ≤ d, coeff e x = 0
end Local
section Norm
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
def ofFun (g : (τ →₀ ℕ) → K) : MvPowerSeries τ K := g
end Norm
end Formalism.FG.CongrVAux


