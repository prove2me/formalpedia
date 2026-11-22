-- Prove2me | Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
-- name    : Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:47:51.864796+00:00
-- url     : https://prove2.me/theorems/343eca1d-11be-4f68-817a-152badb77836
-- title:
--   Inv Int
-- statement:
--   Definitions and structural lemmas for Inv Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v
namespace Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
section Basic
variable {K : Type u} [NormedField K] {ι : Type v}
def Low (m : ℕ) (x : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0
end Basic
section Ultra
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
end Ultra
section Inv
variable {K : Type u} [NormedField K] {ι : Type v}
def tail2 (f : PowerSeries K) : PowerSeries K := PowerSeries.mk fun n => coeff (n + 2) f
end Inv
end Formalism.LT.InvIntP


