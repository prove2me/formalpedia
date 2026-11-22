-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
-- name    : Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:22.950641+00:00
-- url     : https://prove2.me/theorems/4ed0c35a-3881-45d5-aafb-9dcb0e30c014
-- title:
--   Inv Int V
-- statement:
--   Definitions and structural lemmas for Inv Int V, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/InvIntV.lean

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
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
universe u v w
namespace Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
def Low {σ : Type*} (m : ℕ) (x : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0
section Basic
variable {σ : Type*}
end Basic
end Formalism.FG.InvIntVAux


