-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:58:24.381995+00:00
-- url     : https://prove2.me/theorems/6b182b81-a666-4735-a509-f4a1959550f0
-- title:
--   Taylor Wp
-- statement:
--   Definitions and structural lemmas for Taylor Wp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/TaylorWp.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.F
open PowerSeries
namespace TaylorWp
def T (f : ℂ → ℂ) (F : PowerSeries ℂ) : Prop := AnalyticAt ℂ f 0 ∧ taylor0 f = F
end TaylorWp
open TaylorWp
end Formalism.L2.Th1.F


