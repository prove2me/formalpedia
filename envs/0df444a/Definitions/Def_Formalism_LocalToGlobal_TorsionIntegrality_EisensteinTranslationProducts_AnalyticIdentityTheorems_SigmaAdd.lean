-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:14.427157+00:00
-- url     : https://prove2.me/theorems/e481d258-9dd2-42bb-935e-231f0c4b9b24
-- title:
--   Sigma Add
-- statement:
--   Definitions and structural lemmas for Sigma Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaAdd.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace Formalism.L2.Th1.F
namespace SigmaAdditionFormula
variable (L : PeriodPair) (w : ℂ)
def additionQuotient (z : ℂ) : ℂ :=
  wSigma L (z + w) * wSigma L (z - w) / wSigma L z ^ 2 + wSigma L w ^ 2 * L.weierstrassP z
def frobeniusStickelbergerDetMulSigmaCube (z : ℂ) : ℂ :=
  wSigma L (z + w) * wSigma L (z - w)
    + wSigma L w ^ 2 * (dslope (wSigma L) 0 z ^ 2 + wSigma L z ^ 2 * L.weierstrassPExcept 0 z)
end SigmaAdditionFormula
end Formalism.L2.Th1.F


