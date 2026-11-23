-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstUniqueOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:06.677667+00:00
-- url     : https://prove2.me/theorems/855faa9c-fcd6-4e48-92d4-1131b8a17328
-- title:
--   Quasi Period Const Unique Of
-- statement:
--   Definitions and structural lemmas for Quasi Period Const Unique Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/QuasiPeriodConstUniqueOf.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaZeroLogDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.F
namespace PeriodAreaSignLemmas
def det (L : PeriodPair) : ℝ := (conj L.ω₁ * L.ω₂).im
def sgn (L : PeriodPair) : ℤ := if 0 < (L.ω₂ / L.ω₁).im then 1 else -1
end PeriodAreaSignLemmas
open PeriodAreaSignLemmas
namespace PeriodAreaSignLemmas
end PeriodAreaSignLemmas
end Formalism.L2.Th1.F


