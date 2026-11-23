-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaQuasi
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:07.412352+00:00
-- url     : https://prove2.me/theorems/725b2961-3792-439d-ae4a-b435aae2b66b
-- title:
--   Sigma Quasi
-- statement:
--   Definitions and structural lemmas for Sigma Quasi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/SigmaQuasi.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_Legendre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Th1.F
namespace PeriodLatticeBasisLemmas
def QP (L : PeriodPair) (ω c : ℂ) : Prop :=
  ∀ z : ℂ, wSigma L (z + ω) = c * Complex.exp (wEta L ω * (z + ω / 2)) * wSigma L z
end PeriodLatticeBasisLemmas
end Formalism.L2.Th1.F


