-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EtaEis
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_EtaEis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:34.239199+00:00
-- url     : https://prove2.me/theorems/839cde7b-aba7-4c1f-8e29-91cf51c62560
-- title:
--   Eta Eis
-- statement:
--   Definitions and structural lemmas for Eta Eis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/EtaEis.lean

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
open scoped BigOperators ComplexConjugate Topology
open Filter
namespace Formalism.L2.Th1.F
namespace EtaEis
def tm (l x : ℂ) : ℂ := 1 / (x - l) + 1 / l + x / l ^ 2
end EtaEis
end Formalism.L2.Th1.F


