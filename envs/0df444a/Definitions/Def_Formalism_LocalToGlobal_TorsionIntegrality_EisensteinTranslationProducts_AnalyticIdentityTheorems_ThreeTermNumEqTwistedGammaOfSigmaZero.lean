-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_ThreeTermNumEqTwistedGammaOfSigmaZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:34.935545+00:00
-- url     : https://prove2.me/theorems/0741f873-930e-4894-bad5-5d50293ecbfd
-- title:
--   Three Term Num Eq Twisted Gamma Of Sigma Zero
-- statement:
--   Definitions and structural lemmas for Three Term Num Eq Twisted Gamma Of Sigma Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/EisensteinTranslationProducts/AnalyticIdentityTheorems/ThreeTermNumEqTwistedGammaOfSigmaZero.lean

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
namespace ThreeTermRelation
variable (L : PeriodPair) (b c : ℂ)
def threeTermDet (x : ℂ) : ℂ :=
  (L.weierstrassP b * L.derivWeierstrassP c - L.weierstrassP c * L.derivWeierstrassP b)
    - L.weierstrassP x * (L.derivWeierstrassP c - L.derivWeierstrassP b)
    + L.derivWeierstrassP x * (L.weierstrassP c - L.weierstrassP b)
def nAux (x : ℂ) : ℂ := threeTermDet L b c x * wSigma L x ^ 3
def threeTermDenom (x : ℂ) : ℂ := wSigma L (x + (b + c)) * wSigma L (x + -b) * wSigma L (x + -c)
def threeTermQuotient (x : ℂ) : ℂ := nAux L b c x / threeTermDenom L b c x
def frobeniusStickelbergerDetMulSigmaCube (x : ℂ) : ℂ :=
  (L.weierstrassP b * L.derivWeierstrassP c - L.weierstrassP c * L.derivWeierstrassP b)
      * wSigma L x ^ 3
    - (x * dslope (wSigma L) 0 x ^ 3 + L.weierstrassPExcept 0 x * wSigma L x ^ 3)
      * (L.derivWeierstrassP c - L.derivWeierstrassP b)
    + (-2 * dslope (wSigma L) 0 x ^ 3 + L.derivWeierstrassPExcept 0 x * wSigma L x ^ 3)
      * (L.weierstrassP c - L.weierstrassP b)
end ThreeTermRelation
end Formalism.L2.Th1.F


