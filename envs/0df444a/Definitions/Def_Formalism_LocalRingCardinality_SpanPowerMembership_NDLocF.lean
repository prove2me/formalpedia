-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T16:27:32.755353+00:00
-- url     : https://prove2.me/theorems/76e900eb-f60f-438a-936a-1e0b35936b22
-- title:
--   NDLoc F
-- statement:
--   Definitions and structural lemmas for NDLoc F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocF.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)
def toOm : ↥(OL LL) →+* PadicAlgCl l := LL.1.val.toRingHom.comp (OL LL).val.toRingHom
theorem inducing_toOm : Topology.IsInducing (toOm LL) :=
  Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
instance OL_topRing : IsTopologicalRing ↥(OL LL) :=
  { toContinuousAdd := (inducing_toOm LL).continuousAdd (toOm LL)
    toContinuousMul := (inducing_toOm LL).continuousMul (toOm LL)
    toContinuousNeg := (inducing_toOm LL).continuousNeg (map_neg (toOm LL)) }
def toC : ↥(OL LL) →+* ℂ_[l] := (algebraMap (PadicAlgCl l) ℂ_[l]).comp (toOm LL)
def toFrac : ↥LL.1 →+* FractionRing ↥(OL LL) := (FractionRing.algEquiv ↥(OL LL) ↥LL.1).symm.toRingEquiv.toRingHom
end Formalism.BasicNotions.Examples₂.LB


