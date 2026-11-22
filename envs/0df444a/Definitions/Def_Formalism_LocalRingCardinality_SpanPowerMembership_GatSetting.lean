-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:29.96754+00:00
-- url     : https://prove2.me/theorems/5f3c44b5-643b-4511-b4a3-c7211b925c7f
-- title:
--   Gat Setting
-- statement:
--   Definitions and structural lemmas for Gat Setting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GatSetting.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LevelValuationRings
open Formalism.MainNotions.G QuadraticAlgebra
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
abbrev Wn : Type := WittVector p (GaloisField p n)
abbrev Qn : Type := FractionRing (Wn p n)
abbrev On : Type := QuadraticAlgebra (Wn p n) (p : Wn p n) 0
instance instDomOn : IsDomain (On p n) := GatR.isDomain (WittVector.irreducible p)
instance instDvrOn : IsDiscreteValuationRing (On p n) := GatR.isDVR (WittVector.irreducible p)
abbrev Kn : Type := FractionRing (On p n)
def sigN : Qn p n ≃+* Qn p n :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (GaloisField p n))
theorem inj_WK : Function.Injective ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) :=
  (IsFractionRing.injective (On p n) (Kn p n)).comp algebraMap_injective
def iotaN : Qn p n →+* Kn p n := IsFractionRing.lift (inj_WK p n)
end Formalism.BasicNotions.Examples₂.LevelValuationRings


