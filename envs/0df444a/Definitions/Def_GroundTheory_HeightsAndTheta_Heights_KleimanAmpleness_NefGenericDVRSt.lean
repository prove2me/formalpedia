-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefGenericDVRSt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_NefGenericDVRSt
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:14:05.749128+00:00
-- url     : https://prove2.me/theorems/619fd66d-a9cf-4319-b644-cebac2614d8d
-- title:
--   Nef Generic DVRSt
-- statement:
--   Definitions and structural lemmas for Nef Generic DVRSt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/NefGenericDVRSt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
noncomputable section
def NefGenericDVR.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (F : Type) [Field F] [Algebra O F]
    [IsFractionRing O F] (Ω : Type) [Field Ω] [Algebra O Ω] [Algebra F Ω] [IsScalarTower O F Ω]
    (N : ℕ) (x : Fin (N + 1) → Ω) (M : Kleiman.LineBundle O x),
    Kleiman.NefAbove M.toSubSystem ((IsLocalRing.maximalIdeal O).map (C : O →+* Kleiman.Poly O N)) →
    Kleiman.Nef (M.toSubSystem.extend F)
abbrev exO : Type := PowerSeries ℚ
abbrev exF : Type := FractionRing exO
abbrev exΩ : Type := RatFunc exF
theorem NefGenericDVR.hyps :
    Kleiman.NefAbove (Kleiman.twistBundle exO (Kleiman.lineX exF) 0).toSubSystem
      ((IsLocalRing.maximalIdeal exO).map (C : exO →+* Kleiman.Poly exO 1)) :=
  fun pp _ _ => by
    rw [show (Kleiman.twistBundle exO (Kleiman.lineX exF) 0).toSubSystem =
      Kleiman.twistSys exO (Kleiman.lineX exF) 0 from rfl, Kleiman.interNum_twistSys_zero]
example (h : NefGenericDVR.Statement) :=
  h exO exF exΩ 1 (Kleiman.lineX exF) (Kleiman.twistBundle exO (Kleiman.lineX exF) 0) NefGenericDVR.hyps
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


