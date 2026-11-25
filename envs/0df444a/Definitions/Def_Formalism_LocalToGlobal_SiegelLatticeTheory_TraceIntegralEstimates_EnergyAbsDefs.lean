-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T04:47:48.243476+00:00
-- url     : https://prove2.me/theorems/7d25e8a0-39f8-45f4-b477-1aac736a58ef
-- title:
--   Energy Abs Defs
-- statement:
--   Definitions and structural lemmas for Energy Abs Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/EnergyAbsDefs.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
def yv (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) (e : V) : HH :=
  ∫ z, ∫ s in Ω, ⟪W (s⁻¹ * z), e⟫_ℂ • σ (s⁻¹ * z) w ∂μS ∂ν
def Yop (μS ν : Measure G) (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (Ω : Set G) : V →L[ℂ] HH :=
  ∑ i, (innerSL ℂ (stdOrthonormalBasis ℂ V i)).smulRight (yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i))
end Formalism.L2.S.Pv.EnergyAbs


