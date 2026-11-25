-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_ConvGGG
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_ConvGGG
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:36.975408+00:00
-- url     : https://prove2.me/theorems/72ce4a31-a9db-5fc3-ae6f-d7a28b4b2e96
-- title:
--   Conv GGG
-- statement:
--   Definitions and structural lemmas for Conv GGG, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/ConvGGG.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
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
open scoped InnerProductSpace ENNReal
namespace Formalism.L2.S.Pv.ConvG
open Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
  {V V' : Type} [NormedAddCommGroup V] [NormedAddCommGroup V']
@[irreducible] def PhiGG (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (W' : G → V') (γ : G) (a b : G) : ℝ≥0∞ :=
  ‖⟪σ a w, σ γ (σ b w)⟫_ℂ‖ₑ * ‖W a‖ₑ * ‖W' b‖ₑ
end Formalism.L2.S.Pv.ConvG


