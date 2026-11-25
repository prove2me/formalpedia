-- Prove2me | Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
-- name    : CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:51:13.613266+00:00
-- url     : https://prove2.me/theorems/54a4ffb8-eade-4f2e-9435-9610602cc448
-- title:
--   Exists
-- statement:
--   Definitions and structural lemmas for Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/BesselParameterIntegrals/SigmaFiniteQuotients/Exists.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace Set
open scoped ENNReal NNReal Pointwise
noncomputable section
namespace CompanionTheory.D.Upq.Quot
section Abstract
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
end Abstract
open PI CompanionTheory.D.Upq.ModEx
variable {m : ℕ} {G S : Set (Matrix (Fin m) (Fin m) ℂ)}
end CompanionTheory.D.Upq.Quot
end


