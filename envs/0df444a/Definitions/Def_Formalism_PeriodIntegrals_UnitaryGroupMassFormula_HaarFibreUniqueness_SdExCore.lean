-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:07.364405+00:00
-- url     : https://prove2.me/theorems/a9e01a4b-083b-483e-a94c-22aa61c37255
-- title:
--   Sd Ex Core
-- statement:
--   Definitions and structural lemmas for Sd Ex Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExCore.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.OmFibreUniq.W.SdCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter
open PI.VolStabSW.SdUniqW
open scoped ENNReal
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
section Inv
variable (χ : V → V → ℂ) (hχc : Continuous (fun p : V × V => χ p.1 p.2))
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (hsym : ∀ x y, χ x y = χ y x)
  (hn : ∀ x y, ‖χ x y‖ = 1)
  (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V) (hMc : IsCompact (M : Set V))
  (hMo : IsOpen (M : Set V))
end Inv
end PI.OmFibreUniq.W.SdCore


