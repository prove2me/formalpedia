-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormTransitivityGroup_AddLeftInvariantVolumeSingle
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormTransitivityGroup_AddLeftInvariantVolumeSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:38.839794+00:00
-- url     : https://prove2.me/theorems/4c86569b-f677-4449-8124-8d809887cb10
-- title:
--   Add Left Invariant Volume Single
-- statement:
--   Definitions and structural lemmas for Add Left Invariant Volume Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormTransitivityGroup/AddLeftInvariantVolumeSingle.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NormTransG
import Definitions.Def_Formalism_PeriodIntegrals_HeisNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace PI.NormTransGW
variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]
noncomputable def phi (A : ℝ) (F : (T → I → J → ℂ) → ℂ) (z : T → I → J → ℂ) : ℝ :=
  ‖F z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re)
instance sigmaFinite_volume_single : SigmaFinite (volume : Measure (J → ℂ)) := inferInstance
instance addLeftInvariant_volume_single : (volume : Measure (J → ℂ)).IsAddLeftInvariant := inferInstance
instance sigmaFinite_volume_double : SigmaFinite (volume : Measure (I → J → ℂ)) := inferInstance
instance addLeftInvariant_volume_double : (volume : Measure (I → J → ℂ)).IsAddLeftInvariant := inferInstance
instance addLeftInvariant_volume_triple : (volume : Measure (T → I → J → ℂ)).IsAddLeftInvariant := inferInstance
instance vol_vinv : VAddInvariantMeasure (T → I → J → ℂ) (T → I → J → ℂ) volume := inferInstance
instance vol_vinvLat (La' : AddSubgroup (T → I → J → ℂ)) : VAddInvariantMeasure La' (T → I → J → ℂ) volume :=
  inferInstance
end PI.NormTransGW


