-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirVolumeRatios_VolumeClassRepresentatives_ChangeOfVariables
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirVolumeRatios_VolumeClassRepresentatives_ChangeOfVariables
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:17.137568+00:00
-- url     : https://prove2.me/theorems/7c927ba9-a0d3-46f3-bd5f-5cf007d448ae
-- title:
--   Change Of Variables
-- statement:
--   Definitions and structural lemmas for Change Of Variables, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CasimirVolumeRatios/VolumeClassRepresentatives/ChangeOfVariables.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.S.S7.PositiveOrthantChangeOfVariables
open MeasureTheory Set
open scoped ENNReal
def posO (a : ℕ) : Set (Fin a → ℝ) := Set.univ.pi fun _ => Set.Ioi (0 : ℝ)
def chv {a : ℕ} (e : Fin a → ℝ) (t : Fin a → ℝ) : Fin a → ℝ := fun i => t i ^ (-(e i)⁻¹)
def chvD {a : ℕ} (e : Fin a → ℝ) (t : Fin a → ℝ) : (Fin a → ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi fun i => ((-(e i)⁻¹) * t i ^ (-(e i)⁻¹ - 1)) • ContinuousLinearMap.proj i
end Formalism.L2.S.S7.PositiveOrthantChangeOfVariables
end


