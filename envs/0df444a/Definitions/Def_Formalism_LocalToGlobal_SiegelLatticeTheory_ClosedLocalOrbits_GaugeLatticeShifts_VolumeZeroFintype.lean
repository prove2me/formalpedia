-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_VolumeZeroFintype
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_VolumeZeroFintype
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:29.058805+00:00
-- url     : https://prove2.me/theorems/43362a2f-5bbe-4bce-be88-65d1261ffcbe
-- title:
--   Volume Zero Fintype
-- statement:
--   Definitions and structural lemmas for Volume Zero Fintype, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/VolumeZeroFintype.lean

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
open MeasureTheory
open scoped ComplexConjugate
namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
def PF (ι : Type*) : Subalgebra ℂ ((ι → ℝ) → ℂ) :=
  (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ))).range
end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames


