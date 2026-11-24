-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_EvXTemperate
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_FockSpaces_EvXTemperate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:35.757542+00:00
-- url     : https://prove2.me/theorems/8faefe9d-95ce-488e-ab4c-afbd2719a17d
-- title:
--   Ev XTemperate
-- statement:
--   Definitions and structural lemmas for Ev XTemperate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/FockSpaces/EvXTemperate.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap
open PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
def eucl (m n : ℕ) (s : ℝ) (hs : s ≠ 0) : (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  ((LinearEquiv.smulOfNeZero ℝ (Fin m → Fin n → ℂ) s hs).trans
    ((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm)).toContinuousLinearEquiv
end PositivityTheory.SiegelWeilFormula.KFock
end


