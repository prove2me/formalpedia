-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:18.553875+00:00
-- url     : https://prove2.me/theorems/422028b1-9d91-4cda-b45c-692dc72f300a
-- title:
--   Sing To Diff
-- statement:
--   Definitions and structural lemmas for Sing To Diff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/SingToDiff.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Filter Topology Function
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
namespace STD
variable {n : ℕ}
def ell (β : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((2 * Real.pi * Complex.I) • ((Matrix.traceLinearMap (Fin n) ℂ ℂ).comp (LinearMap.mulLeft ℂ β)))
def ml (σ : Equiv.Perm (Fin n)) : Fin (Fintype.card (Fin n)) → Fin n × Fin n :=
  fun i => ((Fintype.equivFin (Fin n)).symm i, σ ((Fintype.equivFin (Fin n)).symm i))
end STD
end PositivityTheory.Rg.Sw.LVs


