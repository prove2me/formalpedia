-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TCCalc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:27.999265+00:00
-- url     : https://prove2.me/theorems/c609d81f-ee8c-4bef-b8f8-b9978f6f34e1
-- title:
--   TCCalc
-- statement:
--   Definitions and structural lemmas for TCCalc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/AnalyticDeterminants/TCCalc.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_TopCompS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff
open Set Filter Topology
namespace PositivityTheory.Rg.Sw.LVs.TC
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
end
def predPerm {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (h0 : σ 0 = 0) : Equiv.Perm (Fin k) where
  toFun i := (σ i.succ).pred (fun h => Fin.succ_ne_zero i (σ.injective (h.trans h0.symm)))
  invFun i := (σ⁻¹ i.succ).pred (fun h => by
    have : σ⁻¹ 0 = 0 := by rw [Equiv.Perm.inv_eq_iff_eq, h0]
    exact Fin.succ_ne_zero i ((σ⁻¹).injective (h.trans this.symm)))
  left_inv i := by simp
  right_inv i := by simp
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
end
section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
end
end PositivityTheory.Rg.Sw.LVs.TC


