-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCasA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:26.111799+00:00
-- url     : https://prove2.me/theorems/365f1bdb-2a82-4a8b-9d80-5131a95149e4
-- title:
--   Core Cas A
-- statement:
--   Definitions and structural lemmas for Core Cas A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreCasA.lean

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
open Matrix
open scoped InnerProductSpace
namespace PositivityTheory.KReal
section Ops
variable {I : Type} [Fintype I] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def matOp (m : Matrix I I ℂ) : Module.End ℂ (PiLp 2 (fun _ : I => V)) where
  toFun Θ := WithLp.toLp 2 (fun i => ∑ j, m i j • Θ j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp [Finset.smul_sum, smul_comm a]
def valOp (A : Module.End ℂ V) : Module.End ℂ (PiLp 2 (fun _ : I => V)) where
  toFun Θ := WithLp.toLp 2 (fun i => A (Θ i))
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp
end Ops
end PositivityTheory.KReal
end


