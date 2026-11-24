-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIsLattice
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIsLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:16.473564+00:00
-- url     : https://prove2.me/theorems/c332b985-0cd3-404d-9864-bd559e82a30f
-- title:
--   PLines Is Lattice
-- statement:
--   Definitions and structural lemmas for PLines Is Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIsLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField
namespace KLinesIsLattice
theorem smul_mem_span_of_mem {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K} (hv : v ∈ M) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  rw [← (integralBasis K).sum_repr t, Finset.sum_smul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (M.smul_mem _ hv))
theorem smul_mem_span {K : Type} [Field K] [NumberField K] {ι : Type}
    (M : Submodule (𝓞 K) (ι → K)) (t : K) {v : ι → K}
    (hv : v ∈ Submodule.span ℚ (M : Set (ι → K))) :
    t • v ∈ Submodule.span ℚ (M : Set (ι → K)) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact smul_mem_span_of_mem M t hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul q x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ q hx
def qSpan {K : Type} [Field K] [NumberField K] {ι : Type} (M : Submodule (𝓞 K) (ι → K)) :
    Submodule K (ι → K) where
  carrier := Submodule.span ℚ (M : Set (ι → K))
  add_mem' ha hb := Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  smul_mem' t _ hv := smul_mem_span M t hv
end KLinesIsLattice
end GroundTheory.Heights₂.Heights


