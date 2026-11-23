-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:58.768801+00:00
-- url     : https://prove2.me/theorems/df6f9e96-b39b-492d-b622-396e9032fba9
-- title:
--   Exists Small Dual Lattices
-- statement:
--   Definitions and structural lemmas for Exists Small Dual Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSmallDualLattices.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
namespace GlobalTheory.JR.DualLattice
variable {F : Type} [NontriviallyNormedField F]
variable {V : Type} [AddCommGroup V] [Module F V]
def box [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) : AddSubgroup V where
  carrier := {x | ∀ i, ‖e.repr x i‖ ≤ r}
  zero_mem' := by intro i; simpa using hr
  add_mem' := by
    intro a b ha hb i
    rw [map_add, Finsupp.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
  neg_mem' := by
    intro a ha i
    simpa using ha i
noncomputable def coordHomeo [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) : V ≃ₜ (ι → F) :=
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  { e.equivFun.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.equivFun.symm.toLinearMap }
end GlobalTheory.JR.DualLattice


