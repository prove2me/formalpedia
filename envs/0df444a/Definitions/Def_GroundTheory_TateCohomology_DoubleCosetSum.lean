-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
-- name    : GroundTheory_TateCohomology_DoubleCosetSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:35.084812+00:00
-- url     : https://prove2.me/theorems/533139e6-835f-41b8-948b-7c3aac20a23f
-- title:
--   Double Coset Sum
-- statement:
--   Definitions and structural lemmas for Double Coset Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/DoubleCosetSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Pointwise
namespace GroundTheory.GroupCoh
variable {G : Type*} [Group G] (T S : Subgroup G)
open scoped Classical in

noncomputable instance fintypeDoubleCosetQuotient [Finite G] :
    Fintype (DoubleCoset.Quotient (T : Set G) S) :=
  @Fintype.ofFinite _ (Quotient.finite (DoubleCoset.setoid (T : Set G) S))
lemma mem_inf_conj_smul_iff (g x : G) :
    x ∈ T ⊓ (MulAut.conj g • S : Subgroup G) ↔ x ∈ T ∧ g⁻¹ * x * g ∈ S := by
  rw [Subgroup.mem_inf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv]
def doubleCosetMap (g : G) : T ⧸ (T ⊓ MulAut.conj g • S).subgroupOf T → G ⧸ S :=
  Quotient.map' (fun t => (t : G) * g) fun a b h => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, mem_inf_conj_smul_iff] at h
    rw [QuotientGroup.leftRel_apply]
    have e : ((a : G) * g)⁻¹ * ((b : G) * g) = g⁻¹ * ((a⁻¹ * b : T) : G) * g := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h.2
variable [Fintype G]
end GroundTheory.GroupCoh


