-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_PlacesFrobenius
-- name    : GroundTheory_GlobalFields_Artin_PlacesFrobenius
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T02:18:00.694852+00:00
-- url     : https://prove2.me/theorems/02914ede-2e60-5d47-8608-0c988b6bf8c4
-- title:
--   Places Frobenius
-- statement:
--   Definitions and structural lemmas for Places Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/PlacesFrobenius.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Places
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField
namespace GroundTheory.Global.Artin
section Group
variable {G : Type*} [Group G]
def conjSubgroupOfEquiv (H D : Subgroup G) (x : G) :
    (MulAut.conj x⁻¹ • H : Subgroup G).subgroupOf D ≃
      (MulAut.conj x • D : Subgroup G).subgroupOf H where
  toFun e := ⟨⟨x * ((e : D) : G) * x⁻¹,
      (mem_conj_inv_smul_iff H x _).1 (Subgroup.mem_subgroupOf.1 e.2)⟩, by
    rw [Subgroup.mem_subgroupOf, mem_conj_smul_iff]
    change x⁻¹ * (x * ((e : D) : G) * x⁻¹) * x ∈ D
    rw [show x⁻¹ * (x * ((e : D) : G) * x⁻¹) * x = (e : D) by group]
    exact (e : D).2⟩
  invFun d := ⟨⟨x⁻¹ * ((d : H) : G) * x,
      (mem_conj_smul_iff D x _).1 (Subgroup.mem_subgroupOf.1 d.2)⟩, by
    rw [Subgroup.mem_subgroupOf, mem_conj_inv_smul_iff]
    change x * (x⁻¹ * ((d : H) : G) * x) * x⁻¹ ∈ H
    rw [show x * (x⁻¹ * ((d : H) : G) * x) * x⁻¹ = (d : H) by group]
    exact (d : H).2⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    change x⁻¹ * (x * ((e : D) : G) * x⁻¹) * x = (e : D)
    group
  right_inv d := by
    apply Subtype.ext
    apply Subtype.ext
    change x * (x⁻¹ * ((d : H) : G) * x) * x⁻¹ = (d : H)
    group
end Group
section Finite
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K)) (v : HeightOneSpectrum (𝓞 K))
  (w : HeightOneSpectrum (𝓞 L))
omit [NumberField K] [NumberField L] [IsGalois K L] in

instance normal_inertia_subgroupOf_stabilizer :
    ((w.asIdeal.inertia Gal(L/K)).subgroupOf (MulAction.stabilizer Gal(L/K) w.asIdeal)).Normal :=
  ⟨fun n hn g ↦ by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact mul_mul_inv_mem_inertia g.2 hn⟩
end Finite
end GroundTheory.Global.Artin


