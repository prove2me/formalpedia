-- Prove2me | Definitions.Def_GroundTheory_LocalFields_Interface
-- name    : GroundTheory_LocalFields_Interface
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:25.371234+00:00
-- url     : https://prove2.me/theorems/45dbbb4e-7b51-4aad-bfde-1e10a415df62
-- title:
--   Interface
-- statement:
--   Definitions and structural lemmas for Interface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Interface.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel
section Algebraic
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
instance valuation_hasExtension : (valuation K).HasExtension (valuation L) where
  val_isEquiv_comap a b := by
    rw [Valuation.comap_apply, Valuation.comap_apply, ← Valuation.vle_iff_le,
      ← Valuation.vle_iff_le, ValuativeExtension.vle_iff_vle]
@[simp]
theorem coe_algebraMap_integer (x : 𝒪[K]) :
    ((algebraMap 𝒪[K] 𝒪[L] x : 𝒪[L]) : L) = algebraMap K L (x : K) :=
  rfl
example : IsScalarTower 𝒪[K] 𝒪[L] L := inferInstance
example : IsScalarTower 𝒪[K] K L := inferInstance
example : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) := inferInstance
example : Algebra 𝓀[K] 𝓀[L] := inferInstance
example : FaithfulSMul 𝒪[K] 𝒪[L] := inferInstance
end Algebraic
section Topological
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
theorem continuous_algebraMap : Continuous (algebraMap K L) := by
  refine continuous_of_continuousAt_zero (algebraMap K L) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero L)]
  intro γ _
  obtain ⟨δ, hδ0, hδ1⟩ := IsNontrivial.exists_lt_one (R := K)
  obtain ⟨a, rfl⟩ := valuation_surjective δ
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hδ0
  have hb : valuation L (algebraMap K L a) < 1 := by
    exact (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr hδ1
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hb γ
  refine ⟨Units.mk0 (valuation K (a ^ n)) (by simp [ha0]), trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx ⊢
  calc valuation L (algebraMap K L x) < valuation L (algebraMap K L (a ^ n)) := by
        rw [← (valuation L).vlt_iff_lt, ValuativeExtension.vlt_iff_vlt, (valuation K).vlt_iff_lt]
        exact hx
    _ = valuation L (algebraMap K L a) ^ n := by simp
    _ < γ := hn
instance continuousSMul : ContinuousSMul K L :=
  continuousSMul_of_algebraMap K L (continuous_algebraMap K L)
end Topological
end GroundTheory.LocalField


