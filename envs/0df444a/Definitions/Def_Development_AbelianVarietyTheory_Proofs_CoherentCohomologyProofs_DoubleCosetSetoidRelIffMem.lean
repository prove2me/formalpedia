-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:10.91067+00:00
-- url     : https://prove2.me/theorems/19998e5a-30aa-4b26-bdbd-b785bb49d8e2
-- title:
--   Double Coset Setoid Rel Iff Mem
-- statement:
--   Definitions and structural lemmas for Double Coset Setoid Rel Iff Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/DoubleCosetSetoidRelIffMem.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.DoubleCosetSetoid
section Rep
variable {k G V : Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
def repStabilizer (ρ : Representation k G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
@[simp] theorem mem_repStabilizer (ρ : Representation k G V) (v : V) (g : G) :
    g ∈ repStabilizer ρ v ↔ ρ g v = v := Iff.rfl
end Rep
section Cont
variable {𝕜 G E : Type*} [NontriviallyNormedField 𝕜] [Group G] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E]
def clmStabilizer (π : G →* (E →L[𝕜] E)) (v : E) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, ContinuousLinearMap.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        ContinuousLinearMap.one_apply]
@[simp] theorem mem_clmStabilizer (π : G →* (E →L[𝕜] E)) (v : E) (g : G) :
    g ∈ clmStabilizer π v ↔ π g v = v := Iff.rfl
end Cont
section DoubleCoset
variable {G : Type*} [Group G]
def doubleCosetSetoid (H K : Subgroup G) : Setoid G where
  r x y := ∃ h ∈ H, ∃ k ∈ K, y = h * x * k
  iseqv :=
    { refl := fun x => ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      symm := by
        rintro x y ⟨h, hh, k, hk, rfl⟩
        exact ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, by group⟩
      trans := by
        rintro x y z ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        exact ⟨h' * h, H.mul_mem hh' hh, k * k', K.mul_mem hk hk', by group⟩ }
end DoubleCoset
end GlobalTheory.DoubleCosetSetoid


