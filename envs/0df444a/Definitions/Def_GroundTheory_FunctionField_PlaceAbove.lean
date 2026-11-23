-- Prove2me | Definitions.Def_GroundTheory_FunctionField_PlaceAbove
-- name    : GroundTheory_FunctionField_PlaceAbove
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:16.00807+00:00
-- url     : https://prove2.me/theorems/45dc2c29-5407-467d-90b6-b4f404b59f8b
-- title:
--   Place Above
-- statement:
--   Definitions and structural lemmas for Place Above, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceAbove.lean

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Theorems.Thm_GroundTheory_FunctionField_Place_exists_ord_eq_one
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.FunctionField
namespace Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
def LiesOver (w : Place k K') (v : Place k K) : Prop :=
  w.ring.comap (algebraMap K K') = v.ring
omit [IsScalarTower k K K'] in
theorem LiesOver.mem_iff {w : Place k K'} {v : Place k K} (h : w.LiesOver v) {x : K} :
    algebraMap K K' x ∈ w.ring ↔ x ∈ v.ring := by
  rw [← ValuationSubring.mem_comap, h]
omit [IsScalarTower k K K'] in
theorem LiesOver.algebraMap_mem {w : Place k K'} {v : Place k K} (h : w.LiesOver v) {x : K}
    (hx : x ∈ v.ring) : algebraMap K K' x ∈ w.ring :=
  h.mem_iff.2 hx
def comap [Algebra.IsAlgebraic K K'] (w : Place k K') : Place k K where
  ring := w.ring.comap (algebraMap K K')
  ne_top := by
    intro htop
    apply w.ne_top
    have hK : ∀ a : K, algebraMap K K' a ∈ w.ring := fun a =>
      ValuationSubring.mem_comap.1 (htop ▸ ValuationSubring.mem_top a)
    let : Algebra K w.ring := (RingHom.codRestrict (algebraMap K K') w.ring hK).toAlgebra
    have : IsScalarTower K w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine eq_top_iff.2 fun z _ => ?_
    have hz : IsIntegral w.ring z := (Algebra.IsIntegral.isIntegral (R := K) z).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hz
    rw [← hy]
    exact y.2
  algebraMap_mem c := by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact w.algebraMap_mem c
abbrev LiesOver.algebra {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    Algebra v.ring w.ring :=
  (RingHom.codRestrict ((algebraMap K K').comp v.ring.subtype) w.ring
    fun a => h.algebraMap_mem a.2).toAlgebra
omit [IsScalarTower k K K'] in
theorem LiesOver.isLocalHom {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsLocalHom (algebraMap v.ring w.ring) := by
  let := h.algebra
  refine ⟨fun a ha => ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff] at ha ⊢
  have hw : w.ring.valuation (algebraMap K K' (a : K)) = 1 := ha
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hw
    exact zero_ne_one hw
  have hinv : (a : K)⁻¹ ∈ v.ring := by
    rw [← h.mem_iff, ← w.ring.valuation_le_one_iff, map_inv₀, map_inv₀, hw, inv_one]
  have h1 := (v.ring.valuation_le_one_iff _).2 hinv
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))] at h1
  exact le_antisymm (v.ring.valuation_le_one a) h1
section Degree
variable [IsFunctionField k K]
noncomputable def uniformizer (v : Place k K) : K :=
  Classical.choose v.exists_ord_eq_one
variable [IsFunctionField k K']
noncomputable def ramificationIdx (w : Place k K') (v : Place k K) : ℕ :=
  (w.ord (algebraMap K K' v.uniformizer)).toNat
noncomputable def inertiaDeg (w : Place k K') (v : Place k K) : ℕ :=
  w.deg / v.deg
end Degree
end Place
end GroundTheory.FunctionField


