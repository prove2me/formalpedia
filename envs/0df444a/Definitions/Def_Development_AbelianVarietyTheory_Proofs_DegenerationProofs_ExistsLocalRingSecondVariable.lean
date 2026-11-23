-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalRingSecondVariable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:11.239795+00:00
-- url     : https://prove2.me/theorems/5906c74f-2011-43ee-86d0-9fefab9903a6
-- title:
--   Exists Local Ring Second Variable
-- statement:
--   Definitions and structural lemmas for Exists Local Ring Second Variable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLocalRingSecondVariable.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.TwoVarValRing
theorem not_X_dvd_iff_weightedOrder {σ R : Type} [DecidableEq σ] [Semiring R] (s : σ)
    (f : MvPowerSeries σ R) :
    ¬ MvPowerSeries.X s ∣ f ↔ f.weightedOrder (Pi.single s 1) = 0 := by
  have h := MvPowerSeries.weightedOrder_eq_nat (f := f) (Pi.single s 1) (n := 0)
  rw [Nat.cast_zero] at h
  rw [h, MvPowerSeries.X_dvd_iff]
  simp only [Finsupp.weight_single_one_apply, not_forall, Nat.not_lt_zero, false_imp_iff,
    implies_true, and_true]
  constructor
  · rintro ⟨m, h1, h2⟩; exact ⟨m, h2, h1⟩
  · rintro ⟨m, h1, h2⟩; exact ⟨m, h2, h1⟩
theorem not_X_dvd_mul {σ R : Type} [DecidableEq σ] [Semiring R] [NoZeroDivisors R] (s : σ)
    {f g : MvPowerSeries σ R} (hf : ¬ MvPowerSeries.X s ∣ f) (hg : ¬ MvPowerSeries.X s ∣ g) :
    ¬ MvPowerSeries.X s ∣ f * g := by
  rw [not_X_dvd_iff_weightedOrder] at *
  rw [MvPowerSeries.weightedOrder_mul, hf, hg, add_zero]
theorem not_X_dvd_one {σ R : Type} [DecidableEq σ] [Semiring R] [Nontrivial R] (s : σ) :
    ¬ MvPowerSeries.X s ∣ (1 : MvPowerSeries σ R) := by
  rw [not_X_dvd_iff_weightedOrder, MvPowerSeries.weightedOrder_one]
noncomputable def locSecondVar (k : Type) [Field k] :
    Subalgebra k (FractionRing (MvPowerSeries (Fin 2) k)) where
  carrier := {x | ∃ u v : MvPowerSeries (Fin 2) k, ¬ MvPowerSeries.X 1 ∣ v ∧
    x * algebraMap (MvPowerSeries (Fin 2) k) _ v = algebraMap (MvPowerSeries (Fin 2) k) _ u}
  mul_mem' := by
    rintro x y ⟨u, v, hv, h⟩ ⟨u', v', hv', h'⟩
    refine ⟨u * u', v * v', not_X_dvd_mul _ hv hv', ?_⟩
    rw [map_mul, map_mul, ← h, ← h']; ring
  add_mem' := by
    rintro x y ⟨u, v, hv, h⟩ ⟨u', v', hv', h'⟩
    refine ⟨u * v' + u' * v, v * v', not_X_dvd_mul _ hv hv', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, ← h, ← h']; ring
  algebraMap_mem' := by
    intro r
    refine ⟨algebraMap k _ r, 1, not_X_dvd_one _, ?_⟩
    rw [map_one, mul_one, ← IsScalarTower.algebraMap_apply]
theorem isUnit_locSecondVar (k : Type) [Field k] (x : locSecondVar k) (u v : MvPowerSeries (Fin 2) k)
    (hu : ¬ MvPowerSeries.X 1 ∣ u)
    (h : (x : FractionRing (MvPowerSeries (Fin 2) k)) * algebraMap (MvPowerSeries (Fin 2) k) _ v
      = algebraMap (MvPowerSeries (Fin 2) k) _ u) : IsUnit x := by
  have hu0 : algebraMap (MvPowerSeries (Fin 2) k) (FractionRing (MvPowerSeries (Fin 2) k)) u
      ≠ 0 := by
    rw [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    exact hu (dvd_zero _)
  have hx : (x : FractionRing (MvPowerSeries (Fin 2) k)) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact hu0 h.symm
  refine IsUnit.of_mul_eq_one (⟨(x : FractionRing (MvPowerSeries (Fin 2) k))⁻¹, v, u, hu, ?_⟩ : locSecondVar k) ?_
  · rw [← h, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  · exact Subtype.ext (mul_inv_cancel₀ hx)
instance isLocalRing_locSecondVar (k : Type) [Field k] : IsLocalRing (locSecondVar k) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨u, v, hv, h⟩ := x.2
  by_cases hu : MvPowerSeries.X 1 ∣ u
  · right
    refine isUnit_locSecondVar k _ (v - u) v (fun h' => hv ?_) ?_
    · simpa using dvd_add h' hu
    · rw [map_sub, ← h]
      push_cast
      ring
  · exact Or.inl (isUnit_locSecondVar k x u v hu h)
end GlobalTheory.TwoVarValRing


