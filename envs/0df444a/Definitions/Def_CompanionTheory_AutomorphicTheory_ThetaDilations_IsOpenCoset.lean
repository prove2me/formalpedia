-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
-- name    : CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:05.278803+00:00
-- url     : https://prove2.me/theorems/1d1f817d-89ae-4d24-adbc-5e452508576f
-- title:
--   Is Open Coset
-- statement:
--   Definitions and structural lemmas for Is Open Coset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/IsOpenCoset.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate
noncomputable section
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {V : Type} [AddCommGroup V] [TopologicalSpace V]
def CO (L : AddSubgroup V) : Prop := IsCompact (L : Set V) ∧ IsOpen (L : Set V)
def ind (a : V) (L : AddSubgroup V) : V → ℂ := Set.indicator {x | x - a ∈ L} fun _ => (1 : ℂ)
section top
variable [IsTopologicalAddGroup V]
end top
variable [MeasurableSpace V] {χ : V → V → ℂ} {μ : Measure V}
section chi
variable (h : NADual V χ μ)
include h
theorem chi_sym (x y : V) : χ x y = χ y x := h.2.2.2.2.2.2.2.2.2.1 x y
theorem chi_norm (x y : V) : ‖χ x y‖ = 1 := h.2.2.2.2.2.2.2.2.2.2.1 x y
theorem chi_add (x x' y : V) : χ (x + x') y = χ x y * χ x' y := h.2.2.2.2.2.2.2.2.2.2.2.1 x x' y
theorem chi_ne (x y : V) : χ x y ≠ 0 := norm_ne_zero_iff.1 (by rw [chi_norm h]; exact one_ne_zero)
theorem chi_add' (x y y' : V) : χ x (y + y') = χ x y * χ x y' := by
  rw [chi_sym h, chi_add h, chi_sym h y, chi_sym h y']
theorem chi_zero (y : V) : χ 0 y = 1 :=
  mul_left_cancel₀ (chi_ne h 0 y) (by rw [← chi_add h, add_zero, mul_one])
theorem chi_neg (x y : V) : χ (-x) y = conj (χ x y) := by
  refine mul_left_cancel₀ (chi_ne h x y) ?_
  rw [← chi_add h, add_neg_cancel, chi_zero h, Complex.mul_conj', chi_norm h]; simp
def perpG (L : AddSubgroup V) : AddSubgroup V where
  carrier := perp χ L
  zero_mem' := fun x _ => by rw [chi_sym h, chi_zero h]
  add_mem' := fun ha hb x hx => by rw [chi_add' h, ha x hx, hb x hx, one_mul]
  neg_mem' := fun {y} hy x hx => by rw [chi_sym h, chi_neg h, chi_sym h, hy x hx, map_one]
end chi
end CompanionTheory.PlacePermOperatorBicommutantSpan


