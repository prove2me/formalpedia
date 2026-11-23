-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_Induced
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_Induced
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:34.753851+00:00
-- url     : https://prove2.me/theorems/46a39ca4-aba2-4ff9-aa18-26e00ee8d09c
-- title:
--   Induced
-- statement:
--   Definitions and structural lemmas for Induced, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RealInducedCharacters/Induced.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_InducedCharRealised
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
namespace BrauerSchur
open scoped BigOperators
section Induced
variable {G : Type*} [Group G] {K : Type*} [Field K] (H : Subgroup G) (ψ : H →* Kˣ)
open scoped Classical in

noncomputable def dot (x : G) : K := if hx : x ∈ H then ((ψ ⟨x, hx⟩ : Kˣ) : K) else 0
theorem dot_mul_of_mem {a b : G} (hb : b ∈ H) : dot H ψ a * dot H ψ b = dot H ψ (a * b) := by
  classical
  unfold dot
  by_cases ha : a ∈ H
  · rw [dif_pos ha, dif_pos hb, dif_pos (H.mul_mem ha hb), ← Units.val_mul, ← map_mul]
    rfl
  · have hab : a * b ∉ H := fun h => ha (by
      have := H.mul_mem h (H.inv_mem hb)
      rwa [mul_inv_cancel_right] at this)
    rw [dif_neg ha, dif_neg hab, zero_mul]
variable {m : ℕ} (t : Fin m → G)
noncomputable def indMat (g : G) : Matrix (Fin m) (Fin m) K :=
  fun i j => dot H ψ ((t i)⁻¹ * g * t j)
theorem indMat_one (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) : indMat H ψ t 1 = 1 := by
  classical
  ext i j
  simp only [indMat, mul_one]
  rw [Matrix.one_apply]
  unfold dot
  split_ifs with h1 h2 h2
  · subst h2
    have e : (⟨(t i)⁻¹ * t i, h1⟩ : H) = 1 := Subtype.ext (inv_mul_cancel _)
    rw [e, map_one, Units.val_one]
  · exact absurd ((ht i j).mp h1) h2
  · exact absurd ((ht i j).mpr h2) h1
  · rfl
theorem indMat_mul (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H)
    (g g' : G) : indMat H ψ t (g * g') = indMat H ψ t g * indMat H ψ t g' := by
  ext i k
  rw [Matrix.mul_apply]
  obtain ⟨j0, hj0⟩ := hc (g' * t k)
  have hb : (t j0)⁻¹ * g' * t k ∈ H := by rwa [mul_assoc]
  rw [Finset.sum_eq_single j0]
  · simp only [indMat]
    rw [dot_mul_of_mem H ψ hb]
    congr 1
    group
  · intro j _ hj
    simp only [indMat]
    have hz : dot H ψ ((t j)⁻¹ * g' * t k) = 0 := by
      classical
      unfold dot
      rw [dif_neg]
      intro hm
      apply hj
      rw [← ht j j0]
      have e : (t j)⁻¹ * t j0 = ((t j)⁻¹ * g' * t k) * ((t j0)⁻¹ * g' * t k)⁻¹ := by group
      rw [e]
      exact H.mul_mem hm (H.inv_mem hb)
    rw [hz, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
noncomputable def indRep (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j) (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H) :
    Representation K G (Fin m → K) where
  toFun g := Matrix.toLin' (indMat H ψ t g)
  map_one' := by rw [indMat_one H ψ t ht, Matrix.toLin'_one]; rfl
  map_mul' g g' := by rw [indMat_mul H ψ t ht hc, Matrix.toLin'_mul]; rfl
end Induced
end BrauerSchur


