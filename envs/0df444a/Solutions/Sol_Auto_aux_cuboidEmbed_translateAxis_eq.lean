-- Prove2me | solution 1 for Auto.aux_cuboidEmbed_translateAxis_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:39:47.464513+00:00
-- url     : https://prove2.me/submissions/d4286d46-3333-420d-8f8f-b22b84e56b69

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_floor_intCast_add_of_mem_Ico
section
@[expose] public section
namespace Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
@[simp] private theorem aux_orbit_zero {X : Type*} (S : Fin 0 → X → X)
    (k : Fin 0 → ℕ) : aux_orbit S k = id :=
  rfl
@[simp] private theorem aux_orbit_succ {X : Type*} {n : ℕ}
    (S : Fin (n + 1) → X → X) (k : Fin (n + 1) → ℕ) :
    aux_orbit S k = (S 0)^[k 0] ∘
      aux_orbit (fun i ↦ S i.succ) (fun i ↦ k i.succ) :=
  rfl
section
universe v
end
namespace aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
end aux_CuboidNorm
namespace aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
end aux_ErgodicBox
end
end Auto
end
end

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} {ε δ : ℝ}
    (hε : ε < 1) (hεδ : ε + δ < 1) (i : Fin n)
    (a : aux_ZVector n → ℝ) (k : aux_ZVector n) (u : aux_RVector n)
    (m : ℤ) (s : ℝ) (hu : ∀ j, 0 ≤ u j ∧ u j < ε)
    (hs : ε - u i ≤ s - m ∧ s - m < ε + δ - u i) :
    aux_cuboidEmbed ε δ i a
        (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) =
      a (aux_translateAxisInt k i m) := by
  let r : ℝ := u i + s - m
  have hr0 : 0 ≤ r := by
    dsimp [r]
    linarith [hs.1, (hu i).1, (hu i).2]
  have hr1 : r < ε + δ := by
    dsimp [r]
    linarith [hs.2]
  have hfloor : ∀ j,
      ⌊aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s j⌋ =
        aux_translateAxisInt k i m j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [aux_translateAxis, aux_translateAxisInt, ite_true]
      have hrewrite : (k i : ℝ) + u i + s =
          ((k i + m : ℤ) : ℝ) + r := by
        dsimp [r]
        push_cast
        ring
      rw [hrewrite]
      exact aux_floor_intCast_add_of_mem_Ico (k i + m) hr0
        (lt_trans hr1 hεδ)
    · simp only [aux_translateAxis, aux_translateAxisInt, if_neg hji]
      simpa only [add_zero] using
        aux_floor_intCast_add_of_mem_Ico (k j) (hu j).1
          (lt_trans (hu j).2 hε)
  unfold aux_cuboidEmbed
  rw [if_pos]
  · congr 1
    funext j
    exact hfloor j
  · intro j
    by_cases hji : j = i
    · subst j
      simp only [if_true]
      rw [hfloor]
      simp only [aux_translateAxis, aux_translateAxisInt, if_pos]
      push_cast
      constructor <;> linarith [hs.1, hs.2]
    · rw [if_neg hji]
      rw [hfloor]
      simpa [aux_translateAxis, aux_translateAxisInt, hji] using hu j
end Auto
