-- Prove2me | solution 1 for Auto.aux_cuboidEmbed_translateAxis_exists_or_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:17.804803+00:00
-- url     : https://prove2.me/submissions/732884fe-7184-4cb7-9984-8b772e855c35

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_cuboidEmbed_translateAxis_eq
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
theorem _root_.solution {n : ℕ}
    {ε δ : ℝ} (hε : ε < 1) (hεδ : ε + δ < 1) (i : Fin n)
    (a : aux_ZVector n → ℝ) (k : aux_ZVector n) (u : aux_RVector n)
    (s : ℝ) (hu : ∀ j, 0 ≤ u j ∧ u j < ε) :
    (∃ m : ℤ, ε - u i ≤ s - (m : ℝ) ∧
        s - (m : ℝ) < ε + δ - u i ∧
        aux_cuboidEmbed ε δ i a
          (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) =
          a (aux_translateAxisInt k i m)) ∨
      (¬ ∃ m : ℤ, ε - u i ≤ s - (m : ℝ) ∧
          s - (m : ℝ) < ε + δ - u i) ∧
        aux_cuboidEmbed ε δ i a
          (aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s) = 0 := by
  classical
  by_cases hex : ∃ m : ℤ, ε - u i ≤ s - (m : ℝ) ∧
      s - (m : ℝ) < ε + δ - u i
  · left
    obtain ⟨m, hm⟩ := hex
    refine ⟨m, hm.1, hm.2, ?_⟩
    exact aux_cuboidEmbed_translateAxis_eq hε hεδ i a k u m s hu hm
  · right
    refine ⟨hex, ?_⟩
    unfold aux_cuboidEmbed
    rw [if_neg]
    intro hbox
    apply hex
    let y : aux_RVector n :=
      aux_translateAxis (fun j ↦ (k j : ℝ) + u j) i s
    refine ⟨⌊y i⌋ - k i, ?_⟩
    have hcoordinate : ε ≤ y i - (⌊y i⌋ : ℝ) ∧
        y i - (⌊y i⌋ : ℝ) < ε + δ := by
      simpa [y] using hbox i
    dsimp [y] at hcoordinate ⊢
    simp only [aux_translateAxis, if_pos] at hcoordinate ⊢
    push_cast at hcoordinate ⊢
    simp only [Int.fract] at hcoordinate
    constructor <;> linarith [hcoordinate.1, hcoordinate.2]
end Auto
