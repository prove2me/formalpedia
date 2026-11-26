-- Prove2me | solution 1 for Auto.aux_ErgodicBox.finite_box_bound_of_finite_sum_cancelled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:11.248016+00:00
-- url     : https://prove2.me/submissions/e758caca-3898-4792-8018-88a19081284c

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_box_subset_double
public import Theorems.Thm_Auto_aux_ErgodicBox_cancel_box_ratio
public import Theorems.Thm_Auto_aux_ErgodicBox_holder_truncOrbit_norms
public import Theorems.Thm_Auto_aux_ErgodicBox_finite_box_ergodic_to_discrete
public import Theorems.Thm_Auto_aux_ErgodicBox_aemeasurable_truncOrbit_normProduct
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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Auto.aux_ErgodicBox
theorem _root_.solution
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {n J M : ℕ}
    (hM : 0 < M)
    (T : (Fin n → ℕ) → X → X)
    (hT : ∀ k ∈ box n (M + M),
      MeasurePreserving (T k) μ μ)
    (p : Fin n → ℝ≥0∞) (N : Fin (J + 1) → ℕ)
    (f : Fin n → X → ℝ) (hf : ∀ i, MemLp (f i) (p i) μ)
    (hp0 : ∀ i, p i ≠ 0) (hptop : ∀ i, p i ≠ ∞)
    (hpreal : ∀ i, 0 < (p i).toReal)
    (hqsum : ∑ i, 2 / (p i).toReal = 1)
    (a : Fin (J + 1) → X → ℝ) (d : Fin J → X → ℝ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ)
    (hjump : ∀ j x, d j x = a j.succ x - a j.castSucc x)
    (A : ℝ≥0∞)
    (hlocal : ∀ x, ∑ j : Fin J, ∑ k ∈ box n M,
      ‖aux_discreteAverage (N j.succ)
          (fun i ↦ truncOrbit (box n (M + M)) T (f i) x) k -
        aux_discreteAverage (N j.castSucc)
          (fun i ↦ truncOrbit (box n (M + M)) T (f i) x) k‖ₑ
        ^ (2 : ℕ) ≤
        A * ∏ i, eLpNorm
          (truncOrbit (box n (M + M)) T (f i) x)
            (p i) Measure.count ^ 2)
    (haverage : ∀ (x : X) (k : Fin n → ℕ) (q : Fin (J + 1)),
      k ∈ box n M →
      aux_discreteAverage (N q)
          (fun i ↦ truncOrbit (box n (M + M)) T (f i) x) k =
        a q (T k x)) :
    ∑ j, eLpNorm (d j) 2 μ ^ 2 ≤
      A * ((2 ^ n : ℕ) : ℝ≥0∞) * ∏ i, eLpNorm (f i) (p i) μ ^ 2 := by
  let B : Finset (Fin n → ℕ) := box n M
  let B' : Finset (Fin n → ℕ) := box n (M + M)
  let F : X → Fin n → (Fin n → ℕ) → ℝ :=
    fun x i ↦ truncOrbit B' T (f i) x
  let Q : X → ℝ≥0∞ := fun x ↦
    ∏ i, eLpNorm (F x i) (p i) Measure.count ^ 2
  have hTinner : ∀ k ∈ B, MeasurePreserving (T k) μ μ := by
    intro k hk
    exact hT k (by simpa only [B, B'] using box_subset_double n M hk)
  have hQmeas : AEMeasurable Q μ := by
    dsimp only [Q]
    simpa only [F, B'] using aemeasurable_truncOrbit_normProduct B' T hT f
      (fun i ↦ (hf i).aestronglyMeasurable) p hp0 hptop hpreal
  have hright : ∫⁻ x, Q x ∂μ ≤
      (B'.card : ℝ≥0∞) * ∏ i, eLpNorm (f i) (p i) μ ^ 2 := by
    dsimp only [Q]
    simpa only [F, B'] using holder_truncOrbit_norms B' T hT f
      (fun i ↦ (hf i).aestronglyMeasurable) p hp0 hptop hpreal hqsum
  have hpoint : ∀ x, ∑ j : Fin J, ∑ k ∈ B,
      ‖d j (T k x)‖ₑ ^ (2 : ℕ) ≤ A * Q x := by
    intro x
    calc
      ∑ j : Fin J, ∑ k ∈ B, ‖d j (T k x)‖ₑ ^ (2 : ℕ) =
          ∑ j : Fin J, ∑ k ∈ B,
            ‖aux_discreteAverage (N j.succ) (F x) k -
              aux_discreteAverage (N j.castSucc) (F x) k‖ₑ ^ (2 : ℕ) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k hk
        rw [hjump, haverage x k j.succ (by simpa only [B] using hk),
          haverage x k j.castSucc (by simpa only [B] using hk)]
      _ ≤ A * Q x := by
        simpa only [B, B', F, Q] using hlocal x
  have hbox := finite_box_ergodic_to_discrete B B' T hTinner d hd A
    (∏ i, eLpNorm (f i) (p i) μ ^ 2) (fun x ↦ A * Q x) Q hpoint
    (fun _ ↦ le_rfl) hQmeas hright
  have hcancel := cancel_box_ratio hM (by
    simpa only [B, B', mul_assoc] using hbox)
  simpa only [B] using hcancel
end Auto.aux_ErgodicBox
