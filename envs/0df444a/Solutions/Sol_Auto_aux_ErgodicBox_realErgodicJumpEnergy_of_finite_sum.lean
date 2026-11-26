-- Prove2me | solution 1 for Auto.aux_ErgodicBox.realErgodicJumpEnergy_of_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:06.629934+00:00
-- url     : https://prove2.me/submissions/eee47b1d-6171-433e-9eeb-807087a19a2e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_orbit_measurePreserving
public import Theorems.Thm_Auto_aux_discreteAverage_orbitFunction
public import Theorems.Thm_Auto_aux_ErgodicBox_holder_exponents_of_inverse_sum
public import Theorems.Thm_Auto_aux_ErgodicBox_scale_le_last
public import Theorems.Thm_Auto_aux_ErgodicBox_finite_box_bound_of_finite_sum_cancelled
public import Theorems.Thm_Auto_aux_ErgodicBox_discreteAverage_truncated_orbit_eq
public import Theorems.Thm_Auto_aux_ErgodicBox_realErgodicAverage_sub_aestronglyMeasurable
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
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {n J : ℕ}
    (p : Fin n → ℝ≥0∞)
    (hp : ∀ i, 1 < p i ∧ p i < ∞)
    (hsum : (∑ i, ((p i)⁻¹).toReal) = 1 / 2)
    (S : ErgodicSystem X μ n) (N : Fin (J + 1) → ℕ)
    (hN : StrictMono N) (hNpos : ∀ j, 0 < N j)
    (f : Fin n → X → ℝ) (hf : ∀ i, MemLp (f i) (p i) μ)
    (A : ℝ≥0∞)
    (hlocal : ∀ x, ∑ j : Fin J,
      ∑ k ∈ box n (N (Fin.last J)),
        ‖aux_discreteAverage (N j.succ)
            (fun i ↦ truncOrbit
              (box n (N (Fin.last J) + N (Fin.last J)))
              (aux_orbit S.transformation) (f i) x) k -
          aux_discreteAverage (N j.castSucc)
            (fun i ↦ truncOrbit
              (box n (N (Fin.last J) + N (Fin.last J)))
              (aux_orbit S.transformation) (f i) x) k‖ₑ ^ (2 : ℝ) ≤
        A * ∏ i, eLpNorm
          (truncOrbit
            (box n (N (Fin.last J) + N (Fin.last J)))
            (aux_orbit S.transformation) (f i) x)
          (p i) Measure.count ^ 2) :
    realErgodicJumpEnergy S N f ≤
      A * ((2 ^ n : ℕ) : ℝ≥0∞) * ∏ i, eLpNorm (f i) (p i) μ ^ 2 := by
  rcases holder_exponents_of_inverse_sum p hp hsum with
    ⟨hp0, hptop, hpreal, hqsum⟩
  let M : ℕ := N (Fin.last J)
  have hM : 0 < M := by
    dsimp [M]
    exact hNpos (Fin.last J)
  let a : Fin (J + 1) → X → ℝ := fun q ↦ realErgodicAverage S (N q) f
  let d : Fin J → X → ℝ := fun j x ↦ a j.succ x - a j.castSucc x
  have hd : ∀ j, AEStronglyMeasurable (d j) μ := by
    intro j
    dsimp [d, a]
    exact realErgodicAverage_sub_aestronglyMeasurable S
      (N j.succ) (N j.castSucc) f (fun i ↦ (hf i).aestronglyMeasurable)
  have hjump : ∀ j x, d j x = a j.succ x - a j.castSucc x := by
    intro j x
    rfl
  have haverage : ∀ (x : X) (k : Fin n → ℕ) (q : Fin (J + 1)),
      k ∈ box n M →
      aux_discreteAverage (N q)
          (fun i ↦ truncOrbit
            (box n (M + M)) (aux_orbit S.transformation) (f i) x) k =
        a q (aux_orbit S.transformation k x) := by
    intro x k q hk
    calc
      aux_discreteAverage (N q)
          (fun i ↦ truncOrbit
            (box n (M + M)) (aux_orbit S.transformation) (f i) x) k =
          aux_discreteAverage (N q) (aux_orbitFunction S f x) k :=
        discreteAverage_truncated_orbit_eq S f x k hk (scale_le_last N hN q)
      _ = realErgodicAverage S (N q) f (aux_orbit S.transformation k x) :=
        aux_discreteAverage_orbitFunction S f x k (N q)
      _ = a q (aux_orbit S.transformation k x) := rfl
  have hbox := finite_box_bound_of_finite_sum_cancelled
    hM (aux_orbit S.transformation)
    (fun k _ ↦ aux_orbit_measurePreserving
      S.transformation k S.measurePreserving)
    p N f hf hp0 hptop hpreal hqsum a d hd hjump A (by
      intro x
      simpa only [M, ENNReal.rpow_two] using hlocal x) haverage
  unfold realErgodicJumpEnergy
  change ∑ j, eLpNorm (d j) 2 μ ^ 2 ≤
    A * ((2 ^ n : ℕ) : ℝ≥0∞) * ∏ i, eLpNorm (f i) (p i) μ ^ 2
  exact hbox
end Auto.aux_ErgodicBox
