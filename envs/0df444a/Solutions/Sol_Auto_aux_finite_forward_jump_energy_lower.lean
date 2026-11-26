-- Prove2me | solution 1 for Auto.aux_finite_forward_jump_energy_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:42.833011+00:00
-- url     : https://prove2.me/submissions/21c9c538-8bd6-4e98-82c7-2de6eec68d86

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_integerDiscreteAverage_natToInt
public import Theorems.Thm_Auto_aux_CuboidNorm_finite_jump_energy_lower_on_of_overlap_formula
public import Theorems.Thm_Auto_aux_CuboidNorm_raw_cuboid_jumpEnergy_eq_endpointEnergy
public import Theorems.Thm_Auto_aux_CuboidNorm_natToInt_support_map
public import Theorems.Thm_Auto_aux_discreteAverage_truncate_eq_of_mem
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
theorem _root_.solution {n J : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1) (hεδ : ε ≤ δ)
    (hwidth : ε + δ < 1) (N : Fin (J + 1) → ℕ)
    (hN : StrictMono N) (hNpos : ∀ q, 0 < N q)
    (F : Fin n → (Fin n → ℕ) → ℝ) (A : Finset (Fin n → ℕ)) :
    (ENNReal.ofReal (δ - ε) ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ j : Fin J, ∑ k ∈ A,
          ‖aux_discreteAverage (N j.succ) F k -
            aux_discreteAverage (N j.castSucc) F k‖ₑ ^ (2 : ℝ) ≤
      ctEndpointEnergy J (fun q ↦ (N q : ℝ)) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i
          (aux_natToInt (aux_truncate
            (aux_localInputSupport A (N (Fin.last J))) (F i))))) := by
  let L : ℕ := N (Fin.last J)
  let B : Finset (Fin n → ℕ) := aux_localInputSupport A L
  let F' : Fin n → (Fin n → ℕ) → ℝ := fun i ↦ aux_truncate B (F i)
  let a : Fin n → aux_ZVector n → ℝ := fun i ↦ aux_natToInt (F' i)
  have hscale : ∀ q : Fin (J + 1), N q ≤ L := by
    intro q
    exact hN.monotone (Fin.le_last q)
  have hsupport : ∀ i z, z ∉ B.map aux_CuboidNorm.natToIntEmbedding → a i z = 0 := by
    intro i z hz
    exact aux_CuboidNorm.natToInt_support_map B (F' i) (by
      intro k hk
      simp [F', aux_truncate, hk]) z hz
  have havg : ∀ (q : Fin (J + 1)) (k : Fin n → ℕ), k ∈ A →
      aux_integerDiscreteAverage (N q) a (aux_CuboidNorm.natToIntEmbedding k) =
        aux_discreteAverage (N q) F k := by
    intro q k hk
    calc
      aux_integerDiscreteAverage (N q) a (aux_CuboidNorm.natToIntEmbedding k) =
          aux_discreteAverage (N q) F' k := by
        exact aux_integerDiscreteAverage_natToInt (N q) F' k
      _ = aux_discreteAverage (N q) F k := by
        exact aux_discreteAverage_truncate_eq_of_mem (hscale q) F hk
  have hlower := aux_CuboidNorm.finite_jump_energy_lower_on_of_overlap_formula
    hn hε hεδ hwidth N hNpos a (A.map aux_CuboidNorm.natToIntEmbedding)
  have hsum :
      ∑ j : Fin J, ∑ z ∈ A.map aux_CuboidNorm.natToIntEmbedding,
          ‖aux_integerDiscreteAverage (N j.succ) a z -
            aux_integerDiscreteAverage (N j.castSucc) a z‖ₑ ^ (2 : ℝ) =
        ∑ j : Fin J, ∑ k ∈ A,
          ‖aux_discreteAverage (N j.succ) F k -
            aux_discreteAverage (N j.castSucc) F k‖ₑ ^ (2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro k hk
    rw [havg j.succ k hk, havg j.castSucc k hk]
  rw [hsum, aux_CuboidNorm.raw_cuboid_jumpEnergy_eq_endpointEnergy] at hlower
  simpa only [L, B, F', a] using hlower
end Auto
