-- Prove2me | solution 1 for Auto.aux_CuboidNorm.finite_jump_energy_lower_on_of_overlap_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:45.108878+00:00
-- url     : https://prove2.me/submissions/8240ac7d-1384-4baa-a40e-77acb373a366

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_overlapWidth_lower_bound
public import Theorems.Thm_Auto_aux_twistedAverageAtScale_cuboidLift_eq
public import Theorems.Thm_Auto_aux_CuboidNorm_endpointJump_cube_dom_of_overlap_formula
public import Theorems.Thm_Auto_aux_CuboidNorm_finite_jump_energy_lower_of_cube_dom
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
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n J : ℕ}
    (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1) (hεδ : ε ≤ δ)
    (hwidth : ε + δ < 1) (N : Fin (J + 1) → ℕ)
    (hNpos : ∀ q, 0 < N q) (a : Fin n → ZVector n → ℝ)
    (A : Finset (ZVector n)) :
    (ENNReal.ofReal (δ - ε) ^ (2 : ℝ) * ENNReal.ofReal ε ^ n) *
        ∑ j : Fin J, ∑ k ∈ A,
          ‖aux_integerDiscreteAverage (N j.succ) a k -
            aux_integerDiscreteAverage (N j.castSucc) a k‖ₑ ^ (2 : ℝ) ≤
      ∑ j : Fin J, eLpNorm
        (fun x ↦ ctTwistedAverageAtScale (N j.succ : ℝ) ctUnitIntervalKernel
            (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
            (WithLp.toLp 2 x) -
          ctTwistedAverageAtScale (N j.castSucc : ℝ) ctUnitIntervalKernel
            (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
            (WithLp.toLp 2 x)) 2 volume ^ 2 := by
  let d : Fin J → ZVector n → ℝ := fun j k ↦
    if k ∈ A then
      aux_integerDiscreteAverage (N j.succ) a k -
        aux_integerDiscreteAverage (N j.castSucc) a k
    else 0
  let G : Fin J → RVector n → ℝ := fun j x ↦
    ctTwistedAverageAtScale (N j.succ : ℝ) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
        (WithLp.toLp 2 x) -
      ctTwistedAverageAtScale (N j.castSucc : ℝ) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
        (WithLp.toLp 2 x)
  have hlower := finite_jump_energy_lower_of_cube_dom (n := n) (J := J)
    (ε := ε) (c := δ - ε) hε.le (sub_nonneg.mpr hεδ) A d G
    (by
      intro j k hk
      simp [d, hk])
    (by
      intro j k hk x hx
      dsimp [d, G]
      simp only [if_pos hk]
      apply endpointJump_cube_dom_of_overlap_formula hεδ N
        (fun M x ↦ ctTwistedAverageAtScale (M : ℝ) ctUnitIntervalKernel
          (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
          (WithLp.toLp 2 x))
        (fun M k ↦ aux_integerDiscreteAverage M a k)
        (aux_overlapWidth hn ε δ)
      · intro u hu
        exact aux_overlapWidth_lower_bound hn u hu
      · intro M k u hu hM
        exact aux_twistedAverageAtScale_cuboidLift_eq hn hε hεδ hwidth M hM
          a k u hu
      · exact hNpos
      · exact hx
      )
  have hsum : ∑ j : Fin J, ∑ k ∈ A, ‖d j k‖ₑ ^ (2 : ℝ) =
      ∑ j : Fin J, ∑ k ∈ A,
        ‖aux_integerDiscreteAverage (N j.succ) a k -
          aux_integerDiscreteAverage (N j.castSucc) a k‖ₑ ^ (2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    simp [d, hk]
  rw [hsum] at hlower
  simpa [G] using hlower
end Auto.aux_CuboidNorm
