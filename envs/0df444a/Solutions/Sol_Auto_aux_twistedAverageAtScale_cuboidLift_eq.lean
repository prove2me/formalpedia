-- Prove2me | solution 1 for Auto.aux_twistedAverageAtScale_cuboidLift_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:51:50.955798+00:00
-- url     : https://prove2.me/submissions/b14fe874-8264-4f0b-847b-6b97306e411e

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_scaled_unitIntervalKernel
public import Theorems.Thm_Auto_aux_integral_scaled_Ico_eq_of_pointwise
public import Theorems.Thm_Auto_aux_cuboidEmbed_integrand_toLp
public import Theorems.Thm_Auto_aux_setIntegral_sum_overlapContribution
public import Theorems.Thm_Auto_aux_cuboidEmbed_product_eq_overlapSum
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
    (hn : 0 < n) {ε δ : ℝ} (hε : ε < 1) (hεδ : ε ≤ δ)
    (hwidth : ε + δ < 1) (N : ℕ) (hN : 0 < N)
    (a : Fin n → aux_ZVector n → ℝ) (k : aux_ZVector n)
    (u : aux_RVector n) (hu : ∀ i, 0 ≤ u i ∧ u i < ε) :
    ctTwistedAverageAtScale (N : ℝ) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
        (WithLp.toLp 2 (fun j ↦ (k j : ℝ) + u j)) =
      aux_overlapWidth hn ε δ u * aux_integerDiscreteAverage N a k := by
  let P : ℝ → ℝ := fun s ↦
    ∏ i, aux_liftRaw (aux_cuboidEmbed ε δ i (a i))
      (WithLp.toLp 2 (fun j ↦ (k j : ℝ) + u j) + s • ctCoordinateAxis i)
  let Q : ℝ → ℝ := fun s ↦ ∑ q : Fin N,
    aux_overlapContribution ε δ a k u q.val s
  unfold ctTwistedAverageAtScale
  unfold aux_ct_twistedAverageAtScale aux_ct_twistedAverage
  change ∫ s : ℝ, (N : ℝ)⁻¹ * ctUnitIntervalKernel ((N : ℝ)⁻¹ * s) * P s = _
  calc
    ∫ s : ℝ, (N : ℝ)⁻¹ * ctUnitIntervalKernel ((N : ℝ)⁻¹ * s) * P s =
        ∫ s : ℝ, ((N : ℝ)⁻¹ * (Ico (0 : ℝ) N).indicator
          (fun _ ↦ (1 : ℝ)) s) * P s := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with s
      rw [aux_scaled_unitIntervalKernel hN s]
    _ = (N : ℝ)⁻¹ * ∫ s in Ico (0 : ℝ) N, Q s :=
      aux_integral_scaled_Ico_eq_of_pointwise P Q (by
        intro s hs
        dsimp [P, Q]
        rw [aux_cuboidEmbed_integrand_toLp]
        exact aux_cuboidEmbed_product_eq_overlapSum hn hε hwidth a k u hu N hs)
    _ = (N : ℝ)⁻¹ *
        (aux_overlapWidth hn ε δ u * ∑ q : Fin N,
          ∏ i, a i (aux_translateAxisInt k i (q.val : ℤ))) := by
      rw [aux_setIntegral_sum_overlapContribution hn hεδ hwidth a k u N hu]
    _ = aux_overlapWidth hn ε δ u * aux_integerDiscreteAverage N a k := by
      unfold aux_integerDiscreteAverage
      rw [Fin.sum_univ_eq_sum_range
        (fun m ↦ ∏ i, a i (aux_translateAxisInt k i (m : ℤ))) N]
      ring
end Auto
