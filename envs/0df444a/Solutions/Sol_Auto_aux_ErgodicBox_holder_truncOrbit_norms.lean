-- Prove2me | solution 1 for Auto.aux_ErgodicBox.holder_truncOrbit_norms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:13.264553+00:00
-- url     : https://prove2.me/submissions/8f321ef4-3f46-4138-8775-ab92dae4db21

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_ErgodicBox_aemeasurable_orbitPowerSum
public import Theorems.Thm_Auto_aux_ErgodicBox_lintegral_orbitPowerSum
public import Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_sq_eq_lintegral_rpow
public import Theorems.Thm_Auto_aux_ErgodicBox_prod_mul_rpow_eq_mul_prod_rpow
public import Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_truncOrbit_sq
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
    {X κ : Type*} [MeasurableSpace X] [MeasurableSpace κ]
    [Countable κ] [MeasurableSingletonClass κ] {μ : Measure X}
    {n : ℕ} (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    (f : Fin n → X → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (p : Fin n → ℝ≥0∞) (hp0 : ∀ i, p i ≠ 0) (hptop : ∀ i, p i ≠ ∞)
    (hpreal : ∀ i, 0 < (p i).toReal)
    (hqsum : ∑ i, 2 / (p i).toReal = 1) :
    ∫⁻ x, ∏ i, eLpNorm (truncOrbit B T (f i) x) (p i) Measure.count ^ 2 ∂μ ≤
      B.card * ∏ i, eLpNorm (f i) (p i) μ ^ 2 := by
  let q : Fin n → ℝ := fun i ↦ 2 / (p i).toReal
  have hqnonneg : ∀ i, 0 ≤ q i := by
    intro i
    dsimp [q]
    positivity
  have hholder0 :
      ∫⁻ x, ∏ i, orbitPowerSum B T (f i) (p i).toReal x ^ q i ∂μ ≤
        ∏ i, (∫⁻ x, orbitPowerSum B T (f i) (p i).toReal x ∂μ) ^ q i := by
    apply ENNReal.lintegral_prod_norm_pow_le Finset.univ
    · intro i _
      exact aemeasurable_orbitPowerSum B T hT (f i) (hf i) (p i).toReal
    · simpa only [q] using hqsum
    · intro i _
      exact hqnonneg i
  have hholder :
      ∫⁻ x, ∏ i, orbitPowerSum B T (f i) (p i).toReal x ^ q i ∂μ ≤
        ∏ i, (B.card * ∫⁻ x, ‖f i x‖ₑ ^ (p i).toReal ∂μ) ^ q i := by
    calc
      ∫⁻ x, ∏ i, orbitPowerSum B T (f i) (p i).toReal x ^ q i ∂μ ≤
          ∏ i, (∫⁻ x, orbitPowerSum B T (f i) (p i).toReal x ∂μ) ^ q i := hholder0
      _ = ∏ i, (B.card * ∫⁻ x, ‖f i x‖ₑ ^ (p i).toReal ∂μ) ^ q i := by
        apply Finset.prod_congr rfl
        intro i _
        rw [lintegral_orbitPowerSum B T hT (f i) (hf i) (p i).toReal]
  calc
    ∫⁻ x, ∏ i, eLpNorm (truncOrbit B T (f i) x) (p i) Measure.count ^ 2 ∂μ =
        ∫⁻ x, ∏ i, orbitPowerSum B T (f i) (p i).toReal x ^ q i ∂μ := by
      congr with x
      apply Finset.prod_congr rfl
      intro i hi
      exact eLpNorm_truncOrbit_sq B T (f i) x (p i) (hp0 i) (hptop i) (hpreal i)
    _ ≤ ∏ i, (B.card * ∫⁻ x, ‖f i x‖ₑ ^ (p i).toReal ∂μ) ^ q i := hholder
    _ = B.card * ∏ i, eLpNorm (f i) (p i) μ ^ 2 := by
      rw [prod_mul_rpow_eq_mul_prod_rpow Finset.univ B.card
        (fun i ↦ ∫⁻ x, ‖f i x‖ₑ ^ (p i).toReal ∂μ) q
        (fun i _ ↦ hqnonneg i) (by simpa only [q] using hqsum)]
      apply congrArg (fun z : ℝ≥0∞ ↦ (B.card : ℝ≥0∞) * z)
      apply Finset.prod_congr rfl
      intro i hi
      symm
      exact eLpNorm_sq_eq_lintegral_rpow μ (f i) (p i) (hp0 i) (hptop i)
end Auto.aux_ErgodicBox
