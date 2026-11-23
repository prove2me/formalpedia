-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsCompactDualHaar_372789bc53a272b8
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsCompactDualHaar_372789bc53a272b8
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:09.866267+00:00
-- url     : https://prove2.me/theorems/daf886c0-a029-43c4-a850-ae383308d920
-- title:
--   Is Compact Dual Haar
-- statement:
--   Definitions and structural lemmas for Is Compact Dual Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsCompactDualHaar.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SUVol
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
variable {ι : Type} {r : ℕ}
def suGrp (H : ι → Matrix (Fin r) (Fin r) ℂ) : Subgroup (ι → GL (Fin r) ℂ) where
  carrier := {g | ∀ i, (g i : Matrix (Fin r) (Fin r) ℂ)ᵀ * H i * (g i : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = H i ∧
    (g i : Matrix (Fin r) (Fin r) ℂ).det = 1}
  one_mem' := fun i => by simp
  mul_mem' := by
    intro g h hg hh i
    obtain ⟨g1, g2⟩ := hg i
    obtain ⟨h1, h2⟩ := hh i
    refine ⟨?_, by simp [g2, h2]⟩
    rw [Pi.mul_apply, Units.val_mul, transpose_mul, Matrix.map_mul]
    calc _ = (h i : Matrix (Fin r) (Fin r) ℂ)ᵀ * ((g i : Matrix (Fin r) (Fin r) ℂ)ᵀ * H i *
        (g i : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ)) * (h i : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = H i := by rw [g1, h1]
  inv_mem' := by
    intro g hg i
    obtain ⟨g1, g2⟩ := hg i
    have e : (g i : Matrix (Fin r) (Fin r) ℂ) * ((g⁻¹ i : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = 1 := by
      rw [Pi.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← g1]
      calc _ = ((g i : Matrix (Fin r) (Fin r) ℂ) * ((g⁻¹ i : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))ᵀ * H i *
          ((g i : Matrix (Fin r) (Fin r) ℂ) * ((g⁻¹ i : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)).map (starRingEnd ℂ) := by
            simp only [transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
        _ = H i := by rw [e]; simp
    · have := congrArg Matrix.det e
      rwa [det_mul, g2, one_mul, det_one] at this
def suLie (H : ι → Matrix (Fin r) (Fin r) ℂ) : Submodule ℝ (ι → Matrix (Fin r) (Fin r) ℂ) where
  carrier := {X | ∀ i, (X i)ᵀ * H i + H i * (X i).map (starRingEnd ℂ) = 0 ∧ (X i).trace = 0}
  zero_mem' := fun i => by simp
  add_mem' := by
    intro X Y hX hY i
    refine ⟨?_, by simp [(hX i).2, (hY i).2]⟩
    rw [Pi.add_apply, transpose_add, Matrix.map_add _ (map_add _), Matrix.add_mul, Matrix.mul_add,
      add_add_add_comm, (hX i).1, (hY i).1, add_zero]
  smul_mem' := by
    intro c X hX i
    refine ⟨?_, by simp [(hX i).2]⟩
    have e : (c • X i).map (starRingEnd ℂ) = c • (X i).map (starRingEnd ℂ) := by
      ext a b; simp
    rw [Pi.smul_apply, transpose_smul, e, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hX i).1, smul_zero]
def trForm [Fintype ι] (X Y : ι → Matrix (Fin r) (Fin r) ℂ) : ℝ := ∑ i, (X i * Y i).trace.re
def expCube {H : ι → Matrix (Fin r) (Fin r) ℂ} {n : ℕ} (b : Module.Basis (Fin n) ℝ (suLie H)) (ε : ℝ) :
    Set (suGrp H) :=
  {g | ∃ t ∈ Metric.ball (0 : Fin n → ℝ) ε, ∀ i, ((g.1 i : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
    NormedSpace.exp ((b.equivFun.symm t).1 i)}
def TraceDensity [Fintype ι] (H : ι → Matrix (Fin r) (Fin r) ℂ) [MeasurableSpace (suGrp H)]
    (m : Measure (suGrp H)) (c : ℝ≥0∞) : Prop :=
  ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ (suLie H)),
    Tendsto (fun ε : ℝ => m (expCube b ε) / volume (Metric.ball (0 : Fin n → ℝ) ε)) (𝓝[>] 0)
      (𝓝 (c * ENNReal.ofReal √|(Matrix.of fun k l => trForm (b k).1 (b l).1).det|))
abbrev suCpt (ι : Type) (r : ℕ) : Subgroup (ι → GL (Fin r) ℂ) := suGrp fun _ : ι => (1 : Matrix (Fin r) (Fin r) ℂ)
def IsCompactDualHaar [Fintype ι] (H : ι → Matrix (Fin r) (Fin r) ℂ) [MeasurableSpace (suGrp H)]
    (m : Measure (suGrp H)) : Prop :=
  m.IsHaarMeasure ∧
    ∃ (_ : MeasurableSpace (suCpt ι r)) (_ : BorelSpace (suCpt ι r)) (m₀ : Measure (suCpt ι r)) (c : ℝ≥0∞),
      m₀.IsHaarMeasure ∧ IsProbabilityMeasure m₀ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧ TraceDensity H m c ∧ TraceDensity _ m₀ c
end GlobalTheory.SUVol


