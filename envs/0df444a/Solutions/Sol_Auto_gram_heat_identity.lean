-- Prove2me | solution 1 for Auto.gram_heat_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:02.741008+00:00
-- url     : https://prove2.me/submissions/4b7fa97e-febf-4dba-8ea5-ba7a007c8faf

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_matCostBil_self
public import Theorems.Thm_Auto_posDef_add_smul_one
public import Theorems.Thm_Auto_hasDerivAt_energyReg
public import Theorems.Thm_Auto_hasDerivAt_energy_hessian
public import Theorems.Thm_Auto_wGram_posSemidef
public import Theorems.Thm_Auto_wGram_isHermitian
public import Theorems.Thm_Auto_hasDerivAt_wGram
public import Theorems.Thm_Auto_gweight_nonneg
public import Theorems.Thm_Auto_hasDerivAt_gweight_p
public import Theorems.Thm_Auto_hasDerivAt_gweightD1_p
public import Theorems.Thm_P2M_Auto_hasDerivAt_gweight___b6d5e5597986

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
namespace Auto
theorem _root_.solution (C : Matrix κ κ ℂ) (hC : C.PosSemidef) (B : Matrix ι κ ℂ) (u : ι → ℝ)
    {h η σ : ℝ} (hh : 0 ≤ h) (hη : 0 < η) (hσ : 0 < σ) (p : ℝ) :
    HasDerivAt (fun q => energyReg η (C + wGram B (gweight u h σ q))) ((3 / 2) * ((CFC.sqrt (C +
      wGram B (gweight u h σ p) + (η : ℂ) • 1) * wGram B (fun i => -(h * gaussianD 1 σ (u i -
      p)))).trace).re) p ∧ HasDerivAt (fun q => (3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ
      q) + (η : ℂ) • 1) * wGram B (fun i => -(h * gaussianD 1 σ (u i - q)))).trace).re) ((matCost
      (C + wGram B (gweight u h σ p) + (η : ℂ) • 1) (wGram B (fun i => -(h * gaussianD 1 σ (u i -
      p))))).toReal + (3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ p) + (η : ℂ) • 1) * wGram B
      (fun i => h * gaussianD 2 σ (u i - p))).trace).re) p ∧ HasDerivAt (fun τ => energyReg η (C +
      wGram B (gweight u h τ p))) ((3 / 2) * ((CFC.sqrt (C + wGram B (gweight u h σ p) + (η : ℂ) •
      1) * wGram B (fun i => h * gaussianD 2 σ (u i - p) / 2)).trace).re) σ := by
  have hPSD : ∀ q τ, 0 < τ → (C + wGram B (gweight u h τ q)).PosSemidef := fun q τ hτ =>
    hC.add (wGram_posSemidef B fun i => gweight_nonneg u hh hτ q i)
  have hdp : ∀ i j, HasDerivAt (fun q => (C + wGram B (gweight u h σ q)) i j) (wGram B (fun i => -(h
      * gaussianD 1 σ (u i - p))) i j) p := by
    intro i j
    have := (hasDerivAt_wGram B (f := fun q => gweight u h σ q) (fun k => hasDerivAt_gweight_p u h σ
        p k) i j).const_add (C i j)
    simpa using this
  have hdU : ∀ i j, HasDerivAt (fun q => wGram B (fun i => -(h * gaussianD 1 σ (u i - q))) i j)
      (wGram B (fun i => h * gaussianD 2 σ (u i - p)) i j) p :=
    hasDerivAt_wGram B (f := fun q i => -(h * gaussianD 1 σ (u i - q))) (fun k =>
        hasDerivAt_gweightD1_p u h σ p k)
  refine ⟨?_, ?_, ?_⟩
  · exact hasDerivAt_energyReg hη (fun q => hPSD q σ hσ) hdp
  · have hH := hasDerivAt_energy_hessian hη (fun q => hPSD q σ hσ) hdp hdU (wGram_isHermitian B _)
    rwa [matCostBil_self (posDef_add_smul_one (hPSD p σ hσ) hη)] at hH
  ·
    have hdσ : ∀ i j, HasDerivAt (fun τ => (C + wGram B (gweight u h (max τ (σ / 2)) p)) i j) (wGram
        B (fun i => h * gaussianD 2 σ (u i - p) / 2) i j) σ := by
      intro i j
      have hmax : HasDerivAt (fun τ => max τ (σ / 2)) 1 σ := by
        refine (hasDerivAt_id σ).congr_of_eventuallyEq ?_
        filter_upwards [lt_mem_nhds (by linarith : σ / 2 < σ)] with τ hτ
        simp [max_eq_left hτ.le]
      have hw : ∀ k, HasDerivAt (fun τ => gweight u h (max τ (σ / 2)) p k) (h * gaussianD 2 σ (u k -
          p) / 2) σ := by
        intro k
        have := (hasDerivAt_gweight_σ u h p (σ := max σ (σ / 2)) (by positivity) k).comp σ hmax
        simp only [max_eq_left (by linarith : σ / 2 ≤ σ), mul_one] at this
        exact this
      have := (hasDerivAt_wGram B (f := fun τ => gweight u h (max τ (σ / 2)) p) hw i j).const_add (C
          i j)
      simpa using this
    have hE := hasDerivAt_energyReg hη (fun τ => hPSD p (max τ (σ / 2)) (by positivity)) hdσ
    simp only [max_eq_left (by linarith : σ / 2 ≤ σ)] at hE
    refine hE.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (by linarith : σ / 2 < σ)] with τ hτ
    simp [max_eq_left hτ.le]
end Auto
