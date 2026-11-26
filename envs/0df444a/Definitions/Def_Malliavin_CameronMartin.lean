-- Prove2me | Definitions.Def_Malliavin_CameronMartin
-- name    : Malliavin_CameronMartin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:41:51.934946+00:00
-- url     : https://prove2.me/theorems/214875a8-9402-4d93-9f80-e766b4932949
-- title:
--   Cameron Martin
-- statement:
--   Definitions and structural lemmas for Cameron Martin, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CameronMartin.lean

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Tactic.Recall
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real Topology
universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_7
namespace Malliavin
section Translations
variable {W : Type*} [NormedAddCommGroup W] [MeasurableSpace W]
def translate (h : W) : W → W := fun x ↦ x + h
noncomputable def translatedMeasure (μ : Measure W) (h : W) : Measure W :=
  μ.map (translate h)
@[fun_prop]
theorem measurable_translate [BorelSpace W] (h : W) : Measurable (translate h) := by
  unfold translate
  fun_prop
@[simp]
theorem translatedMeasure_zero (μ : Measure W) : translatedMeasure μ 0 = μ := by
  have h_zero : translate (0 : W) = id := by
    funext x
    simp only [translate, add_zero, id_eq]
  simp only [translatedMeasure, h_zero, Measure.map_id]
def IsAdmissibleShift (μ : Measure W) (h : W) : Prop :=
  translatedMeasure μ h ≪ μ
def IsQuasiInvariantShift (μ : Measure W) (h : W) : Prop :=
  translatedMeasure μ h ≪ μ ∧ μ ≪ translatedMeasure μ h
end Translations
namespace CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
noncomputable def mean : W := ∫ x, x ∂μ
noncomputable def centeredId : W → W := id - fun _ ↦ mean μ
theorem memLp_centeredId : MemLp (centeredId μ) 2 μ := by
  have h_id : MemLp id 2 μ := IsGaussian.memLp_id μ 2 (by norm_num)
  have h_const : MemLp (fun _ : W ↦ mean μ) 2 μ := memLp_const (mean μ)
  exact h_id.sub h_const
noncomputable def centeredIdLp : Lp W 2 μ :=
  (memLp_centeredId μ).toLp (centeredId μ)
noncomputable def centeredDualToLp : StrongDual ℝ W →L[ℝ] Lp ℝ 2 μ :=
  StrongDual.toLp μ 2 -
    (Lp.constL 2 μ ℝ).comp (ContinuousLinearMap.apply ℝ ℝ (mean μ))
noncomputable def firstChaos : Submodule ℝ (Lp ℝ 2 μ) :=
  (centeredDualToLp μ).range.topologicalClosure
noncomputable abbrev Space := firstChaos μ
noncomputable def ofDual : StrongDual ℝ W →L[ℝ] Space μ :=
  (centeredDualToLp μ).codRestrict (firstChaos μ) fun L ↦
    Submodule.le_topologicalClosure _ ⟨L, rfl⟩
omit [CompleteSpace W] [SecondCountableTopology W] in
@[simp]
theorem coe_ofDual (L : StrongDual ℝ W) :
    ((ofDual μ L : Space μ) : Lp ℝ 2 μ) = centeredDualToLp μ L :=
  rfl
theorem integrable_smul_centeredId (f : Lp ℝ 2 μ) :
    Integrable (fun x ↦ f x • centeredId μ x) μ := by
  change Integrable (((fun x ↦ f x) • centeredId μ)) μ
  have h_one :
      MemLp ((fun x ↦ f x) • centeredId μ) 1 μ :=
    (memLp_centeredId μ).smul (Lp.memLp f)
  have h_integrable : Integrable (((fun x ↦ f x) • centeredId μ)) μ :=
    memLp_one_iff_integrable.mp h_one
  exact h_integrable
noncomputable def covarianceLinearMap : Lp ℝ 2 μ →ₗ[ℝ] W where
  toFun f := ∫ x, f x • centeredId μ x ∂μ
  map_add' f g := by
    rw [← integral_add (integrable_smul_centeredId μ f)
      (integrable_smul_centeredId μ g)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [Pi.add_apply] at hx ⊢
    rw [hx, add_smul]
  map_smul' c f := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply] at hx ⊢
    calc
      (c • f) x • centeredId μ x = (c * f x) • centeredId μ x := by
        simpa only [smul_eq_mul] using congrArg (fun a : ℝ ↦ a • centeredId μ x) hx
      _ = c • (f x • centeredId μ x) := by rw [smul_smul]
noncomputable def covarianceMap : Lp ℝ 2 μ →L[ℝ] W :=
  ((ContinuousLinearMap.lsmul ℝ ℝ (E := W)).lpPairing μ 2 2).flip (centeredIdLp μ)
noncomputable def inclusion : Space μ →L[ℝ] W :=
  (covarianceMap μ).domRestrict (firstChaos μ)
noncomputable def subspace : Submodule ℝ W :=
  (inclusion μ).range
noncomputable def translated (h : Space μ) : Measure W :=
  translatedMeasure μ (inclusion μ h)
noncomputable def logDensity (h : Space μ) : W → ℝ :=
  llr (translated μ h) μ
end CameronMartin
end Malliavin


