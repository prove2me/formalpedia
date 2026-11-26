-- Prove2me | Definitions.Def_Malliavin_ClarkOconeExamples
-- name    : Malliavin_ClarkOconeExamples
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:35:09.027954+00:00
-- url     : https://prove2.me/theorems/8f53bb01-7f8f-4690-b49a-6e99dfc727a0
-- title:
--   Clark Ocone Examples
-- statement:
--   Definitions and structural lemmas for Clark Ocone Examples, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/ClarkOconeExamples.lean

import Definitions.Def_Malliavin_ClarkOcone
import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_CylindricalGrowth
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_coe_space_mem_domD12
import Theorems.Thm_Malliavin_comp_brownian_mem_domD12
import Theorems.Thm_Malliavin_cylinder_growth_brownian_mem_domD12
import Theorems.Thm_Malliavin_wienerIntegral_mem_space

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace
namespace Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
noncomputable def wienerIntegralD12 (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (g : Lp ℝ 2 nonnegativeLebesgueMeasure) : D12 P :=
  ⟨wienerIntegral hB g, (coe_space_mem_domD12 P ⟨_, wienerIntegral_mem_space hB L hL hgen g⟩).1⟩
noncomputable def compBrownianD12 (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ C * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0) : D12 P :=
  ⟨(memLp_comp_brownian L hL hg hC hc hgb T).toLp _,
    comp_brownian_mem_domD12 L hL hg hC hc hgb hgb' T⟩
theorem memLp_deriv_comp_brownian (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hgb' : ∀ x, |deriv g x| ≤ C * Real.exp (c * |x|)) (T : ℝ≥0) :
    MemLp (fun w ↦ deriv g (B T w)) 2 P := by
  have h : (fun w ↦ deriv g (B T w)) = fun w ↦ deriv g (L T w) := by
    funext w
    rw [hL]
  rw [h]
  have hc' : Continuous fun w ↦ deriv g (L T w) :=
    hg.continuous_deriv_one.comp (L T).continuous
  refine memLp_of_le_of_integrable_sq P hc'.aestronglyMeasurable
    (integrable_expGrowth_sq P C c ‖L T‖) fun w ↦ ?_
  rw [Real.norm_eq_abs]
  refine (hgb' _).trans ?_
  gcongr
  exact (Real.norm_eq_abs _).symm.le.trans ((L T).le_opNorm w)
noncomputable def cylinderGrowthD12 (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
    {n k : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ y, |f y| ≤ C * (1 + ‖y‖) ^ k) (hfg' : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ k)
    (t : Fin n → ℝ≥0) : D12 P :=
  ⟨(memLp_cylinder_growth_brownian L hL hf hC hfg t).toLp _,
    (cylinder_growth_brownian_mem_domD12 L hL hf hC hfg hfg' t).1⟩
noncomputable def compWienerIntegralD12 (hB : IsPreBrownianReal B P) (L : ℝ≥0 → StrongDual ℝ W)
    (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B) {φ : ℝ → ℝ} {K : ℝ≥0}
    (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    D12 P :=
  ⟨(memLp_comp_of_deriv_le P hφ hK (wienerIntegral hB g)).toLp _,
    (comp_mem_domD12 P hφ hK (wienerIntegralD12 hB L hL hgen g).2).1⟩
noncomputable def compPiWienerIntegralD12 (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K)
    (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) : D12 P :=
  ⟨(memLp_comp_pi P hf hK fun i ↦ wienerIntegral hB (g i)).toLp _,
    (comp_pi_mem_domD12 P hf hK fun i ↦ (wienerIntegralD12 hB L hL hgen (g i)).2).1⟩
end Malliavin


