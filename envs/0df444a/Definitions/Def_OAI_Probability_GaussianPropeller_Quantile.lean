-- Prove2me | Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
-- name    : OAI_Probability_GaussianPropeller_Quantile
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T05:12:07.211992+00:00
-- url     : https://prove2.me/theorems/df705a07-0031-4ca5-9640-04b0014d47f3
-- title:
--   The normal density, distribution function and quantile
-- statement:
--   These notions belong to a formal proof of the Gaussian propeller conjecture of Khot and Naor. Let $\gamma_d$ be the standard Gaussian measure on $\mathbb R^d$. For a partition of $\mathbb R^d$ into measurable sets $A_1,\dots,A_k$, the Gaussian centroid of $A_i$ is $z_i=\int_{A_i}x\,d\gamma_d(x)$. The theorem states that $\sum_i|z_i|^2\le 9/(8\pi)$ for all $d$ and $k$, with equality for the propeller: three $120^\circ$ sectors in a plane, extended by $\mathbb R^{d-2}$. The proof takes an optimal partition with the fewest cells of positive mass. Its cells are the polyhedral cones on which $\langle z_i,x\rangle$ is largest. Configurations with four or more such cells are ruled out by Gaussian integral estimates and explicit numerical certificates.
--
--   1. **Density and distribution function.** $\varphi(x)=\frac1{\sqrt{2\pi}}e^{-x^2/2}$ and $\Phi(x)=\int_{-\infty}^x\varphi$, a strictly increasing bijection of $\mathbb R$ onto $(0,1)$.
--   2. **Quantile.** The inverse $q=\Phi^{-1}$ on $(0,1)$, extended by $0$ outside.
--   3. **Isoperimetric profile.** The Gaussian isoperimetric function
--   $$
--   I(p)=\varphi\bigl(\Phi^{-1}(p)\bigr),\qquad p\in(0,1).
--   $$
--   These are the scalar functions in Ehrhard-type concavity statements for Gaussian measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Quantile.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianPropeller/Quantile.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GaussianPropeller mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution

namespace OAI

universe uX

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace GaussianPropeller.Quantile

noncomputable def φ (x : ℝ) : ℝ := (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-x^2/2)
noncomputable def Φ (x : ℝ) : ℝ := ∫ y in Iic x, φ y

lemma φ_pos (x : ℝ) : 0 < φ x := by unfold φ; positivity
lemma φ_neg (x : ℝ) : φ (-x) = φ x := by simp [φ]
lemma integrable_φ : Integrable φ := by
  unfold φ
  have h := integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
  simpa only [φ, show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring] using
    h.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
lemma integral_φ : ∫ x, φ x = 1 := by
  unfold φ
  rw [integral_const_mul]
  simp_rw [show ∀ x : ℝ, -x^2/2 = -(1/2:ℝ)*x^2 by intro x; ring]
  rw [integral_gaussian]
  have hp : Real.pi/(1/2:ℝ) = 2*Real.pi := by ring
  rw [hp, inv_mul_cancel₀ (by positivity)]
lemma hasDerivAt_φ (x : ℝ) : HasDerivAt φ (-x*φ x) x := by
  unfold φ
  convert ((((hasDerivAt_pow 2 x).neg.div_const 2).exp).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)) using 1 <;>
  first | rfl | (dsimp; ring)
lemma continuous_φ : Continuous φ := by exact continuous_iff_continuousAt.mpr fun x =>
  (hasDerivAt_φ x).continuousAt
lemma hasDerivAt_Φ (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have heq : Φ = fun a => Φ 0 + ∫ t in (0:ℝ)..a, φ t := by
    funext a
    have hi := intervalIntegral.integral_Iic_sub_Iic
      (a := 0) (b := a) integrable_φ.integrableOn integrable_φ.integrableOn
    change Φ a-Φ 0 = _ at hi
    linarith only [hi]
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right integrable_φ.intervalIntegrable
    continuous_φ.stronglyMeasurable.stronglyMeasurableAtFilter continuous_φ.continuousAt).const_add _
lemma continuous_Φ : Continuous Φ := continuous_iff_continuousAt.mpr fun x =>
  (hasDerivAt_Φ x).continuousAt
lemma strictMono_Φ : StrictMono Φ := strictMono_of_deriv_pos (fun x => by
    rw [(hasDerivAt_Φ x).deriv]; exact φ_pos x)
lemma Φ_pos (x : ℝ) : 0 < Φ x := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ (fun x => (φ_pos x).le))
    integrable_φ.integrableOn).mpr
  simp [Function.support, ne_of_gt (φ_pos _)]
lemma Φ_eq_one_sub_tail (x : ℝ) : Φ x = 1 - ∫ y in Ioi x, φ y := by
  have h := integral_add_compl measurableSet_Iic integrable_φ (s := Iic x)
  rw [compl_Iic, integral_φ] at h
  unfold Φ
  linarith only [h]
lemma Φ_neg (x : ℝ) : Φ (-x) = 1-Φ x := by
  have h := integral_comp_neg_Iic (-x) φ
  simp only [φ_neg, neg_neg] at h
  change Φ (-x) = (∫ y in Ioi x, φ y) at h
  rw [h, Φ_eq_one_sub_tail]
  ring
lemma Φ_lt_one (x : ℝ) : Φ x < 1 := by
  have h := Φ_pos (-x)
  rw [Φ_neg] at h
  linarith only [h]
lemma Φ_mem (x : ℝ) : Φ x ∈ Ioo (0:ℝ) 1 := ⟨Φ_pos x, Φ_lt_one x⟩
lemma tendsto_Φ_atTop : Tendsto Φ atTop (𝓝 1) := by
  have ht := tendsto_integral_Ioi_zero (f := φ) (μ := volume) tendsto_id
  convert ht.const_sub 1 using 1
  · exact funext Φ_eq_one_sub_tail
  · norm_num
lemma tendsto_Φ_atBot : Tendsto Φ atBot (𝓝 0) := by
  have ht := tendsto_Φ_atTop.comp tendsto_neg_atBot_atTop
  have hh := ht.const_sub 1
  simpa only [Function.comp_def, Φ_neg, sub_sub_cancel, sub_self] using hh
lemma range_Φ : range Φ = Ioo (0:ℝ) 1 := by
  apply Subset.antisymm
  · rintro _ ⟨x,rfl⟩; exact Φ_mem x
  · have hh := isPreconnected_univ.intermediate_value_Ioo
      (l₁ := atBot) (l₂ := atTop) (by simp) (by simp) continuous_Φ.continuousOn
      tendsto_Φ_atBot tendsto_Φ_atTop
    simpa only [image_univ] using hh

noncomputable def cdfIso : ℝ ≃o Ioo (0:ℝ) 1 :=
  (strictMono_Φ.orderIso Φ).trans (OrderIso.setCongr _ _ range_Φ)
noncomputable def q (p : ℝ) : ℝ :=
  if h : p ∈ Ioo (0:ℝ) 1 then cdfIso.symm ⟨p,h⟩ else 0
noncomputable def I (p : ℝ) : ℝ := φ (q p)
section Integration
variable {X : Type uX} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

end Integration
end GaussianPropeller.Quantile

end OAI


