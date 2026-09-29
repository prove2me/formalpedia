-- Prove2me | Definitions.Def_RepTheory_MulConvolution
-- name    : RepTheory_MulConvolution
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/5738dee7-ac8a-5596-9606-78a9202bf5ae
-- title:
--   Multiplicative convolution of complex functions on a group
-- statement:
--   For a group $G$ equipped with a measurable space structure, a measure $\mu$ on $G$ and functions $f,g\colon G\to\mathbb{C}$, [`MulConvolution.mulConv`](../def/RepTheory_MulConvolution.html#L16) is the function $x\mapsto\int_G f(y)\,g(y^{-1}x)\,d\mu(y)$, the integral being the Bochner integral; as always in Mathlib, the integral is $0$ at those $x$ for which the integrand fails to be integrable, so no integrability hypothesis enters the definition and `mulConv_apply` records the defining formula. The remaining declarations are the basic formal properties of this operation. Under the standing assumptions that $G$ is a topological group whose open sets are measurable and that $\mu$ is finite on compact sets, `integrable_mul_comp` states that if $f$ is locally constant with compact support and $g$ is locally constant, then for every $x$ the function $y\mapsto f(y)g(y^{-1}x)$ is $\mu$-integrable (it is continuous with compact support); `mulConv_add_left` and `mulConv_add_right` deduce additivity in each argument, in the left-hand case for $f_1,f_2$ locally constant with compact support and $g$ locally constant, and in the right-hand case for $f$ locally constant with compact support and $g_1,g_2$ locally constant. Homogeneity, `mulConv_smul_left` and `mulConv_smul_right`, holds for an arbitrary measure and arbitrary $f,g$: scaling either argument by $c\in\mathbb{C}$ scales the convolution by $c$. For supports, `hasCompactSupport_mulConv` shows that on a Hausdorff topological group the convolution of two compactly supported functions has compact support, the support being contained in the product of the two supports. Finally, `isLocallyConstant_mulConv` assumes only that multiplication on $G$ is continuous and that $g$ is invariant under right translation by all $u$ in some neighbourhood $U$ of $1$, i.e. $g(xu)=g(x)$ for all $x\in G$ and $u\in U$, and concludes that $\mathrm{mulConv}\,\mu\,f\,g$ is locally constant for every $f$.
--
--   **Relation to Mathlib.** Mathlib's `convolution` is set up for additively written groups and a bilinear pairing; the operation defined here is the multiplicative-group version for complex-valued functions, with the integrability conditions appearing only in the hypotheses of the individual lemmas rather than in the definition.
--
--   **Where it is used.** Together these results give the convolution product on the space of locally constant, compactly supported complex functions on a topological group — the Hecke-algebra setting for smooth representations of $p$-adic groups — which is used in the representation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_MulConvolution.lean

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace MulConvolution

open MeasureTheory Set Filter Topology

variable {G : Type*} [Group G] [MeasurableSpace G]

def mulConv (μ : Measure G) (f g : G → ℂ) : G → ℂ := fun x => ∫ y, f y * g (y⁻¹ * x) ∂μ

theorem mulConv_apply (μ : Measure G) (f g : G → ℂ) (x : G) :
    mulConv μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ := rfl

section Integrable

variable [TopologicalSpace G] [IsTopologicalGroup G] [OpensMeasurableSpace G] {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]

theorem integrable_mul_comp {f g : G → ℂ} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f)
    (hg : IsLocallyConstant g) (x : G) : Integrable (fun y => f y * g (y⁻¹ * x)) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact hf.continuous.mul (hg.continuous.comp (continuous_inv.mul continuous_const))
  · exact hfc.mul_right

theorem mulConv_add_left {f₁ f₂ g : G → ℂ} (hf₁ : IsLocallyConstant f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : IsLocallyConstant f₂) (hf₂c : HasCompactSupport f₂) (hg : IsLocallyConstant g) :
    mulConv μ (f₁ + f₂) g = mulConv μ f₁ g + mulConv μ f₂ g := by
  funext x
  simp only [mulConv, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_comp hf₁ hf₁c hg x) (integrable_mul_comp hf₂ hf₂c hg x)

theorem mulConv_add_right {f g₁ g₂ : G → ℂ} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f)
    (hg₁ : IsLocallyConstant g₁) (hg₂ : IsLocallyConstant g₂) :
    mulConv μ f (g₁ + g₂) = mulConv μ f g₁ + mulConv μ f g₂ := by
  funext x
  simp only [mulConv, Pi.add_apply, mul_add]
  exact integral_add (integrable_mul_comp hf hfc hg₁ x) (integrable_mul_comp hf hfc hg₂ x)

end Integrable

theorem mulConv_smul_left (μ : Measure G) (c : ℂ) (f g : G → ℂ) : mulConv μ (c • f) g = c • mulConv μ f g := by
  funext x
  simp only [mulConv, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem mulConv_smul_right (μ : Measure G) (c : ℂ) (f g : G → ℂ) :
    mulConv μ f (c • g) = c • mulConv μ f g := by
  funext x
  simp only [mulConv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

section Support

variable [TopologicalSpace G]

theorem hasCompactSupport_mulConv [IsTopologicalGroup G] [T2Space G] (μ : Measure G) {f g : G → ℂ}
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) : HasCompactSupport (mulConv μ f g) := by
  refine HasCompactSupport.intro (hfc.mul hgc) fun x hx => ?_
  have h0 : (fun y => f y * g (y⁻¹ * x)) = fun _ => 0 := by
    funext y
    by_cases hfy : f y = 0
    · rw [hfy, zero_mul]
    · have hgy : g (y⁻¹ * x) = 0 := by
        by_contra hgy
        exact hx (Set.mem_mul.mpr ⟨y, subset_tsupport _ (Function.mem_support.mpr hfy), y⁻¹ * x,
          subset_tsupport _ (Function.mem_support.mpr hgy), mul_inv_cancel_left y x⟩)
      rw [hgy, mul_zero]
  rw [mulConv_apply, h0, integral_zero]

theorem isLocallyConstant_mulConv [ContinuousMul G] (μ : Measure G) (f g : G → ℂ)
    (hg : ∃ U ∈ 𝓝 (1 : G), ∀ u ∈ U, ∀ x, g (x * u) = g x) : IsLocallyConstant (mulConv μ f g) := by
  obtain ⟨U, hU, hgU⟩ := hg
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hN : (fun y => x⁻¹ * y) ⁻¹' U ∈ 𝓝 x := by
    refine (continuous_const_mul x⁻¹).continuousAt.preimage_mem_nhds ?_
    show U ∈ 𝓝 (x⁻¹ * x)
    rwa [inv_mul_cancel]
  filter_upwards [hN] with y hy
  rw [← mul_inv_cancel_left x y, mulConv_apply, mulConv_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show f z * g (z⁻¹ * (x * (x⁻¹ * y))) = f z * g (z⁻¹ * x)
  rw [← mul_assoc z⁻¹ x, hgU (x⁻¹ * y) hy]

end Support

end MulConvolution

end

#print axioms MulConvolution.integrable_mul_comp
#print axioms MulConvolution.mulConv_add_left
#print axioms MulConvolution.mulConv_add_right
#print axioms MulConvolution.mulConv_smul_left
#print axioms MulConvolution.mulConv_smul_right
#print axioms MulConvolution.hasCompactSupport_mulConv
#print axioms MulConvolution.isLocallyConstant_mulConv


