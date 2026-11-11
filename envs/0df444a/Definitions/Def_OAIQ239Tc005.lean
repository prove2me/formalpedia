-- Prove2me | Definitions.Def_OAIQ239Tc005
-- name    : OAIQ239Tc005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:14:47.495392+00:00
-- url     : https://prove2.me/theorems/1ae828c3-a1b4-46b8-aada-d168851dd608
-- title:
--   Definitions bundle OAIQ239Tc005 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 92 declarations of OpenAI's Lean: 21 definitions and 71 theorems. The definitions and types are `OAI.TamingCompatibility.HilbertSobolev.boundedFourierMultiplier`, `OAI.TamingCompatibility.HilbertSobolev.derivative`, `OAI.TamingCompatibility.HilbertSobolev.greenNegOne`, `OAI.TamingCompatibility.HilbertSobolev.inclusion`, `OAI.TamingCompatibility.HilbertSobolev.liftOperator`, `OAI.TamingCompatibility.HilbertSobolev.localizationError`, `OAI.TamingCompatibility.HilbertSobolev.negativeProductMain`, `OAI.TamingCompatibility.HilbertSobolev.negativeProductTerm`, `OAI.TamingCompatibility.HilbertSobolev.perturbation`, `OAI.TamingCompatibility.HilbertSobolev.perturbationNegOne`, `OAI.TamingCompatibility.HilbertSobolev.perturbedHelmholtz`, `OAI.TamingCompatibility.HilbertSobolev.principalCoefficientSize`, `OAI.TamingCompatibility.HilbertSobolev.product`, `OAI.TamingCompatibility.HilbertSobolev.productNegOne`, `OAI.TamingCompatibility.HilbertSobolev.recover`, `OAI.TamingCompatibility.HilbertSobolev.reindex`, `OAI.TamingCompatibility.HilbertSobolev.secondDerivative`, `OAI.TamingCompatibility.HilbertSobolev.toDistribution`, `OAI.TamingCompatibility.HilbertSobolev.weakGradient`, `OAI.TamingCompatibility.HilbertSobolev.weakPrincipalCoefficientSize`, `OAI.TamingCompatibility.HilbertSobolev.weakValue`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_AffineBase`, `TamingCompatibility_Charts_AffineLocal`, `TamingCompatibility_Charts_LinearTransport`, `TamingCompatibility_DifferentialForms_Bessel`, `TamingCompatibility_DifferentialForms_ComplexEquiv`, `TamingCompatibility_DifferentialForms_FormPairing`, `TamingCompatibility_DifferentialForms_FramePairing`, `TamingCompatibility_DifferentialForms_GreenNeg`, `TamingCompatibility_DifferentialForms_Helmholtz`, `TamingCompatibility_DifferentialForms_PerturbationNeg`, `TamingCompatibility_DifferentialForms_Product`, `TamingCompatibility_DifferentialForms_ScaledLower`, `TamingCompatibility_Elliptic_DirectionalPrincipal`, `TamingCompatibility_Elliptic_FrozenCoefficient`, `TamingCompatibility_Elliptic_FrozenSystem`, `TamingCompatibility_Elliptic_InteriorRegularity`, `TamingCompatibility_Elliptic_MatrixH1Smooth`, `TamingCompatibility_Elliptic_PrincipalNormalize`, `TamingCompatibility_Elliptic_PrincipalTransport`, `TamingCompatibility_Elliptic_SecondDerivative`, `TamingCompatibility_Functional_SobolevSpace`, `TamingCompatibility_Hodge_ClosureLinear`, `TamingCompatibility_Hodge_HodgeDifferentialLocality`, `TamingCompatibility_Hodge_HodgeUniformOdd`, `TamingCompatibility_Hodge_LocalCodifferential`.
--
--   **Imports.** It imports the bundles `OAIQ239Tc000`, `OAIQ239Tc001` and `OAIQ239Tc002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc010`, `OAIQ239Tc011`, `OAIQ239Tc012` and `OAIQ239Tc013`; the statement `OAI.TamingCompatibility.HilbertSobolev.parameter_energy_two_jet`; the proof of `OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ239Tc000
import Definitions.Def_OAIQ239Tc001
import Definitions.Def_OAIQ239Tc002

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_SobolevSpace
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open _root_.MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap ENNReal

namespace TamingCompatibility.HilbertSobolev

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def toDistribution (s : ℝ) : H E F s →L[ℂ] 𝓢'(E,F) :=
  (besselPotential E F (-s)).comp (Lp.toTemperedDistributionCLM F volume 2)

variable {E F}

lemma toDistribution_injective (s : ℝ) : Function.Injective (toDistribution E F s) := by
  intro u v huv
  apply lp_injective
  have h := congrArg (besselPotential E F s) huv
  change besselPotential E F s (besselPotential E F (-s) (u : 𝓢'(E,F))) =
    besselPotential E F s (besselPotential E F (-s) (v : 𝓢'(E,F))) at h
  simpa using h

lemma bessel_toDistribution (s : ℝ) (u : H E F s) :
    besselPotential E F s (toDistribution E F s u) =
      Lp.toTemperedDistributionCLM F volume 2 u := by
  change besselPotential E F s (besselPotential E F (-s) (u : 𝓢'(E,F))) = _
  simp

lemma toDistribution_memSobolev (s : ℝ) (u : H E F s) :
    MemSobolev s 2 (toDistribution E F s u) :=
  ⟨u, bessel_toDistribution s u⟩

theorem range_toDistribution (s : ℝ) :
    Set.range (toDistribution E F s) = {u | MemSobolev s 2 u} := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact toDistribution_memSobolev s v
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change besselPotential E F (-s) (v : 𝓢'(E,F)) = u
    rw [← hv, besselPotential_besselPotential_apply]
    simp

def boundedFourierMultiplier (s : ℝ) (g : Lp ℂ ∞ (volume : Measure E)) :
    H E F s →L[ℂ] H E F s :=
  (Lp.fourierTransformₗᵢ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    multiplyLp g ∘L (Lp.fourierTransformₗᵢ E F).toContinuousLinearEquiv.toContinuousLinearMap

lemma boundedFourierMultiplier_apply (s : ℝ) (g : Lp ℂ ∞ (volume : Measure E))
    (u : H E F s) :
    boundedFourierMultiplier s g u = 𝓕⁻ (g • 𝓕 (u : Lp F 2 (volume : Measure E)) : Lp F 2 (volume : Measure E)) := rfl

lemma boundedFourierMultiplier_norm_le (s : ℝ)
    (g : Lp ℂ ∞ (volume : Measure E)) (u : H E F s) :
    ‖boundedFourierMultiplier s g u‖ ≤ ‖g‖ * ‖u‖ := by
  change ‖(Lp.fourierTransformₗᵢ E F).symm (g • 𝓕 (u : Lp F 2 (volume : Measure E)))‖ ≤ _
  rw [(Lp.fourierTransformₗᵢ E F).symm.norm_map]
  simpa only [Lp.norm_fourier_eq] using Lp.norm_smul_le g (𝓕 (u : Lp F 2 (volume : Measure E)))

lemma boundedFourierMultiplier_distribution (s : ℝ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hb : MemLp g ∞ (volume : Measure E))
    (u : H E F s) :
    (boundedFourierMultiplier s (hb.toLp g) u : 𝓢'(E,F)) =
      fourierMultiplierCLM F g (u : 𝓢'(E,F)) := by
  rw [boundedFourierMultiplier_apply, ← Lp.fourierInv_toTemperedDistribution_eq,
    Lp.toTemperedDistribution_smul_eq hg,
    ← Lp.fourier_toTemperedDistribution_eq]
  rfl

lemma toDistribution_boundedFourierMultiplier (s : ℝ) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (hb : MemLp g ∞ (volume : Measure E))
    (u : H E F s) :
    toDistribution E F s (boundedFourierMultiplier s (hb.toLp g) u) =
      fourierMultiplierCLM F g (toDistribution E F s u) := by
  change besselPotential E F (-s)
      (boundedFourierMultiplier s (hb.toLp g) u : 𝓢'(E,F)) =
    fourierMultiplierCLM F g (besselPotential E F (-s) (u : 𝓢'(E,F)))
  rw [boundedFourierMultiplier_distribution s hg hb,
    bessel_fourierMultiplier_comm (-s) hg]

def reindex (s t : ℝ) : H E F s ≃ₗᵢ[ℂ] H E F t := LinearIsometryEquiv.refl ℂ _

lemma toDistribution_reindex (s t : ℝ) (u : H E F s) :
    toDistribution E F t (reindex s t u) =
      besselPotential E F (s - t) (toDistribution E F s u) := by
  change besselPotential E F (-t) (u : 𝓢'(E,F)) =
      besselPotential E F (s - t) (besselPotential E F (-s) (u : 𝓢'(E,F)))
  rw [besselPotential_besselPotential_apply, show -s + (s - t) = -t by ring]

def inclusion {s t : ℝ} (h : t ≤ s) : H E F s →L[ℂ] H E F t :=
  (reindex s t).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    boundedFourierMultiplier s ((weight_memLp_top (sub_nonpos.mpr h)).toLp _)

lemma inclusion_norm_le {s t : ℝ} (h : t ≤ s) (u : H E F s) :
    ‖inclusion h u‖ ≤ ‖u‖ := by
  change ‖boundedFourierMultiplier s
    ((weight_memLp_top (sub_nonpos.mpr h)).toLp _) u‖ ≤ ‖u‖
  refine (boundedFourierMultiplier_norm_le s _ u).trans ?_
  have hw := toLp_top_norm_le (weight_memLp_top (E := E) (sub_nonpos.mpr h))
    zero_le_one (weight_le_one (sub_nonpos.mpr h))
  simpa using mul_le_mul_of_nonneg_right hw (norm_nonneg u)

lemma toDistribution_inclusion {s t : ℝ} (h : t ≤ s) (u : H E F s) :
    toDistribution E F t (inclusion h u) = toDistribution E F s u := by
  change toDistribution E F t (reindex s t
    (boundedFourierMultiplier s ((weight_memLp_top (sub_nonpos.mpr h)).toLp _) u)) = _
  rw [toDistribution_reindex, toDistribution_boundedFourierMultiplier s
    (weight_temperate (t-s)) (weight_memLp_top (sub_nonpos.mpr h))]
  change besselPotential E F (s-t)
    (besselPotential E F (t-s) (toDistribution E F s u)) = _
  rw [besselPotential_besselPotential_apply]
  have hzero : t - s + (s - t) = 0 := by ring
  rw [hzero, besselPotential_zero, ContinuousLinearMap.id_apply]

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Bessel
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma liftOperator_exists {s t : ℝ} (A : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (hA : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (A u)) (u : H E F s) :
    ∃ v : H E F t, toDistribution E F t v = A (toDistribution E F s u) := by
  change A (toDistribution E F s u) ∈ Set.range (toDistribution E F t)
  rw [range_toDistribution]
  exact hA _ (toDistribution_memSobolev s u)

def liftOperator {s t : ℝ} (A : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (hA : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (A u)) :
    H E F s →L[ℂ] H E F t := by
  let hex := liftOperator_exists A hA
  let L : H E F s →ₗ[ℂ] H E F t :=
    { toFun := fun u => (hex u).choose
      map_add' := fun u v => by
        apply toDistribution_injective t
        rw [(hex (u+v)).choose_spec, map_add, map_add, map_add,
          (hex u).choose_spec, (hex v).choose_spec]
      map_smul' := fun c u => by
        apply toDistribution_injective t
        rw [(hex (c • u)).choose_spec, map_smul, map_smul, map_smul,
          (hex u).choose_spec]
        rfl }
  apply ContinuousLinearMap.ofIsClosedGraph (g := L)
  have hg : (L.graph : Set (H E F s × H E F t)) =
      {p | toDistribution E F t p.2 = A (toDistribution E F s p.1)} := by
    ext p
    change p.2 = L p.1 ↔ toDistribution E F t p.2 = A (toDistribution E F s p.1)
    rw [← (hex p.1).choose_spec]
    exact (toDistribution_injective t).eq_iff.symm
  rw [hg]
  exact isClosed_eq ((toDistribution E F t).continuous.comp continuous_snd)
    (A.continuous.comp ((toDistribution E F s).continuous.comp continuous_fst))

lemma toDistribution_liftOperator {s t : ℝ} (A : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (hA : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (A u)) (u : H E F s) :
    toDistribution E F t (liftOperator A hA u) = A (toDistribution E F s u) := by
  dsimp only [liftOperator, ContinuousLinearMap.ofIsClosedGraph,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact (liftOperator_exists A hA u).choose_spec

open scoped LineDeriv

def derivative (s : ℝ) (v : E) : H E F s →L[ℂ] H E F (s-1) :=
  liftOperator (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E,F) v) (fun _ h => h.lineDerivOp)

lemma toDistribution_derivative (s : ℝ) (v : E) (u : H E F s) :
    toDistribution E F (s-1) (derivative s v u) = ∂_{v} (toDistribution E F s u) :=
  toDistribution_liftOperator _ _ _

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Helmholtz
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
namespace TamingCompatibility.EuclideanGreen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
open TemperedDistribution

theorem green_helmholtz (f : 𝓢'(E,F)) :
    besselPotential E F (-2) (helmholtz f) = f := by
  rw [← bessel_two_eq_helmholtz, besselPotential_besselPotential_apply]
  norm_num

end TamingCompatibility.EuclideanGreen

namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def recover (s : ℝ) (u : H E F s) (du : basisIndex E → H E F s) : H E F (s+1) :=
  reindex (s-1) (s+1) (inclusion (show s-1 ≤ s by linarith) u -
    ((2*Real.pi)^2)⁻¹ • ∑ i, derivative s (stdOrthonormalBasis ℝ E i) (du i))

lemma recover_distribution (s : ℝ) (u : H E F s) (du : basisIndex E → H E F s) :
    toDistribution E F (s+1) (recover s u du) = besselPotential E F (-2)
      (toDistribution E F s u - ((2*Real.pi)^2)⁻¹ •
        ∑ i, ∂_{stdOrthonormalBasis ℝ E i} (toDistribution E F s (du i))) := by
  rw [recover, toDistribution_reindex]
  have he : s-1-(s+1) = -2 := by ring
  rw [he, map_sub, ContinuousLinearMap.map_smul_of_tower, map_sum, toDistribution_inclusion]
  simp only [toDistribution_derivative]

lemma recover_gradient (s : ℝ) (u : H E F (s+1)) :
    recover s (inclusion (show s ≤ s+1 by linarith) u)
      (fun i => derivative (s+1) (stdOrthonormalBasis ℝ E i) u) = u := by
  apply toDistribution_injective (s+1)
  rw [recover_distribution, toDistribution_inclusion]
  have hd (i : basisIndex E) :
      toDistribution E F s (derivative (s+1) (stdOrthonormalBasis ℝ E i) u) =
        ∂_{stdOrthonormalBasis ℝ E i} (toDistribution E F (s+1) u) := by
    have h := toDistribution_derivative (s+1) (stdOrthonormalBasis ℝ E i) u
    have he : s+1-1 = s := by ring
    rw [he] at h
    exact h
  simp only [hd]
  rw [← TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ E)]
  change besselPotential E F (-2) (EuclideanGreen.helmholtz (toDistribution E F (s+1) u)) = _
  exact EuclideanGreen.green_helmholtz _

lemma recover_norm_le (s : ℝ) (u : H E F s) (du : basisIndex E → H E F s) :
    ‖recover s u du‖ ≤ ‖u‖ + |((2*Real.pi)^2)⁻¹| *
      ∑ i, ‖derivative (F := F) s (stdOrthonormalBasis ℝ E i)‖ * ‖du i‖ := by
  rw [recover, (reindex (s-1) (s+1)).norm_map]
  apply (norm_sub_le _ _).trans
  apply add_le_add (inclusion_norm_le _ u)
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ =>
    ContinuousLinearMap.le_opNorm _ _))

theorem norm_le_gradient (s : ℝ) (u : H E F (s+1)) :
    ‖u‖ ≤ ‖inclusion (show s ≤ s+1 by linarith) u‖ + |((2*Real.pi)^2)⁻¹| *
      ∑ i, ‖derivative (F := F) s (stdOrthonormalBasis ℝ E i)‖ *
        ‖derivative (s+1) (stdOrthonormalBasis ℝ E i) u‖ := by
  have h := recover_norm_le s (inclusion (show s ≤ s+1 by linarith) u)
    (fun i => derivative (s+1) (stdOrthonormalBasis ℝ E i) u)
  rw [recover_gradient] at h
  exact h

end TamingCompatibility.HilbertSobolev
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Product
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def product (n : ℕ) (g : 𝓢(E,ℂ)) : H E F n →L[ℂ] H E F n :=
  liftOperator (smulLeftCLM F g) (fun _ h =>
    EuclideanSobolevOperators.memSobolev_nat_product n g h)

lemma toDistribution_product (n : ℕ) (g : 𝓢(E,ℂ)) (u : H E F n) :
    toDistribution E F n (product n g u) = smulLeftCLM F g (toDistribution E F n u) :=
  toDistribution_liftOperator _ _ _

lemma product_inclusion (n : ℕ) (g : 𝓢(E,ℂ)) (u : H E F (n+1)) :
    inclusion (show (n:ℝ) ≤ n+1 by linarith) (product (n+1) g u) =
      product n g (inclusion (show (n:ℝ) ≤ n+1 by linarith) u) := by
  apply toDistribution_injective (n:ℝ)
  rw [toDistribution_inclusion, toDistribution_product, toDistribution_inclusion]
  simpa only [toDistribution, Nat.cast_add, Nat.cast_one] using toDistribution_product (n+1) g u

lemma product_derivative (n : ℕ) (g : 𝓢(E,ℂ)) (v : E) (u : H E F (n+1)) :
    derivative (n+1) v (product (n+1) g u) =
      product n (∂_{v} g) (inclusion (show (n:ℝ) ≤ n+1 by linarith) u) +
      product n g (derivative (n+1) v u) := by
  apply toDistribution_injective (n:ℝ)
  have he : (n:ℝ)+1-1 = n := by ring
  have hd (w : H E F (n+1)) :
      toDistribution E F n (derivative ((n:ℝ)+1) v w) =
        ∂_{v} (toDistribution E F ((n:ℝ)+1) w) := by
    have h := toDistribution_derivative ((n:ℝ)+1) v w
    rw [he] at h
    exact h
  have hp : toDistribution E F ((n:ℝ)+1) (product (n+1) g u) =
      smulLeftCLM F g (toDistribution E F ((n:ℝ)+1) u) := by
    simpa only [toDistribution, Nat.cast_add, Nat.cast_one] using toDistribution_product (n+1) g u
  rw [hd, hp, EuclideanSobolevOperators.distribution_derivative_product]
  rw [map_add, toDistribution_product, toDistribution_product,
    toDistribution_inclusion, hd]

lemma product_zero_eq (g : 𝓢(E,ℂ)) (u : H E F 0) :
    product 0 g u = (g.toBoundedContinuousFunction.memLp_top (μ := volume)).toLp g.toBoundedContinuousFunction • u := by
  apply toDistribution_injective 0
  have hp : toDistribution E F 0 (product 0 g u) =
      smulLeftCLM F g (toDistribution E F 0 u) := by
    simpa only [toDistribution, Nat.cast_zero] using toDistribution_product 0 g u
  rw [hp]
  simp only [toDistribution, neg_zero, besselPotential_zero,
    ContinuousLinearMap.id_comp]
  exact Lp.toTemperedDistribution_smul_eq g.hasTemperateGrowth
    (g.toBoundedContinuousFunction.memLp_top (μ := volume)) u |>.symm

lemma product_zero_norm_le (g : 𝓢(E,ℂ)) (u : H E F 0) :
    ‖product 0 g u‖ ≤ ‖g.toBoundedContinuousFunction‖ * ‖u‖ := by
  rw [product_zero_eq]
  apply (Lp.norm_smul_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
  exact toLp_top_norm_le (g.toBoundedContinuousFunction.memLp_top (μ := volume))
    (norm_nonneg _) (fun x => g.toBoundedContinuousFunction.norm_coe_le_norm x)

theorem product_estimate (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (g : 𝓢(E,ℂ)) (u : H E F n),
      ‖product n g u‖ ≤ C * coefficientSize n g * ‖u‖ := by
  induction n with
  | zero =>
    refine ⟨1, zero_lt_one, fun g u => ?_⟩
    simpa only [one_mul, coefficientSize] using product_zero_norm_le g u
  | succ n ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    let c : ℝ := |((2*Real.pi)^2)⁻¹|
    let D (i : basisIndex E) : ℝ := ‖derivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)‖
    let D' (i : basisIndex E) : ℝ := ‖derivative (F := F) ((n:ℝ)+1) (stdOrthonormalBasis ℝ E i)‖
    let K : ℝ := 1 + c * ∑ i, D i * (1 + D' i)
    have hc : 0 ≤ c := abs_nonneg _
    have hD (i) : 0 ≤ D i := norm_nonneg _
    have hD' (i) : 0 ≤ D' i := norm_nonneg _
    have hK : 0 < K := by
      dsimp only [K]
      positivity
    refine ⟨C*K, mul_pos hC hK, fun g u => ?_⟩
    let S := coefficientSize (n+1) g
    let A := C * S * ‖u‖
    have hS : 0 ≤ S := coefficientSize_nonneg _ _
    have hB (f : 𝓢(E,ℂ)) (hf : coefficientSize n f ≤ S) (w : H E F n) :
        ‖product n f w‖ ≤ C*S*‖w‖ :=
      (hbound f w).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf hC.le) (norm_nonneg w))
    have hu0 : ‖inclusion (show (n:ℝ) ≤ n+1 by linarith) u‖ ≤ ‖u‖ :=
      inclusion_norm_le (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ))
        (show (n:ℝ) ≤ n+1 by linarith) u
    have hz : ‖inclusion (show (n:ℝ) ≤ n+1 by linarith) (product (n+1) g u)‖ ≤ A := by
      rw [product_inclusion]
      exact (hB g (coefficientSize_le_succ n g) _).trans
        (mul_le_mul_of_nonneg_left hu0 (mul_nonneg hC.le hS))
    have hd (i : basisIndex E) :
        ‖derivative ((n:ℝ)+1) (stdOrthonormalBasis ℝ E i) (product (n+1) g u)‖ ≤
          A * (1 + D' i) := by
      rw [product_derivative]
      have h1 := (hB (∂_{stdOrthonormalBasis ℝ E i} g)
        (coefficientSize_derivative_le n g i) _).trans
        (mul_le_mul_of_nonneg_left hu0 (mul_nonneg hC.le hS))
      have h2 := (hB g (coefficientSize_le_succ n g)
        (derivative ((n:ℝ)+1) (stdOrthonormalBasis ℝ E i) u)).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ u)
          (mul_nonneg hC.le hS))
      apply (norm_add_le _ _).trans
      calc
        _ ≤ A + C*S*(D' i*‖u‖) := add_le_add h1 h2
        _ = A*(1+D' i) := by dsimp only [A] <;> ring
    have hn := norm_le_gradient (n:ℝ) (product (n+1) g u)
    apply hn.trans
    calc
      _ ≤ A + c * ∑ i, D i * (A * (1+D' i)) :=
        add_le_add hz (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hd i) (hD i))) hc)
      _ = (C*K)*S*‖u‖ := by
        have he : (∑ i, D i * (A * (1+D' i))) = A * ∑ i, D i * (1+D' i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [he]
        dsimp only [A, K]
        ring

theorem product_operator_estimate (n : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ g : 𝓢(E,ℂ), ‖product (F := F) n g‖ ≤ C * coefficientSize n g := by
  obtain ⟨C, hC, h⟩ := product_estimate (E := E) (F := F) n
  refine ⟨C, hC, fun g => ?_⟩
  exact ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC.le (coefficientSize_nonneg n g)) (h g)

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_GreenNeg
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def greenNegOne : H E F (-1) ≃ₗᵢ[ℂ] H E F 1 := reindex (-1) 1

def weakValue : H E F (-1) →L[ℂ] H E F 0 :=
  (inclusion (E := E) (F := F) (s := 1) (t := 0) (by norm_num)).comp
    (greenNegOne (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap

def weakGradient (v : E) : H E F (-1) →L[ℂ] H E F 0 :=
  (derivative (F := F) 1 v).comp
    (greenNegOne (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap

lemma weakValue_norm_le (u : H E F (-1)) : ‖weakValue u‖ ≤ ‖u‖ := by
  exact (inclusion_norm_le (E := E) (F := F) (s := 1) (t := 0)
    (by norm_num) (greenNegOne u)).trans (greenNegOne.norm_map u).le

lemma weakGradient_norm_le (v : E) (u : H E F (-1)) :
    ‖weakGradient v u‖ ≤ ‖derivative (F := F) 1 v‖ * ‖u‖ := by
  change ‖derivative (F := F) 1 v (greenNegOne u)‖ ≤ _
  simpa only [greenNegOne.norm_map] using
    ContinuousLinearMap.le_opNorm (derivative (F := F) 1 v) (greenNegOne u)

def negativeProductMain (g : 𝓢(E,ℂ)) : H E F (-1) →L[ℂ] H E F (-1) :=
  (inclusion (E := E) (F := F) (s := 0) (t := -1) (by norm_num)).comp
    ((product 0 g).comp weakValue)

def negativeProductTerm (g : 𝓢(E,ℂ)) (v : E) : H E F (-1) →L[ℂ] H E F (-1) :=
  (derivative (F := F) 0 v).comp ((product 0 g).comp (weakGradient v)) -
  (inclusion (E := E) (F := F) (s := 0) (t := -1) (by norm_num)).comp
    ((product 0 (∂_{v} g)).comp (weakGradient v))

def productNegOne (g : 𝓢(E,ℂ)) : H E F (-1) →L[ℂ] H E F (-1) :=
  negativeProductMain g - (((2*Real.pi)^2)⁻¹ : ℝ) •
    ∑ i : basisIndex E, negativeProductTerm g (stdOrthonormalBasis ℝ E i)

lemma product_zero_le_size_one (g f : 𝓢(E,ℂ))
    (hf : ‖f.toBoundedContinuousFunction‖ ≤ coefficientSize 1 g) (w : H E F 0) :
    ‖product 0 f w‖ ≤ coefficientSize 1 g * ‖w‖ :=
  (product_zero_norm_le f w).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg _))

lemma negativeProductMain_norm_le (g : 𝓢(E,ℂ)) (u : H E F (-1)) :
    ‖negativeProductMain g u‖ ≤ coefficientSize 1 g * ‖u‖ := by
  have h0 := product_zero_le_size_one g g (coefficientSize_le_succ 0 g) (weakValue u)
  have h1 := inclusion_norm_le (E := E) (F := F) (s := 0) (t := -1) (by norm_num)
    (product 0 g (weakValue u))
  exact h1.trans (h0.trans (mul_le_mul_of_nonneg_left (weakValue_norm_le u)
    (coefficientSize_nonneg _ _)))

lemma negativeProductTerm_norm_le (g : 𝓢(E,ℂ)) (i : basisIndex E) (u : H E F (-1)) :
    ‖negativeProductTerm g (stdOrthonormalBasis ℝ E i) u‖ ≤
      coefficientSize 1 g * ‖u‖ *
        ((‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖ + 1) *
          ‖derivative (F := F) 1 (stdOrthonormalBasis ℝ E i)‖) := by
  let v := stdOrthonormalBasis ℝ E i
  let w : H E F 0 := weakGradient v u
  let A := coefficientSize 1 g
  let D := ‖derivative (F := F) 0 v‖
  let D' := ‖derivative (F := F) 1 v‖
  have hw : ‖w‖ ≤ D' * ‖u‖ := weakGradient_norm_le v u
  have h1 : ‖derivative (F := F) 0 v (product 0 g w)‖ ≤ D * (A * (D' * ‖u‖)) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left
      ((product_zero_le_size_one g g (coefficientSize_le_succ 0 g) w).trans
        (mul_le_mul_of_nonneg_left hw (coefficientSize_nonneg _ _))) (norm_nonneg _))
  have h2 : ‖inclusion (E := E) (F := F) (s := 0) (t := -1) (by norm_num)
      (product 0 (∂_{v} g) w)‖ ≤ A * (D' * ‖u‖) :=
    (inclusion_norm_le (E := E) (F := F) (s := 0) (t := -1) (by norm_num) _).trans
      ((product_zero_le_size_one g (∂_{v} g) (coefficientSize_derivative_le 0 g i) w).trans
        (mul_le_mul_of_nonneg_left hw (coefficientSize_nonneg _ _)))
  change ‖derivative (F := F) 0 v (product 0 g w) -
    inclusion (E := E) (F := F) (s := 0) (t := -1) (by norm_num) (product 0 (∂_{v} g) w)‖ ≤ _
  exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by dsimp only [A,D,D',v] <;> ring))

lemma productNegOne_norm_le (g : 𝓢(E,ℂ)) (u : H E F (-1)) :
    ‖productNegOne g u‖ ≤ coefficientSize 1 g * ‖u‖ *
      (1 + |((2*Real.pi)^2)⁻¹| * ∑ i : basisIndex E,
        (‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖ + 1) *
        ‖derivative (F := F) 1 (stdOrthonormalBasis ℝ E i)‖) := by
  rw [productNegOne, sub_apply, smul_apply, sum_apply]
  apply (norm_sub_le _ _).trans
  rw [norm_smul, Real.norm_eq_abs]
  have hterm := (norm_sum_le Finset.univ (fun i : basisIndex E =>
    negativeProductTerm (F := F) g (stdOrthonormalBasis ℝ E i) u)).trans (Finset.sum_le_sum
    (fun i _ => negativeProductTerm_norm_le g i u))
  apply (add_le_add (negativeProductMain_norm_le g u)
    (mul_le_mul_of_nonneg_left hterm (abs_nonneg _))).trans_eq
  rw [← Finset.mul_sum]
  ring

lemma productNegOne_operator_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ g : 𝓢(E,ℂ),
      ‖productNegOne (F := F) g‖ ≤ C * coefficientSize 1 g := by
  let C : ℝ := 1 + |((2*Real.pi)^2)⁻¹| * ∑ i : basisIndex E,
      (‖derivative (F := F) 0 (stdOrthonormalBasis ℝ E i)‖ + 1) *
      ‖derivative (F := F) 1 (stdOrthonormalBasis ℝ E i)‖
  have hC : 0 < C := by dsimp only [C] <;> positivity
  refine ⟨C, hC, fun g => (productNegOne (F := F) g).opNorm_le_bound
    (mul_nonneg hC.le (coefficientSize_nonneg _ _)) (fun u => ?_)⟩
  convert productNegOne_norm_le g u using 1
  all_goals try with_reducible_and_instances rfl
  ring

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SecondDerivative
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def secondDerivative (s : ℝ) (v w : E) : H E F (s+2) →L[ℂ] H E F s :=
  (derivative (s+1) v).comp (derivative (s+2) w)

def perturbation (n : ℕ) (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    H E F ((n:ℝ)+2) →L[ℂ] H E F n :=
  ∑ i, ∑ j, (product n (a i j)).comp
    (secondDerivative n (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j))

def principalCoefficientSize (n : ℕ)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) : ℝ :=
  ∑ i, ∑ j, coefficientSize n (a i j) *
    ‖secondDerivative (F := F) n (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖

lemma perturbation_norm_le (n : ℕ) {C : ℝ}
    (hp : ∀ g : 𝓢(E,ℂ), ‖product (F := F) n g‖ ≤ C * coefficientSize n g)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    ‖perturbation (F := F) n a‖ ≤ C * principalCoefficientSize (F := F) n a := by
  unfold perturbation principalCoefficientSize
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_right (hp (a i j))
          (norm_nonneg (secondDerivative (F := F) n
            (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)))))

def perturbedHelmholtz (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  EuclideanGreen.helmholtz u + differentialPerturbation a u

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PerturbationNeg
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def perturbationNegOne (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    H E F 1 →L[ℂ] H E F (-1) :=
  ∑ i, ∑ j, (productNegOne (F := F) (a i j)).comp
    (secondDerivative (F := F) (-1) (stdOrthonormalBasis ℝ E i)
      (stdOrthonormalBasis ℝ E j))

def weakPrincipalCoefficientSize
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) : ℝ :=
  ∑ i, ∑ j, coefficientSize 1 (a i j) *
    ‖secondDerivative (F := F) (-1) (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖

lemma perturbationNegOne_norm_le {C : ℝ}
    (hp : ∀ g : 𝓢(E,ℂ), ‖productNegOne (F := F) g‖ ≤ C * coefficientSize 1 g)
    (a : basisIndex E → basisIndex E → 𝓢(E,ℂ)) :
    ‖perturbationNegOne (F := F) a‖ ≤ C * weakPrincipalCoefficientSize (F := F) a := by
  unfold perturbationNegOne weakPrincipalCoefficientSize
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_right (hp (a i j))
        (norm_nonneg (secondDerivative (F := F) (-1)
          (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)))))

lemma secondCommutator_memSobolev (n : ℕ) (g : 𝓢(E,ℂ)) (v w : E)
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (secondCommutator g v w u) := by
  have huv : MemSobolev n 2 (∂_{v} u) := by
    convert hu.lineDerivOp (m := v) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have huw : MemSobolev n 2 (∂_{w} u) := by
    convert hu.lineDerivOp (m := w) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact ((memSobolev_nat_product n _ (hu.mono (by linarith))).add
    (memSobolev_nat_product n _ huv)).add (memSobolev_nat_product n _ huw)

def localizationError (a : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  -(((2*Real.pi)^2)⁻¹ : ℝ) • ∑ i, secondCommutator g
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i) u +
  ∑ i, ∑ j, smulLeftCLM F (a i j) (secondCommutator g
    (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) u)

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_AffineBase
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem memSobolev_nat_affine (n : ℕ) (p : E) (r : ℝ) (hr : r ≠ 0)
    {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) :
    MemSobolev n 2 (affineDistribution p r hr u) := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.cast_zero] at hu ⊢
    exact memSobolev_zero_affine p r hr hu
  | succ n ih =>
    have hu' : MemSobolev n 2 u := hu.mono (by exact_mod_cast Nat.le_succ n)
    have hd (i : Fin (Module.finrank ℝ E)) :
        MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} (affineDistribution p r hr u)) := by
      have hdu : MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} u) := by
        convert hu.lineDerivOp using 1
        all_goals try with_reducible_and_instances rfl
        simp
      have ha := (ih hdu).smul (r⁻¹:ℝ)
      rw [affineDistribution_derivative] at ha
      have hc (w : 𝓢'(E,F)) : ((r⁻¹:ℝ):ℂ) • (r • w) = w := by
        rw [← algebraMap_smul ℂ r w, show algebraMap ℝ ℂ r = (r:ℂ) from rfl,
          smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr, Complex.ofReal_one, one_smul]
      rw [hc] at ha
      exact ha
    simpa using memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ E) (ih hu') hd

end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_MatrixH1Smooth
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma matrixLowerOrder_locality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (matrixLowerOrder b L v c K (smulLeftCLM F h u)) =
      smulLeftCLM F g (matrixLowerOrder b L v c K u) := by
  simp only [matrixLowerOrder, map_add, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [coefficient_products_commute g (b i), distribution_derivative_product,
      map_add, fiberMap_product, fiberMap_product, map_add,
      cutoff_mul_derivative g h hh, cutoff_mul_cutoff g h hh, zero_add]
    exact coefficient_products_commute (b i) g _
  · apply Finset.sum_congr rfl
    intro i _
    rw [coefficient_products_commute g (c i), fiberMap_product,
      cutoff_mul_cutoff g h hh]
    exact coefficient_products_commute (c i) g _

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_InteriorRegularity
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter Set
open scoped SchwartzMap LineDeriv Topology Manifold ContDiff BoundedContinuousFunction
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma MemSobolevLoc.mono {U : Set E} {s t : ℝ} {u : 𝓢'(E,F)}
    (h : MemSobolevLoc U s u) (hst : t ≤ s) : MemSobolevLoc U t u :=
  fun g hg hgU => (h g hg hgU).mono hst

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma linearDistribution_apply (L : E ≃L[ℝ] E) (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    linearDistribution L u φ = u (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma linearDistribution_derivative (L : E ≃L[ℝ] E) (u : 𝓢'(E,F)) (v : E) :
    linearDistribution L (∂_{v} u) = ∂_{L v} (linearDistribution L u) := by
  ext φ
  simp only [linearDistribution_apply,lineDerivOp_apply_apply,
    linearSchwartz_derivative,map_neg]

lemma linearDistribution_lp (L : E ≃L[ℝ] E) (f : Lp F 2 (volume : Measure E)) :
    ∃ g : Lp F 2 (volume : Measure E), linearDistribution L (f : 𝓢'(E,F)) = (g : 𝓢'(E,F)) := by
  let c : ℝ := |(LinearMap.det (L : E →ₗ[ℝ] E))⁻¹|
  let h : E → F := fun y => c • f (L.symm y)
  have hh : MemLp h 2 (volume : Measure E) :=
    (memLp_comp_linearEquiv L.symm (Lp.memLp f)).const_smul c
  refine ⟨hh.toLp h,?_⟩
  ext φ
  rw [linearDistribution_apply,Lp.toTemperedDistribution_apply,Lp.toTemperedDistribution_apply]
  have he : (∫ y, φ y • (hh.toLp h) y) = ∫ y, φ y • h y := by
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp] with y hy
    rw [hy]
  rw [he]
  change (∫ x, φ (L x) • f x) = _
  have hm := L.toHomeomorph.measurableEmbedding.integral_map
    (μ := (volume : Measure E)) (fun y => φ y • f (L.symm y))
  change (∫ y, φ y • f (L.symm y) ∂Measure.map L volume) =
    ∫ x, φ (L x) • f (L.symm (L x)) at hm
  rw [show Measure.map L volume = ENNReal.ofReal c • volume from
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume L.toLinearEquiv.isUnit_det'.ne_zero,
    integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _)] at hm
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hm
  rw [← hm,← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  exact smul_comm c (φ y) _

lemma memSobolev_zero_linear (L : E ≃L[ℝ] E) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (linearDistribution L u) := by
  obtain ⟨f,hf⟩ := hu
  have he : u = (f : 𝓢'(E,F)) := by simpa using hf
  rw [he]
  obtain ⟨g,hg⟩ := linearDistribution_lp L f
  exact ⟨g,by simpa using hg⟩

theorem memSobolev_nat_linear (n : ℕ) (L : E ≃L[ℝ] E) {u : 𝓢'(E,F)}
    (hu : MemSobolev n 2 u) : MemSobolev n 2 (linearDistribution L u) := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.cast_zero] at hu ⊢
    exact memSobolev_zero_linear L hu
  | succ n ih =>
    have hu' : MemSobolev n 2 u := hu.mono (by exact_mod_cast Nat.le_succ n)
    have hd (i : Fin (Module.finrank ℝ E)) :
        MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} (linearDistribution L u)) := by
      have hdu : MemSobolev n 2 (∂_{L.symm (stdOrthonormalBasis ℝ E i)} u) := by
        convert hu.lineDerivOp using 1
        all_goals try with_reducible_and_instances rfl
        simp
      have h := ih hdu
      rw [linearDistribution_derivative,ContinuousLinearEquiv.apply_symm_apply] at h
      exact h
    simpa using memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ E) (ih hu') hd
end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_AffineLocal
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma memSobolevLoc_affine (n : ℕ) (p : E) (r : ℝ) (hr : r ≠ 0)
    {U : Set E} {u : 𝓢'(E,F)} (hu : HilbertSobolev.MemSobolevLoc U n u) :
    HilbertSobolev.MemSobolevLoc ((fun y => r⁻¹ • y + -(r⁻¹ • p)) ⁻¹' U) n
      (affineDistribution p r hr u) := by
  intro g hg hgU
  let q := affineSchwartz p r hr g
  have he : (q : E → ℂ) = g ∘ affineHomeomorph p r hr := by
    funext x
    exact affineSchwartz_apply p x r hr g
  have hq : HasCompactSupport (q : E → ℂ) := by
    rw [he]
    exact hg.comp_homeomorph _
  have hqU : tsupport q ⊆ U := by
    rw [he,tsupport_comp_eq_preimage]
    intro x hx
    have h := hgU hx
    simpa only [mem_preimage,affineHomeomorph_apply,affine_inverse_point p x hr] using h
  have h := memSobolev_nat_affine n p r hr (hu q hq hqU)
  rw [affineDistribution_product,affineSchwartz_comp_inverse] at h
  exact h

lemma memSobolevLoc_zoom (n : ℕ) (p : E) (r : ℝ) (hr : r ≠ 0)
    {U : Set E} {u : 𝓢'(E,F)} (hu : HilbertSobolev.MemSobolevLoc U n u) :
    HilbertSobolev.MemSobolevLoc ((fun y => r • y+p) ⁻¹' U) n (zoomDistribution p r hr u) := by
  have h := memSobolevLoc_affine n (-(r⁻¹ • p)) r⁻¹ (inv_ne_zero hr) hu
  simpa only [zoomDistribution,inv_inv,smul_neg,smul_smul,mul_inv_cancel₀ hr,one_smul,neg_neg] using h

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LinearTransport
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma linearDistribution_product (L : E ≃L[ℝ] E) (g : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    linearDistribution L (smulLeftCLM F g u) =
      smulLeftCLM F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g) (linearDistribution L u) := by
  ext φ
  simp only [linearDistribution_apply,smulLeftCLM_apply_apply]
  congr 1
  ext x
  change SchwartzMap.smulLeftCLM ℂ g (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L φ) x =
    SchwartzMap.smulLeftCLM ℂ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g) φ (L x)
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm g).hasTemperateGrowth]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [CompleteSpace G] in
lemma linearDistribution_postcomp (L : E ≃L[ℝ] E) (K : F →L[ℂ] G) (u : 𝓢'(E,F)) :
    linearDistribution L (HilbertSobolev.fiberMap K u) =
      HilbertSobolev.fiberMap K (linearDistribution L u) := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma linearDistribution_inverse (L : E ≃L[ℝ] E) (u : 𝓢'(E,F)) :
    linearDistribution L.symm (linearDistribution L u) = u := by
  ext φ
  simp only [linearDistribution_apply]
  congr 1
  ext x
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply]

lemma memSobolevLoc_linear (n : ℕ) (L : E ≃L[ℝ] E) {U : Set E} {u : 𝓢'(E,F)}
    (hu : HilbertSobolev.MemSobolevLoc U n u) :
    HilbertSobolev.MemSobolevLoc (L.symm ⁻¹' U) n (linearDistribution L u) := by
  intro g hg hgU
  let q := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L g
  have hq : HasCompactSupport (q : E → ℂ) := hg.comp_homeomorph L.toHomeomorph
  have hqU : tsupport q ⊆ U := by
    have he : tsupport q = L ⁻¹' tsupport g := tsupport_comp_eq_preimage g L.toHomeomorph
    rw [he]
    intro x hx
    have h := hgU hx
    simpa only [mem_preimage,ContinuousLinearEquiv.symm_apply_apply] using h
  have h := memSobolev_nat_linear n L (hu q hq hqU)
  rw [linearDistribution_product] at h
  have he : SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm q = g := by
    ext x
    simp only [q,SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rwa [he] at h

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FormPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators

namespace TamingCompatibility.FormMetric
open RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {k : ℕ}

lemma pairing_smul_left (c : ℝ) (α β : E [⋀^Fin k]→L[ℝ] ℝ) :
    pairing (c • α) β = c * pairing α β := by
  simp only [pairing, map_smul, real_inner_smul_left]

end TamingCompatibility.FormMetric

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set _root_.MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.MetricForms
open MetricModel ContinuousAlternatingMap
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma pairing_smul_left (g : Metric E) {k : ℕ} (t : ℝ) (a b : Form E k) :
    pairing g (t • a) b = t * pairing g a b := by
  change FormMetric.pairing (MetricHodge.formEquiv g k (t • a)) (MetricHodge.formEquiv g k b) = _
  rw [_root_.map_smul]
  exact FormMetric.pairing_smul_left _ _ _
end TamingCompatibility.MetricForms

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_LocalCodifferential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section

namespace TamingCompatibility.MetricHodge
open MetricModel MetricForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma starThree_smul (g : Metric E) (F : MetricForms.Form E 2) (t : ℝ) (a : MetricForms.Form E 3) :
    starThree g F (t • a) = t • starThree g F a := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv,ContinuousAlternatingMap.smul_apply,starThree_apply,starThree_apply,pairing_smul_left]
  simp only [smul_eq_mul]
  ring

end TamingCompatibility.MetricHodge

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FramePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.AntiInvariantFrame
open ContinuousAlternatingMap MetricModel MetricForms MetricHodge ExteriorForms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (g : Metric E) (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → E)
  (hb : ∀ i j, g.bilinear (b i) (b j) = if i=j then 1 else 0)
  (J : E →L[ℝ] E) (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
include hdim hb h0 h1 h2 h3 hF in
lemma star_wedge_combination (ξ : E →L[ℝ] ℝ) (A B : ℝ) :
    let a := A • realPart g b + B • imagPart g b
    pairing g (starThree g F (wedgeOne ξ a)) (starThree g F (wedgeOne ξ a)) =
      pairing g (ofSubsingletonLIE (0 : Fin 1) ξ) (ofSubsingletonLIE (0 : Fin 1) ξ) * (A^2+B^2) := by
  dsimp only
  have he : wedgeOne ξ (A • realPart g b + B • imagPart g b) =
      A • wedgeOne ξ (realPart g b) + B • wedgeOne ξ (imagPart g b) := by
    change (wedgeOneBilinear (E := E) (ofSubsingletonLIE (0 : Fin 1) ξ)) _ = _
    rw [_root_.map_add,_root_.map_smul,_root_.map_smul]
    rfl
  rw [he,starThree_add,starThree_smul,starThree_smul,pairing_one_eq_sum g hdim b hb,
    pairing_one_eq_sum g hdim b hb]
  simp only [ContinuousAlternatingMap.add_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  simp_rw [star_wedge_real g hdim b hb J h0 h1 h2 h3 F hF,
    star_wedge_imag g hdim b hb J h0 h1 h2 h3 F hF]
  simp [Fin.sum_univ_succ]
  ring

include hdim hb h0 h1 h2 h3 hF in
lemma star_wedge_anti (ξ : E →L[ℝ] ℝ) (a : MetricForms.Form E 2)
    (ha : a.compContinuousLinearMap J = -a) :
    pairing g (starThree g F (wedgeOne ξ a)) (starThree g F (wedgeOne ξ a)) =
      (1/2:ℝ) * pairing g (ofSubsingletonLIE (0 : Fin 1) ξ) (ofSubsingletonLIE (0 : Fin 1) ξ) *
        pairing g a a := by
  have he := expansion g hdim b hb J h0 h1 h2 h3 a ha
  rw [he,star_wedge_combination g hdim b hb J h0 h1 h2 h3 F hF,
    pairing_combination g hdim b hb]
  ring
end TamingCompatibility.AntiInvariantFrame

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DirectionalPrincipal
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma directionalPrincipal_basis (b : OrthonormalBasis κ ℝ E) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    directionalPrincipal v g u = directionalPrincipal b (principalInBasis b v g) u := by
  unfold directionalPrincipal principalInBasis
  conv_lhs => arg 2; ext i; arg 2; ext j; arg 2; rw [derivative_basis b (v i),derivative_basis b (v j)]
  simp only [scalar_product_sum,scalar_product_smul]
  simp only [lineDerivOp_sum,lineDerivOp_smul,map_sum,
    ContinuousLinearMap.map_smul_of_tower,Finset.smul_sum,smul_smul]
  let H := fun (i j : ι) (k l : κ) => (⟪b k,v i⟫*⟪b l,v j⟫) •
    smulLeftCLM F (g i j) (∂_{b k} (∂_{b l} u))
  change (∑ i, ∑ j, ∑ k, ∑ l,H i j k l) = ∑ k, ∑ l, ∑ i, ∑ j,H i j k l
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l,H i j k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, ∑ l,H i j k l := by rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ l, ∑ j,H i j k l := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_FrozenCoefficient
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution Filter Function EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Topology ContDiff BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma frozen_principal_size_tendsto (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    Tendsto (fun r => principalCoefficientSize (F := F) n (frozenPrincipal χ hχ a ha p r))
      (𝓝 0) (𝓝 0) := by
  unfold principalCoefficientSize frozenPrincipal
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (frozenCoefficient_size_tendsto_zero n χ hχ (a i j) (ha i j) p).mul_const
        ‖secondDerivative (F := F) (n:ℝ) (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E j)‖))
  simpa only [zero_mul, Finset.sum_const_zero] using hh

lemma frozen_weak_size_tendsto
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    Tendsto (fun r => weakPrincipalCoefficientSize (F := F) (frozenPrincipal χ hχ a ha p r))
      (𝓝 0) (𝓝 0) := by
  unfold weakPrincipalCoefficientSize frozenPrincipal
  have hh := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ =>
      (frozenCoefficient_size_tendsto_zero 1 χ hχ (a i j) (ha i j) p).mul_const
        ‖secondDerivative (F := F) (-1) (stdOrthonormalBasis ℝ E i)
          (stdOrthonormalBasis ℝ E j)‖))
  simpa only [zero_mul, Finset.sum_const_zero] using hh

theorem frozen_perturbation_norm_tendsto (n : ℕ)
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    Tendsto (fun r => ‖perturbation (F := F) n (frozenPrincipal χ hχ a ha p r)‖)
      (𝓝 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := product_operator_estimate (E := E) (F := F) n
  apply squeeze_zero (fun _ => norm_nonneg _) (fun r => perturbation_norm_le n hC _)
  simpa only [mul_zero] using (frozen_principal_size_tendsto (F := F) n χ hχ a ha p).const_mul C

theorem frozen_weak_norm_tendsto
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (a : basisIndex E → basisIndex E → E → ℂ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (p : E) :
    Tendsto (fun r => ‖perturbationNegOne (F := F) (frozenPrincipal χ hχ a ha p r)‖)
      (𝓝 0) (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := productNegOne_operator_estimate (E := E) (F := F)
  apply squeeze_zero (fun _ => norm_nonneg _) (fun r => perturbationNegOne_norm_le hC _)
  simpa only [mul_zero] using (frozen_weak_size_tendsto (F := F) χ hχ a ha p).const_mul C

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalTransport
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma directionalPrincipal_linear (L : E ≃L[ℝ] E) (v : ι → E)
    (g : ι → ι → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    linearDistribution L (directionalPrincipal v g u) =
      directionalPrincipal (fun i => L (v i))
        (fun i j => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm (g i j))
        (linearDistribution L u) := by
  simp only [directionalPrincipal,map_sum,linearDistribution_product,linearDistribution_derivative]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma matrixLowerOrder_linear (A : E ≃L[ℝ] E)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    linearDistribution A (matrixLowerOrder b L v c K u) =
      matrixLowerOrder (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (b i))
        L (fun i => A (v i))
        (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (c i)) K
        (linearDistribution A u) := by
  simp only [matrixLowerOrder,map_add,map_sum,linearDistribution_product,
    linearDistribution_postcomp,linearDistribution_derivative]

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ScaledLower
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma matrixLowerOrder_sub_cutoff
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (χ : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    matrixLowerOrder b L v (Sum.elim c (fun _ : Unit => -χ))
      (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) u =
      matrixLowerOrder b L v c K u - smulLeftCLM F χ u := by
  simp only [matrixLowerOrder,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Fintype.sum_unique]
  have he : fiberMap (ContinuousLinearMap.id ℂ F) u = u := rfl
  rw [he]
  change _ + (_ + smulLeftCLM F (- (χ : E → ℂ)) u) = _
  rw [smulLeftCLM_neg χ.hasTemperateGrowth]
  simp only [_root_.neg_apply]
  abel

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_FrozenSystem
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma exists_small_frozen_scale
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p : E) :
    ∃ r : ℝ, 0 < r ∧
      ‖perturbationNegOne (F := F)
        (frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r)‖ < 1 ∧
      ‖perturbation (F := F) 0
        (frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r)‖ < 1 := by
  have h1 := (frozen_weak_norm_tendsto (F := F) χ hχ (fun i j x => -g i j x)
    (fun i j => (g i j).smooth ⊤ |>.neg) p).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have h2 := (frozen_perturbation_norm_tendsto (F := F) 0 χ hχ (fun i j x => -g i j x)
    (fun i j => (g i j).smooth ⊤ |>.neg) p).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp (h1.and h2)
  have hr := hεsub (show ε/2 ∈ Metric.ball (0 : ℝ) ε by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  exact ⟨ε/2,half_pos hε,hr⟩

lemma MemSobolevLoc.real_smul {U : Set E} {n : ℝ} {u : 𝓢'(E,F)}
    (h : MemSobolevLoc U n u) (r : ℝ) : MemSobolevLoc U n (r • u) := by
  intro g hg hgU
  rw [ContinuousLinearMap.map_smul_of_tower,RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact MemSobolev.smul (r : ℂ) (h g hg hgU)

lemma MemSobolevLoc.restrict {U V : Set E} {n : ℝ} {u : 𝓢'(E,F)}
    (h : MemSobolevLoc U n u) (hVU : V ⊆ U) : MemSobolevLoc V n u :=
  fun g hg hgV => h g hg (hgV.trans hVU)

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalNormalize
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma memSobolevLoc_linear_one (L : E ≃L[ℝ] E) {U : Set E} {u : 𝓢'(E,F)}
    (hu : MemSobolevLoc U 1 u) : MemSobolevLoc (L.symm ⁻¹' U) 1 (linearDistribution L u) := by
  have hu' : MemSobolevLoc U (1 : ℕ) u := by simpa only [Nat.cast_one] using hu
  simpa only [Nat.cast_one] using memSobolevLoc_linear 1 L hu'

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_ClosureLinear
attribute [-instance] _root_.OAI.TamingCompatibility.FormMetric.formFiniteDimensional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ClosureLinear
open Set
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma toClosure_dense (f : E →ₗ[ℝ] F) : DenseRange (toClosure f) := by
  change DenseRange (Set.inclusion (s := Set.range f) (t := closure (Set.range f))
    subset_closure ∘ Set.rangeFactorization f)
  exact ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
    rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
end TamingCompatibility.ClosureLinear

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeUniformOdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

lemma fullShiftedSquare_memSobolev (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6))
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+2) 2 u) :
    MemSobolev n 2 (fullShiftedSquare a b ρ ζ u) := by
  rw [full_shifted_square_expansion a b ρ ζ g ha]
  apply MemSobolev.add
  · apply MemSobolev.neg
    apply memSobolev_sum
    intro i _
    apply memSobolev_sum
    intro j _
    apply memSobolev_nat_product
    convert (hu.lineDerivOp (m := e j)).lineDerivOp (m := e i) using 1 <;> first | rfl | ring
  · exact matrixLowerOrder_memSobolev n _ _ _ _ _ (hu.mono (by linarith))

lemma fullShiftedSquare_commutator_memSobolev (n : ℕ)
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (M : C 6 →L[ℂ] C 6)
    {u : 𝓢'(V,C 6)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (fullShiftedSquare a b ρ ζ (fiberMap M u) -
      fiberMap M (fullShiftedSquare a b ρ ζ u)) := by
  let L := matrixLowerOrder
    (fun q : Fin 4 × Fin 6 × Fin 6 =>
      squareFirst e (fun i => coefficient (a i)) (coefficient b)
        (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b) q.1 q.2.1 q.2.2)
    (fun q => unit 6 6 q.2.1 q.2.2) (fun q => e q.1)
    (fun q : Fin 6 × Fin 6 =>
      (squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i))
        (fullWeightedAdj ρ b)+scalarMatrix 6 ζ) q.1 q.2)
    (fun q => unit 6 6 q.1 q.2)
  have he : fullShiftedSquare a b ρ ζ (fiberMap M u) -
      fiberMap M (fullShiftedSquare a b ρ ζ u) = L (fiberMap M u) - fiberMap M (L u) := by
    rw [full_shifted_square_expansion a b ρ ζ g ha,
      full_shifted_square_expansion a b ρ ζ g ha]
    simp only [map_add,map_neg,fiberMap_directionalPrincipal]
    change -_ + L _ - (-_ + fiberMap M (L _)) = _
    abel
  rw [he]
  exact (matrixLowerOrder_memSobolev n _ _ _ _ _ (MemSobolev_fiberMap hu M)).sub
    (MemSobolev_fiberMap (matrixLowerOrder_memSobolev n _ _ _ _ _ hu) M)

end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeDifferentialLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution Filter Set
open EuclideanEnergy
open scoped SchwartzMap LineDeriv Topology
variable {m : ℕ}

lemma fullShiftedSquare_cutoff_locality
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (G : Fin 4 → Fin 4 → V → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 6))
    (g h : 𝓢(V,ℂ)) (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(V,C 6)) :
    smulLeftCLM (C 6) g (fullShiftedSquare a b ρ ζ (smulLeftCLM (C 6) h u)) =
      smulLeftCLM (C 6) g (fullShiftedSquare a b ρ ζ u) := by
  rw [full_shifted_square_expansion a b ρ ζ G hG,
    full_shifted_square_expansion a b ρ ζ G hG]
  simp only [map_add,map_neg]
  rw [directionalPrincipal_locality e (fullPrincipalScalar a ρ) g h hh u,
    matrixLowerOrder_locality _ _ _ _ _ g h hh u]

end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end


