-- Prove2me | Definitions.Def_OAIQ239Tc001
-- name    : OAIQ239Tc001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T22:09:28.047705+00:00
-- url     : https://prove2.me/theorems/08d43b9c-3a3c-4cec-bc9b-dd23b3574241
-- title:
--   Definitions bundle OAIQ239Tc001 of the split of OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 140 declarations of OpenAI's Lean: 48 definitions and 92 theorems. The definitions and types are `OAI.TamingCompatibility.CompactKernel.evaluate`, `OAI.TamingCompatibility.CompactKernel.operator`, `OAI.TamingCompatibility.ComplexMatrix.C`, `OAI.TamingCompatibility.ComplexMatrix.LocallyEqual`, `OAI.TamingCompatibility.ComplexMatrix.R`, `OAI.TamingCompatibility.ComplexMatrix.antiMatrix`, `OAI.TamingCompatibility.ComplexMatrix.antiPairSelector`, `OAI.TamingCompatibility.ComplexMatrix.coefficient`, `OAI.TamingCompatibility.ComplexMatrix.componentTest`, `OAI.TamingCompatibility.ComplexMatrix.derivativeMatrix`, `OAI.TamingCompatibility.ComplexMatrix.embed`, `OAI.TamingCompatibility.ComplexMatrix.entry`, `OAI.TamingCompatibility.ComplexMatrix.entryProduct`, `OAI.TamingCompatibility.ComplexMatrix.firstOrder`, `OAI.TamingCompatibility.ComplexMatrix.formalAdjoint`, `OAI.TamingCompatibility.ComplexMatrix.fullPrincipalScalar`, `OAI.TamingCompatibility.ComplexMatrix.fullShiftedSquare`, `OAI.TamingCompatibility.ComplexMatrix.fullWeightedAdj`, `OAI.TamingCompatibility.ComplexMatrix.matProduct`, `OAI.TamingCompatibility.ComplexMatrix.multiply`, `OAI.TamingCompatibility.ComplexMatrix.principalMatrix`, `OAI.TamingCompatibility.ComplexMatrix.realComponent`, `OAI.TamingCompatibility.ComplexMatrix.retract`, `OAI.TamingCompatibility.ComplexMatrix.scalarMatrix`, `OAI.TamingCompatibility.ComplexMatrix.square`, `OAI.TamingCompatibility.ComplexMatrix.squareFirst`, `OAI.TamingCompatibility.ComplexMatrix.squareZero`, `OAI.TamingCompatibility.ComplexMatrix.unit`, `OAI.TamingCompatibility.EuclideanEnergy.S`, `OAI.TamingCompatibility.EuclideanEnergy.V`, `OAI.TamingCompatibility.EuclideanEnergy.e`, `OAI.TamingCompatibility.EuclideanGreen.helmholtz`, `OAI.TamingCompatibility.EuclideanSobolev.boundedDistribution`, `OAI.TamingCompatibility.EuclideanSobolevOperators.linearDistribution`, `OAI.TamingCompatibility.HilbertSobolev.H`, `OAI.TamingCompatibility.HilbertSobolev.MemSobolevLoc`, `OAI.TamingCompatibility.HilbertSobolev.directionalPrincipal`, `OAI.TamingCompatibility.HilbertSobolev.fiberMap`, `OAI.TamingCompatibility.HilbertSobolev.matrixLowerOrder`, `OAI.TamingCompatibility.HilbertSobolev.secondCommutator` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `TamingCompatibility_Charts_LocalFormalAdjoint`, `TamingCompatibility_Charts_SquareCutoff`, `TamingCompatibility_Currents_BoundedDistribution`, `TamingCompatibility_Currents_DistributionEvaluation`, `TamingCompatibility_DifferentialForms_ComplexMatrix`, `TamingCompatibility_DifferentialForms_ComplexReal`, `TamingCompatibility_DifferentialForms_ComplexSquare`, `TamingCompatibility_DifferentialForms_FiberMap`, `TamingCompatibility_DifferentialForms_Helmholtz`, `TamingCompatibility_DifferentialForms_PerturbationNeg`, `TamingCompatibility_DifferentialForms_SquareLower`, `TamingCompatibility_DifferentialForms_TestEvaluation`, `TamingCompatibility_DifferentialForms_TestLinear`, `TamingCompatibility_DifferentialForms_UnitaryFrame`, `TamingCompatibility_DifferentialForms_WeightedRawPairing`, `TamingCompatibility_Elliptic_ComplexScalarPrincipal`, `TamingCompatibility_Elliptic_DirectionalPrincipal`, `TamingCompatibility_Elliptic_InteriorRegularity`, `TamingCompatibility_Elliptic_LocalGarding`, `TamingCompatibility_Elliptic_MatrixH1Smooth`, `TamingCompatibility_Elliptic_MemSobolevSum`, `TamingCompatibility_Elliptic_PrincipalDerivativeError`, `TamingCompatibility_Elliptic_SquarePrincipal`, `TamingCompatibility_Functional_CompactQuadratic`, `TamingCompatibility_Functional_FourierCutoff`, `TamingCompatibility_Functional_PiCompact`, `TamingCompatibility_Functional_SobolevSpace`, `TamingCompatibility_Hodge_HodgeDifferentialLocality`, `TamingCompatibility_Hodge_HodgePairing`, `TamingCompatibility_Hodge_HodgeProjectionRaw`, `TamingCompatibility_Hodge_HodgeScalarSquare`, `TamingCompatibility_Hodge_HodgeShiftedRegularity`, `TamingCompatibility_Hodge_HodgeUniformOdd`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ239Tc005`, `OAIQ239Tc006`, `OAIQ239Tc007` and `OAIQ239Tc008`; the statement `OAI.TamingCompatibility.HilbertSobolev.linear_center_energy_two_jet`.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ239_TC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_LocalFormalAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.LocalFormalAdjoint
open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D E F : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def multiply (a : D → E →L[ℝ] F) (ha : a.HasTemperateGrowth) :
    𝓢(D,E) →L[ℝ] 𝓢(D,F) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℝ F) ha

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] [CompleteSpace E] [CompleteSpace F] in
@[simp] lemma multiply_apply (a : D → E →L[ℝ] F) (ha : a.HasTemperateGrowth)
    (u : 𝓢(D,E)) (x : D) : multiply a ha u x = a x (u x) := rfl

def adjointCoefficient (a : 𝓢(D,E →L[ℝ] F)) : 𝓢(D,F →L[ℝ] E) :=
  SchwartzMap.postcompCLM ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).toContinuousLinearEquiv.toContinuousLinearMap) a

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
@[simp] lemma adjointCoefficient_apply (a : 𝓢(D,E →L[ℝ] F)) (x : D) :
    adjointCoefficient a x = (a x).adjoint := rfl

variable {ι : Type*} [Fintype ι]

def firstOrder (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F)) (b : 𝓢(D,E →L[ℝ] F)) :
    𝓢(D,E) →L[ℝ] 𝓢(D,F) :=
  (∑ i, multiply (a i) (a i).hasTemperateGrowth ∘L
    lineDerivOpCLM ℝ 𝓢(D,E) (e i)) + multiply b b.hasTemperateGrowth

def formalAdjoint (e : ι → D) (a : ι → 𝓢(D,E →L[ℝ] F)) (b : 𝓢(D,E →L[ℝ] F)) :
    𝓢(D,F) →L[ℝ] 𝓢(D,E) :=
  -(∑ i, lineDerivOpCLM ℝ 𝓢(D,E) (e i) ∘L multiply (adjointCoefficient (a i))
    (adjointCoefficient (a i)).hasTemperateGrowth) +
    multiply (adjointCoefficient b) (adjointCoefficient b).hasTemperateGrowth

def weightedCoefficient (ρ : D → ℝ) (a : 𝓢(D,E →L[ℝ] F)) : 𝓢(D,E →L[ℝ] F) :=
  SchwartzMap.smulLeftCLM (E →L[ℝ] F) ρ a

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
  [CompleteSpace E] [CompleteSpace F] in
lemma weightedCoefficient_apply (ρ : D → ℝ) (hρ : ρ.HasTemperateGrowth)
    (a : 𝓢(D,E →L[ℝ] F)) (x : D) : weightedCoefficient ρ a x = ρ x • a x :=
  SchwartzMap.smulLeftCLM_apply_apply hρ a x

end TamingCompatibility.LocalFormalAdjoint

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_FourierCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped BoundedContinuousFunction
namespace TamingCompatibility.CompactKernel

variable {K H F : Type*} [MetricSpace K]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def evaluate (k : K →ᵇ (H →L[ℂ] F)) (u : H) : K →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => k x u)
    (k.continuous.clm_apply continuous_const) (‖k‖ * ‖u‖)
    (fun x => (k x).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg u)))

lemma norm_evaluate_le (k : K →ᵇ (H →L[ℂ] F)) (u : H) :
    ‖evaluate k u‖ ≤ ‖k‖ * ‖u‖ := by
  apply (BoundedContinuousFunction.norm_le (f := evaluate k u)
    (mul_nonneg (norm_nonneg k) (norm_nonneg u))).mpr
  intro x
  exact ((k x).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (k.norm_coe_le_norm x) (norm_nonneg u))

def operator (k : K →ᵇ (H →L[ℂ] F)) : H →L[ℂ] (K →ᵇ F) :=
  LinearMap.mkContinuous
    { toFun := evaluate k
      map_add' := fun u v => by ext x; exact (k x).map_add u v
      map_smul' := fun c u => by ext x; exact (k x).map_smul c u }
    ‖k‖ (norm_evaluate_le k)

theorem compact_operator [CompactSpace K] [ProperSpace F]
    (k : K →ᵇ (H →L[ℂ] F)) : IsCompactOperator (operator k) := by
  apply (isCompactOperator_iff_isCompact_closure_image_ball (operator k).toLinearMap
    (show (0:ℝ) < 1 by norm_num)).mpr
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:F) ‖k‖)
    (isCompact_closedBall _ _)
  · intro f x hf
    obtain ⟨u, hu, rfl⟩ := hf
    rw [Metric.mem_closedBall, dist_zero_right]
    have hu' : ‖u‖ ≤ 1 := (by simpa using hu : ‖u‖ < 1).le
    exact ((k x).le_opNorm u).trans
      ((mul_le_mul_of_nonneg_left hu' (norm_nonneg _)).trans
        (by simpa using k.norm_coe_le_norm x))
  · intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hk⟩ := Metric.continuousAt_iff.mp k.continuous.continuousAt ε hε
    refine ⟨δ,hδ,?_⟩
    intro y hy f
    obtain ⟨u,hu,hfu⟩ := f.2
    have hnu : ‖u‖ ≤ 1 := (by simpa using hu : ‖u‖ < 1).le
    rw [dist_comm]
    change dist (f.val y) (f.val x) < ε
    rw [← hfu]
    change dist (k y u) (k x u) < ε
    calc
      dist (k y u) (k x u) = ‖(k y - k x) u‖ := by rw [dist_eq_norm]; rfl
      _ ≤ ‖k y - k x‖ * ‖u‖ := (k y - k x).le_opNorm u
      _ ≤ ‖k y - k x‖ := by nlinarith [norm_nonneg (k y - k x)]
      _ < ε := by simpa only [dist_eq_norm] using hk hy

end TamingCompatibility.CompactKernel

open _root_.MeasureTheory FourierTransform
open scoped BoundedContinuousFunction RealInnerProductSpace ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_SobolevSpace
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

abbrev H (_s : ℝ) : Type _ := Lp F 2 (volume : Measure E)

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_Helmholtz
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

lemma multiplier_add {g h : E → ℂ} (hg : g.HasTemperateGrowth)
    (hh : h.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (g + h) u =
      fourierMultiplierCLM F g u + fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add hg hh,
    add_apply, FourierTransform.fourierInv_add]

lemma bessel_two (u : 𝓢'(E,F)) :
    besselPotential E F 2 u = u +
      fourierMultiplierCLM F (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) u := by
  have hs : (fun x : E => (((1 + ‖x‖^2) ^ (2 / 2 : ℝ) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ)) + (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by
    ext x
    simp
  rw [besselPotential, hs, multiplier_add (by fun_prop) (by fun_prop)]
  simp

def helmholtz (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  u - ((2 * Real.pi)^2)⁻¹ • (Δ u)

lemma bessel_two_eq_helmholtz (u : 𝓢'(E,F)) :
    besselPotential E F 2 u = helmholtz u := by
  rw [bessel_two, helmholtz, laplacian_eq_fourierMultiplierCLM, smul_smul]
  have hc : (2 * Real.pi)^2 ≠ 0 := by positivity
  rw [mul_neg, inv_mul_cancel₀ hc]
  simp [Complex.ofReal_pow]

variable [CompleteSpace F]

theorem memSobolev_helmholtz_iff (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : 𝓢'(E,F)) :
    MemSobolev s p (helmholtz u) ↔ MemSobolev (s + 2) p u := by
  rw [← bessel_two_eq_helmholtz, memSobolev_besselPotential_iff, add_comm s 2]

end TamingCompatibility.EuclideanGreen

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_MemSobolevSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.EuclideanSobolevOperators
open _root_.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap Laplacian ENNReal
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma memSobolev_sum {ι : Type*} (s : Finset ι) {t : ℝ} (f : ι → 𝓢'(E,F))
    (h : ∀ i ∈ s, MemSobolev t 2 (f i)) : MemSobolev t 2 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma memSobolev_of_laplacian {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  apply (EuclideanGreen.memSobolev_helmholtz_iff s 2 u).mp
  exact hu.sub (hd.smul _)

lemma memSobolev_succ_of_derivatives {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : ∀ i, MemSobolev s 2 (∂_{b i} u)) :
    MemSobolev (s+1) 2 u := by
  have hl : MemSobolev (s-1) 2 (Δ u) := by
    rw [TemperedDistribution.laplacian_eq_sum b]
    exact memSobolev_sum _ _ (fun i _ => (hd i).lineDerivOp)
  have hm := memSobolev_of_laplacian (hu.mono (show s-1 ≤ s by linarith)) hl
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma schwartz_derivative_product (g φ : 𝓢(E,ℂ)) (v : E) :
    ∂_{v} (SchwartzMap.smulLeftCLM ℂ g φ) =
      SchwartzMap.smulLeftCLM ℂ (∂_{v} g : 𝓢(E,ℂ)) φ +
      SchwartzMap.smulLeftCLM ℂ g (∂_{v} φ) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_apply]
  have hf : (SchwartzMap.smulLeftCLM ℂ g φ : E → ℂ) = (⇑g * ⇑φ) := by
    ext y
    simp [g.hasTemperateGrowth, smul_eq_mul]
  rw [hf, fderiv_mul g.differentiableAt φ.differentiableAt]
  simp [g.hasTemperateGrowth,
    (∂_{v} g : 𝓢(E,ℂ)).hasTemperateGrowth,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul, mul_comm, add_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

lemma distribution_derivative_product (g : 𝓢(E,ℂ)) (v : E) (u : 𝓢'(E,F)) :
    ∂_{v} (smulLeftCLM F g u) =
      smulLeftCLM F (∂_{v} g : 𝓢(E,ℂ)) u + smulLeftCLM F g (∂_{v} u) := by
  ext φ
  simp only [lineDerivOp_apply_apply, smulLeftCLM_apply_apply,
    add_apply, map_neg]
  rw [schwartz_derivative_product]
  simp only [map_add, neg_add_rev]
  abel

lemma memSobolev_zero_product (g : 𝓢(E,ℂ)) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨f,hf⟩ := hu
  have he : u = (f : 𝓢'(E,F)) := by simpa using hf
  rw [he]
  let b := g.toBoundedContinuousFunction
  let w : Lp F 2 (volume : Measure E) := ((b.memLp_top (μ := volume)).toLp b) • f
  refine ⟨w, ?_⟩
  simp only [besselPotential_zero, ContinuousLinearMap.id_apply]
  exact (Lp.toTemperedDistribution_smul_eq (g.hasTemperateGrowth) (b.memLp_top (μ := volume)) f).symm

theorem memSobolev_nat_product (n : ℕ) (g : 𝓢(E,ℂ)) {u : 𝓢'(E,F)}
    (hu : MemSobolev n 2 u) : MemSobolev n 2 (smulLeftCLM F g u) := by
  induction n generalizing g u with
  | zero =>
    simp only [Nat.cast_zero] at hu ⊢
    exact memSobolev_zero_product g hu
  | succ n ih =>
    have hu' : MemSobolev n 2 u := hu.mono (by exact_mod_cast Nat.le_succ n)
    have hp := ih g hu'
    have hd (i : Fin (Module.finrank ℝ E)) :
        MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} (smulLeftCLM F g u)) := by
      rw [distribution_derivative_product]
      have hdu : MemSobolev n 2 (∂_{stdOrthonormalBasis ℝ E i} u) := by
        convert hu.lineDerivOp using 1
        all_goals try with_reducible_and_instances rfl
        simp
      exact (ih _ hu').add (ih g hdu)
    simpa using memSobolev_succ_of_derivatives (stdOrthonormalBasis ℝ E) hp hd

end TamingCompatibility.EuclideanSobolevOperators

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_PerturbationNeg
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


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma coefficient_products_commute (g h : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (smulLeftCLM F h u) =
      smulLeftCLM F h (smulLeftCLM F g u) := by
  rw [smulLeftCLM_smulLeftCLM_apply g.hasTemperateGrowth h.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply h.hasTemperateGrowth g.hasTemperateGrowth]
  rw [mul_comm (g : E → ℂ) (h : E → ℂ)]

def secondCommutator (g : 𝓢(E,ℂ)) (v w : E) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  smulLeftCLM F (∂_{v} (∂_{w} g) : 𝓢(E,ℂ)) u +
  smulLeftCLM F (∂_{w} g : 𝓢(E,ℂ)) (∂_{v} u) +
  smulLeftCLM F (∂_{v} g : 𝓢(E,ℂ)) (∂_{w} u)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma distribution_second_product (g : 𝓢(E,ℂ)) (v w : E) (u : 𝓢'(E,F)) :
    ∂_{v} (∂_{w} (smulLeftCLM F g u)) =
      smulLeftCLM F g (∂_{v} (∂_{w} u)) + secondCommutator g v w u := by
  rw [distribution_derivative_product, LineDeriv.lineDerivOp_add,
    distribution_derivative_product, distribution_derivative_product]
  unfold secondCommutator
  abel

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_FiberMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv
section FiberMaps

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def fiberMap (L : F →L[ℂ] G) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,G) :=
  PointwiseConvergenceCLM.postcomp 𝓢(E,ℂ) L

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] [CompleteSpace G] in
lemma fiberMap_apply (L : F →L[ℂ] G) (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    fiberMap L u φ = L (u φ) := rfl

omit [CompleteSpace F] [CompleteSpace G] in
lemma fiberMap_bessel (L : F →L[ℂ] G) (s : ℝ) (u : 𝓢'(E,F)) :
    fiberMap L (besselPotential E F s u) = besselPotential E G s (fiberMap L u) := by
  ext φ
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] [CompleteSpace G] in
lemma fiberMap_derivative (L : F →L[ℂ] G) (v : E) (u : 𝓢'(E,F)) :
    fiberMap L (∂_{v} u) = ∂_{v} (fiberMap L u) := by
  ext φ
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F] [CompleteSpace G] in
lemma fiberMap_product (L : F →L[ℂ] G) (g : E → ℂ) (u : 𝓢'(E,F)) :
    fiberMap L (smulLeftCLM F g u) = smulLeftCLM G g (fiberMap L u) := by
  ext φ
  rfl

lemma fiberMap_Lp (L : F →L[ℂ] G) (u : Lp F 2 (volume : Measure E)) :
    fiberMap L (u : 𝓢'(E,F)) = (L.compLp u : 𝓢'(E,G)) := by
  ext φ
  rw [fiberMap_apply, Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  have hφ : Integrable (fun x => φ x • u x) (volume : Measure E) := by
    exact memLp_one_iff_integrable.mp ((Lp.memLp u).smul (φ.memLp 2 volume))
  rw [← L.integral_comp_comm hφ]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLp u] with x hx
  rw [hx, L.map_smul]

lemma MemSobolev_fiberMap {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u)
    (L : F →L[ℂ] G) : MemSobolev s 2 (fiberMap L u) := by
  obtain ⟨v, hv⟩ := hu
  refine ⟨L.compLp v, ?_⟩
  rw [← fiberMap_bessel, hv, fiberMap_Lp]

end FiberMaps

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def matrixLowerOrder {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  (∑ i, smulLeftCLM F (b i) (fiberMap (L i) (∂_{v i} u))) +
  ∑ k, smulLeftCLM F (c k) (fiberMap (K k) u)

lemma matrixLowerOrder_memSobolev {ι κ : Type*} [Fintype ι] [Fintype κ]
    (n : ℕ) (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    {u : 𝓢'(E,F)} (hu : MemSobolev ((n:ℝ)+1) 2 u) :
    MemSobolev n 2 (matrixLowerOrder b L v c K u) := by
  apply MemSobolev.add
  · apply memSobolev_sum
    intro i _
    apply memSobolev_nat_product
    apply MemSobolev_fiberMap
    convert hu.lineDerivOp (m := v i) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · apply memSobolev_sum
    intro k _
    exact memSobolev_nat_product n (c k)
      (MemSobolev_fiberMap (hu.mono (by linarith)) (K k))

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open EuclideanSobolevOperators HilbertSobolev TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
abbrev R (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev C (n : ℕ) := EuclideanSpace ℂ (Fin n)

def embed (n : ℕ) : R n →L[ℝ] C n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => Complex.ofRealCLM ∘L EuclideanSpace.proj i)

@[simp] lemma embed_apply (n : ℕ) (u : R n) (i : Fin n) : embed n u i = (u i : ℂ) := rfl

def unit (m n : ℕ) (i : Fin m) (j : Fin n) : C n →L[ℂ] C m :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : Fin m => ℂ) i ∘L EuclideanSpace.proj j

@[simp] lemma unit_apply (m n : ℕ) (i : Fin m) (j : Fin n) (u : C n) (k : Fin m) :
    unit m n i j u k = if k=i then u j else 0 := by simp [unit]

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

def multiply {m n : ℕ} (a : Fin m → Fin n → 𝓢(D,ℂ)) :
    𝓢'(D,C n) →L[ℂ] 𝓢'(D,C m) :=
  ∑ i, ∑ j, smulLeftCLM (C m) (a i j) ∘L fiberMap (unit m n i j)

lemma fiberMap_schwartz {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) (u : 𝓢(D,E)) :
    fiberMap L (u : 𝓢'(D,E)) = (SchwartzMap.postcompCLM L u : 𝓢'(D,F)) := by
  ext φ
  change L ((u : 𝓢'(D,E)) φ) = (SchwartzMap.postcompCLM L u : 𝓢'(D,F)) φ
  rw [SchwartzMap.coe_apply,SchwartzMap.coe_apply]
  have hi : Integrable (fun x => φ x • u x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth] using
      (SchwartzMap.smulLeftCLM E φ u).integrable
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with x
  exact L.map_smul (φ x) (u x)

lemma product_schwartz {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (a : 𝓢(D,ℂ)) (u : 𝓢(D,F)) :
    smulLeftCLM F a (u : 𝓢'(D,F)) = (SchwartzMap.smulLeftCLM F a u : 𝓢'(D,F)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [a.hasTemperateGrowth,smul_smul,mul_comm]

lemma multiply_schwartz {m n : ℕ} (a : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢(D,C n)) :
    multiply a (u : 𝓢'(D,C n)) =
      ((∑ i, ∑ j, SchwartzMap.smulLeftCLM (C m) (a i j)
        (SchwartzMap.postcompCLM (unit m n i j) u) : 𝓢(D,C m)) : 𝓢'(D,C m)) := by
  simp only [multiply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    fiberMap_schwartz,product_schwartz,map_sum]

end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_UnitaryFrame
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
namespace TamingCompatibility.UnitaryFrame

abbrev W := EuclideanSpace ℝ (Fin 6)

def jAction (a : W) : W := WithLp.toLp 2 ![a 0, a 4, -a 3, -a 2, a 1, a 5]

def antiInvariantPart (a : W) : W := (1 / 2 : ℝ) • (a - jAction a)

end TamingCompatibility.UnitaryFrame

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_LocalGarding
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
open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace

namespace TamingCompatibility.EuclideanEnergy
abbrev V := EuclideanSpace ℝ (Fin 4)
abbrev S := 𝓢(V,ℝ)
def e (i : Fin 4) : V := EuclideanSpace.single i 1

end TamingCompatibility.EuclideanEnergy

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexReal
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
namespace TamingCompatibility.ComplexMatrix
open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
def retract (n : ℕ) : C n →L[ℝ] R n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i => Complex.reCLM ∘L (EuclideanSpace.proj i).restrictScalars ℝ)

@[simp] lemma retract_apply (n : ℕ) (u : C n) (i : Fin n) : retract n u i = (u i).re := rfl
@[simp] lemma retract_embed (n : ℕ) (u : R n) : retract n (embed n u) = u := by
  ext i
  rfl

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

def entry {m n : ℕ} (i : Fin m) (j : Fin n) : (R n →L[ℝ] R m) →L[ℝ] ℝ :=
  EuclideanSpace.proj i ∘L ContinuousLinearMap.apply ℝ (R m) (EuclideanSpace.single j 1)

@[simp] lemma entry_apply {m n : ℕ} (i : Fin m) (j : Fin n) (L : R n →L[ℝ] R m) :
    entry i j L = L (EuclideanSpace.single j 1) i := rfl

def coefficient {m n : ℕ} (a : 𝓢(D,R n →L[ℝ] R m)) (i : Fin m) (j : Fin n) : 𝓢(D,ℂ) :=
  SchwartzMap.postcompCLM (Complex.ofRealCLM ∘L entry i j) a

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
@[simp] lemma coefficient_apply {m n : ℕ} (a : 𝓢(D,R n →L[ℝ] R m))
    (i : Fin m) (j : Fin n) (x : D) : coefficient a i j x = (entry i j (a x) : ℂ) := rfl

lemma real_sum_coord {ι : Type*} [Fintype ι] {n : ℕ} (f : ι → R n) (j : Fin n) :
    (∑ i, f i) j = ∑ i, f i j :=
  map_sum (EuclideanSpace.proj (𝕜 := ℝ) j) f Finset.univ
lemma complex_sum_coord {ι : Type*} [Fintype ι] {n : ℕ} (f : ι → C n) (j : Fin n) :
    (∑ i, f i) j = ∑ i, f i j :=
  map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) f Finset.univ

lemma real_matrix_apply {m n : ℕ} (a : R n →L[ℝ] R m) (u : R n) (i : Fin m) :
    ∑ j, entry i j a * u j = a u i := by
  have hu : ∑ j : Fin n, u j • EuclideanSpace.single j 1 = u := by
    simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr u
  have hh := congrArg (fun v : R n => a v i) hu
  simpa only [map_sum,map_smul,real_sum_coord,PiLp.smul_apply,smul_eq_mul,mul_comm,entry_apply] using hh

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma schwartz_matrix_embed {m n : ℕ} (a : 𝓢(D,R n →L[ℝ] R m)) (u : 𝓢(D,R n)) :
    (∑ i, ∑ j, SchwartzMap.smulLeftCLM (C m) (coefficient a i j)
      (SchwartzMap.postcompCLM (unit m n i j) (SchwartzMap.postcompCLM (embed n) u))) =
    SchwartzMap.postcompCLM (embed m) (LocalFormalAdjoint.multiply a a.hasTemperateGrowth u) := by
  ext x k
  simp only [sum_apply,complex_sum_coord,SchwartzMap.smulLeftCLM_apply
    (coefficient a _ _).hasTemperateGrowth,SchwartzMap.postcompCLM_apply,PiLp.smul_apply,
    coefficient_apply,unit_apply,embed_apply,smul_eq_mul]
  simp only [mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  simp_rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum,real_matrix_apply]
  rfl

lemma multiply_embed {m n : ℕ} (a : 𝓢(D,R n →L[ℝ] R m)) (u : 𝓢(D,R n)) :
    multiply (coefficient a) (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n)) =
      (SchwartzMap.postcompCLM (embed m) (LocalFormalAdjoint.multiply a a.hasTemperateGrowth u) :
        𝓢'(D,C m)) := by
  rw [multiply_schwartz,schwartz_matrix_embed]

end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open _root_.MeasureTheory LineDeriv TemperedDistribution
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {ι : Type*} [Fintype ι] {m n : ℕ}

def firstOrder (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m)) (b : 𝓢(D,R n →L[ℝ] R m)) :
    𝓢'(D,C n) →L[ℂ] 𝓢'(D,C m) :=
  (∑ i, multiply (coefficient (a i)) ∘L lineDerivOpCLM ℂ 𝓢'(D,C n) (e i)) + multiply (coefficient b)

def formalAdjoint (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m)) (b : 𝓢(D,R n →L[ℝ] R m)) :
    𝓢'(D,C m) →L[ℂ] 𝓢'(D,C n) :=
  -(∑ i, lineDerivOpCLM ℂ 𝓢'(D,C n) (e i) ∘L
    multiply (coefficient (LocalFormalAdjoint.adjointCoefficient (a i)))) +
    multiply (coefficient (LocalFormalAdjoint.adjointCoefficient b))

def square (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m)) (b : 𝓢(D,R n →L[ℝ] R m))
    (ρ : 𝓢(D,ℝ)) : 𝓢'(D,C n) →L[ℂ] 𝓢'(D,C n) :=
  formalAdjoint e (fun i => LocalFormalAdjoint.weightedCoefficient ρ (a i))
    (LocalFormalAdjoint.weightedCoefficient ρ b) ∘L firstOrder e a b

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma lineDeriv_embed (v : D) (u : 𝓢(D,R n)) :
    ∂_{v} (SchwartzMap.postcompCLM (embed n) u) = SchwartzMap.postcompCLM (embed n) (∂_{v} u) := by
  ext1 x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hh := (embed n).hasFDerivAt.comp x u.differentiableAt.hasFDerivAt
  change fderiv ℝ ((embed n) ∘ u) x v = _
  rw [hh.fderiv]
  rfl

lemma distribution_lineDeriv_embed (v : D) (u : 𝓢(D,R n)) :
    ∂_{v} (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n)) =
      (SchwartzMap.postcompCLM (embed n) (∂_{v} u) : 𝓢'(D,C n)) := by
  rw [TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq,lineDeriv_embed]

lemma firstOrder_embed (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m))
    (b : 𝓢(D,R n →L[ℝ] R m)) (u : 𝓢(D,R n)) :
    firstOrder e a b (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n)) =
      (SchwartzMap.postcompCLM (embed m) (LocalFormalAdjoint.firstOrder e a b u) : 𝓢'(D,C m)) := by
  simp only [firstOrder,LocalFormalAdjoint.firstOrder,_root_.add_apply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply,distribution_lineDeriv_embed,
    multiply_embed,map_add,map_sum]

lemma formalAdjoint_embed (e : ι → D) (a : ι → 𝓢(D,R n →L[ℝ] R m))
    (b : 𝓢(D,R n →L[ℝ] R m)) (u : 𝓢(D,R m)) :
    formalAdjoint e a b (SchwartzMap.postcompCLM (embed m) u : 𝓢'(D,C m)) =
      (SchwartzMap.postcompCLM (embed n) (LocalFormalAdjoint.formalAdjoint e a b u) : 𝓢'(D,C n)) := by
  simp only [formalAdjoint,LocalFormalAdjoint.formalAdjoint,_root_.add_apply,_root_.neg_apply,
    _root_.sum_apply,ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply,
    multiply_embed,distribution_lineDeriv_embed,map_add,map_neg,map_sum]

end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {m n k : ℕ}

lemma multiply_apply_component (a : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n))
    (φ : 𝓢(D,ℂ)) (i : Fin m) :
    (multiply a u φ) i = ∑ j, (u (SchwartzMap.smulLeftCLM ℂ (a i j) φ)) j := by
  simp only [multiply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    smulLeftCLM_apply_apply,fiberMap_apply,complex_sum_coord,unit_apply]
  simp [Finset.sum_ite_irrel]

lemma multiply_derivative (a : Fin m → Fin n → 𝓢(D,ℂ)) (v : D) (u : 𝓢'(D,C n)) :
    ∂_{v} (multiply a u) = multiply (fun i j => ∂_{v} (a i j)) u + multiply a (∂_{v} u) := by
  simp only [multiply,_root_.sum_apply,ContinuousLinearMap.comp_apply,
    lineDerivOp_sum,distribution_derivative_product,← fiberMap_derivative,Finset.sum_add_distrib]

lemma multiply_add (a b : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (fun i j => a i j + b i j) u = multiply a u + multiply b u := by
  ext φ i
  simp only [_root_.add_apply,multiply_apply_component,PiLp.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : SchwartzMap.smulLeftCLM ℂ (a i j+b i j) φ =
      SchwartzMap.smulLeftCLM ℂ (a i j) φ + SchwartzMap.smulLeftCLM ℂ (b i j) φ := by
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply (a i j+b i j).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply (a i j).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply (b i j).hasTemperateGrowth,_root_.add_apply,add_smul]
  rw [he,map_add]
  rfl

lemma multiply_sum {ι : Type*} [Fintype ι] (a : ι → Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (fun i j => ∑ t, a t i j) u = ∑ t, multiply (a t) u := by
  classical
  let P (s : Finset ι) : Prop := multiply (fun i j => ∑ t ∈ s, a t i j) u = ∑ t ∈ s, multiply (a t) u
  have hp : ∀ s, P s := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      dsimp only [P]
      simp only [Finset.sum_empty]
      ext φ i
      have h0 : SchwartzMap.smulLeftCLM ℂ (0 : 𝓢(D,ℂ)) φ = 0 := by
        ext x
        rw [SchwartzMap.smulLeftCLM_apply_apply (0 : 𝓢(D,ℂ)).hasTemperateGrowth]
        simp only [_root_.zero_apply,zero_smul]
      simp only [multiply_apply_component,h0,map_zero,PiLp.zero_apply,Finset.sum_const_zero,
        _root_.zero_apply]
    | @insert t s ht ih =>
      dsimp only [P] at ih ⊢
      simp only [Finset.sum_insert ht,multiply_add,ih]
  exact hp Finset.univ

def entryProduct (f g : 𝓢(D,ℂ)) : 𝓢(D,ℂ) := SchwartzMap.smulLeftCLM ℂ f g

lemma entryProduct_apply (f g : 𝓢(D,ℂ)) (x : D) : entryProduct f g x = f x * g x :=
  SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth g x

lemma entryProduct_test (f g φ : 𝓢(D,ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (entryProduct f g) φ =
      SchwartzMap.smulLeftCLM ℂ g (SchwartzMap.smulLeftCLM ℂ f φ) := by
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply (entryProduct f g).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,entryProduct_apply,smul_eq_mul]
  ring

def matProduct (b : Fin k → Fin m → 𝓢(D,ℂ)) (a : Fin m → Fin n → 𝓢(D,ℂ)) :
    Fin k → Fin n → 𝓢(D,ℂ) := fun i l => ∑ j, entryProduct (b i j) (a j l)

lemma multiply_comp (b : Fin k → Fin m → 𝓢(D,ℂ)) (a : Fin m → Fin n → 𝓢(D,ℂ))
    (u : 𝓢'(D,C n)) : multiply b (multiply a u) = multiply (matProduct b a) u := by
  change multiply b (multiply a u) = multiply (fun i l => ∑ j, entryProduct (b i j) (a j l)) u
  rw [multiply_sum]
  ext φ i
  simp only [multiply_apply_component,_root_.sum_apply,complex_sum_coord,entryProduct_test]

end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_ComplexSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} [Fintype ι] {m n : ℕ}

lemma multiply_neg (a : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (fun i j => -a i j) u = -multiply a u := by
  ext φ i
  simp only [multiply_apply_component,_root_.neg_apply,PiLp.neg_apply,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : SchwartzMap.smulLeftCLM ℂ (-a i j) φ = -SchwartzMap.smulLeftCLM ℂ (a i j) φ := by
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply (-a i j).hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply_apply (a i j).hasTemperateGrowth,_root_.neg_apply,neg_smul]
  rw [he,map_neg]
  rfl

lemma multiply_sub (a b : Fin m → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (fun i j => a i j-b i j) u = multiply a u-multiply b u := by
  simp only [sub_eq_add_neg,multiply_add,multiply_neg]

def derivativeMatrix (v : D) (a : Fin m → Fin n → 𝓢(D,ℂ)) :
    Fin m → Fin n → 𝓢(D,ℂ) := fun i j => ∂_{v} (a i j)

def squareFirst (e : ι → D) (a : ι → Fin m → Fin n → 𝓢(D,ℂ))
    (b : Fin m → Fin n → 𝓢(D,ℂ)) (c : ι → Fin n → Fin m → 𝓢(D,ℂ))
    (d : Fin n → Fin m → 𝓢(D,ℂ)) (j : ι) : Fin n → Fin n → 𝓢(D,ℂ) :=
  fun k l => matProduct d (a j) k l -
    (∑ i, derivativeMatrix (e i) (matProduct (c i) (a j)) k l) - matProduct (c j) b k l

def squareZero (e : ι → D) (b : Fin m → Fin n → 𝓢(D,ℂ))
    (c : ι → Fin n → Fin m → 𝓢(D,ℂ)) (d : Fin n → Fin m → 𝓢(D,ℂ)) :
    Fin n → Fin n → 𝓢(D,ℂ) :=
  fun k l => matProduct d b k l - ∑ i, derivativeMatrix (e i) (matProduct (c i) b) k l

lemma divergence_square_expansion (e : ι → D) (a : ι → Fin m → Fin n → 𝓢(D,ℂ))
    (b : Fin m → Fin n → 𝓢(D,ℂ)) (c : ι → Fin n → Fin m → 𝓢(D,ℂ))
    (d : Fin n → Fin m → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    -(∑ i, ∂_{e i} (multiply (c i) ((∑ j, multiply (a j) (∂_{e j} u)) + multiply b u))) +
      multiply d ((∑ j, multiply (a j) (∂_{e j} u)) + multiply b u) =
    -(∑ i, ∑ j, multiply (matProduct (c i) (a j)) (∂_{e i} (∂_{e j} u))) +
      (∑ j, multiply (squareFirst e a b c d j) (∂_{e j} u)) + multiply (squareZero e b c d) u := by
  unfold squareFirst squareZero derivativeMatrix
  simp only [map_add,map_sum,multiply_comp,lineDerivOp_add,lineDerivOp_sum,multiply_derivative,
    multiply_sub,multiply_sum,
    Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => multiply (fun k l => ∂_{e i} (matProduct (c i) (a j) k l)) (∂_{e j} u))]
  abel

end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_PrincipalDerivativeError
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
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators
open scoped SchwartzMap ENNReal LineDeriv Laplacian FourierTransform
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma distribution_derivatives_commute (v w : E) (u : 𝓢'(E,F)) :
    ∂_{v} (∂_{w} u) = ∂_{w} (∂_{v} u) := by
  apply (FourierTransform.fourierEquiv ℂ 𝓢'(E,F)).injective
  change 𝓕 (∂_{v} (∂_{w} u)) = 𝓕 (∂_{w} (∂_{v} u))
  simp only [fourier_lineDerivOp_eq, map_smul]
  congr 2
  rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
  rw [mul_comm]

end TamingCompatibility.HilbertSobolev

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_ComplexScalarPrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} [Fintype ι] {m n k : ℕ}

lemma matProduct_coefficient_apply (b : 𝓢(D,R m →L[ℝ] R k))
    (a : 𝓢(D,R n →L[ℝ] R m)) (i : Fin k) (j : Fin n) (x : D) :
    matProduct (coefficient b) (coefficient a) i j x =
      (entry i j (b x ∘L a x) : ℂ) := by
  simp only [matProduct,_root_.sum_apply,entryProduct_apply,coefficient_apply,
    ← Complex.ofReal_mul,← Complex.ofReal_sum]
  congr 1
  exact real_matrix_apply (b x) (a x (EuclideanSpace.single j 1)) i

lemma schwartz_zero_product (φ : 𝓢(D,ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (0 : 𝓢(D,ℂ)) φ = 0 := by
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply (0 : 𝓢(D,ℂ)).hasTemperateGrowth]
  simp only [_root_.zero_apply,zero_smul]

def scalarMatrix (n : ℕ) (q : 𝓢(D,ℂ)) : Fin n → Fin n → 𝓢(D,ℂ) :=
  fun i j => if i=j then q else 0

lemma multiply_scalarMatrix (q : 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    multiply (scalarMatrix n q) u = smulLeftCLM (C n) q u := by
  ext φ i
  rw [multiply_apply_component,smulLeftCLM_apply_apply]
  rw [Finset.sum_eq_single i]
  · simp only [scalarMatrix,ite_true, if_true]
  · intro j _ hji
    simp only [scalarMatrix,ite_eq_right (Ne.symm hji),schwartz_zero_product,map_zero,PiLp.zero_apply]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

variable [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]

lemma symmetrized_principal (e : ι → D)
    (a : ι → ι → Fin n → Fin n → 𝓢(D,ℂ)) (g : ι → ι → 𝓢(D,ℂ))
    (ha : ∀ i j k l, a i j k l + a j i k l = scalarMatrix n (g i j + g i j) k l)
    (u : 𝓢'(D,C n)) :
    (∑ i, ∑ j, multiply (a i j) (∂_{e i} (∂_{e j} u))) =
      ∑ i, ∑ j, smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u)) := by
  let S := ∑ i, ∑ j, multiply (a i j) (∂_{e i} (∂_{e j} u))
  have hs : S = ∑ i, ∑ j, multiply (a j i) (∂_{e i} (∂_{e j} u)) := by
    dsimp only [S]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [distribution_derivatives_commute (e i) (e j)]
  have hm (i j : ι) :
      multiply (a i j) (∂_{e i} (∂_{e j} u)) + multiply (a j i) (∂_{e i} (∂_{e j} u)) =
      smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u)) +
        smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u)) := by
    rw [← multiply_add]
    have he : (fun k l => a i j k l + a j i k l) = scalarMatrix n (g i j + g i j) :=
      funext fun k => funext fun l => ha i j k l
    rw [he,multiply_scalarMatrix]
    ext φ k
    simp only [smulLeftCLM_apply_apply,_root_.add_apply,PiLp.add_apply]
    have hf : SchwartzMap.smulLeftCLM ℂ (g i j+g i j) φ =
        SchwartzMap.smulLeftCLM ℂ (g i j) φ + SchwartzMap.smulLeftCLM ℂ (g i j) φ := by
      ext x
      simp only [SchwartzMap.smulLeftCLM_apply_apply (g i j+g i j).hasTemperateGrowth,
        SchwartzMap.smulLeftCLM_apply_apply (g i j).hasTemperateGrowth,_root_.add_apply,add_smul]
    rw [hf,map_add]
    rfl
  have hsum : S+S =
      (∑ i, ∑ j, smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u))) +
      (∑ i, ∑ j, smulLeftCLM (C n) (g i j) (∂_{e i} (∂_{e j} u))) := by
    calc
      S+S = S+(∑ i, ∑ j, multiply (a j i) (∂_{e i} (∂_{e j} u))) :=
        congrArg (fun v => S+v) hs
      _ = _ := by
        dsimp only [S]
        simp_rw [← Finset.sum_add_distrib,hm]
  have he := congrArg (fun v : 𝓢'(D,C n) => (1/2:ℂ) • v) hsum
  simpa only [← two_smul ℂ,smul_smul,div_mul_cancel₀ _ (by norm_num : (2:ℂ) ≠ 0),one_smul] using he

end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_SquarePrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} {m n : ℕ}

def principalMatrix (a : ι → 𝓢(D,R n →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (i j : ι) : Fin n → Fin n → 𝓢(D,ℂ) :=
  matProduct (coefficient (LocalFormalAdjoint.adjointCoefficient
    (LocalFormalAdjoint.weightedCoefficient ρ (a i)))) (coefficient (a j))

lemma principalMatrix_apply (a : ι → 𝓢(D,R n →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (i j : ι) (k l : Fin n) (x : D) :
    principalMatrix a ρ i j k l x =
      (entry k l ((ρ x • a i x).adjoint ∘L a j x) : ℂ) := by
  rw [principalMatrix,matProduct_coefficient_apply,LocalFormalAdjoint.adjointCoefficient_apply,
    LocalFormalAdjoint.weightedCoefficient_apply ρ ρ.hasTemperateGrowth]

lemma entry_polarized {S T : R n →L[ℝ] R n} {q : ℝ}
    (h : S+T = q • ContinuousLinearMap.id ℝ (R n)) (k l : Fin n) :
    entry k l S + entry k l T = q * (if k=l then 1 else 0) := by
  rw [← (entry k l).map_add,h,(entry k l).map_smul]
  congr 1
  simp only [entry_apply,ContinuousLinearMap.id_apply,PiLp.single_apply]

end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_SquareLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma entries_lowerOrder (e : ι → D) (b : ι → Fin n → Fin n → 𝓢(D,ℂ))
    (c : Fin n → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    (∑ i, multiply (b i) (∂_{e i} u)) + multiply c u =
      matrixLowerOrder (fun q : ι × Fin n × Fin n => b q.1 q.2.1 q.2.2)
        (fun q => unit n n q.2.1 q.2.2) (fun q => e q.1)
        (fun q : Fin n × Fin n => c q.1 q.2) (fun q => unit n n q.1 q.2) u := by
  simp only [matrixLowerOrder,Fintype.sum_prod_type,multiply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply]

end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_DirectionalPrincipal
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

def directionalPrincipal (v : ι → E) (g : ι → ι → 𝓢(E,ℂ)) (u : 𝓢'(E,F)) : 𝓢'(E,F) :=
  ∑ i, ∑ j,smulLeftCLM F (g i j) (∂_{v i} (∂_{v j} u))

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_BoundedDistribution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory FourierTransform
open scoped SchwartzMap BoundedContinuousFunction RealInnerProductSpace
namespace TamingCompatibility.EuclideanSobolev
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def boundedDistribution (g : E →ᵇ F) : 𝓢'(E,F) :=
  ((g.memLp_top (μ := volume)).toLp g : Lp F ⊤ volume)

lemma boundedDistribution_apply (g : E →ᵇ F) (φ : 𝓢(E,ℂ)) :
    boundedDistribution g φ = ∫ x, φ x • g x := by
  rw [boundedDistribution, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [g.memLp_top.coeFn_toLp] with x hx
  rw [hx]

end TamingCompatibility.EuclideanSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_MatrixH1Smooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.HilbertSobolev
open _root_.MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology
section Locality
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma cutoff_product_eq (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) : (g : E → ℂ) * h = g := by
  funext x
  by_cases hx : x ∈ tsupport g
  · simp [hh x hx |>.eq_of_nhds]
  · simp [image_eq_zero_of_notMem_tsupport hx]

lemma cutoff_derivative_product_zero (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v : E) :
    (g : E → ℂ) * (∂_{v} h : 𝓢(E,ℂ)) = 0 := by
  funext x
  by_cases hx : x ∈ tsupport g
  · have hd := (hh x hx).lineDeriv_eq (𝕜 := ℝ) (v := v)
    simpa only [SchwartzMap.lineDerivOp_apply, lineDeriv, deriv_const, Pi.mul_apply,
      Pi.zero_apply, mul_zero] using congrArg (g x * ·) hd
  · simp [image_eq_zero_of_notMem_tsupport hx]

lemma cutoff_second_product_zero (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v w : E) :
    (g : E → ℂ) * (∂_{v} (∂_{w} h) : 𝓢(E,ℂ)) = 0 := by
  funext x
  by_cases hx : x ∈ tsupport g
  · have hdh : (fun y => (∂_{w} h : 𝓢(E,ℂ)) y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(hh x hx).eventuallyEq_nhds] with y hy
      simpa only [SchwartzMap.lineDerivOp_apply, lineDeriv, deriv_const] using hy.lineDeriv_eq (𝕜 := ℝ) (v := w)
    have hd := hdh.lineDeriv_eq (𝕜 := ℝ) (v := v)
    simpa only [SchwartzMap.lineDerivOp_apply, lineDeriv, deriv_const, Pi.mul_apply,
      Pi.zero_apply, mul_zero] using congrArg (g x * ·) hd
  · simp [image_eq_zero_of_notMem_tsupport hx]

lemma cutoff_mul_cutoff (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (smulLeftCLM F h u) = smulLeftCLM F g u := by
  rw [smulLeftCLM_smulLeftCLM_apply h.hasTemperateGrowth g.hasTemperateGrowth,
    mul_comm (h : E → ℂ), cutoff_product_eq g h hh]

lemma cutoff_mul_derivative (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v : E) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (smulLeftCLM F (∂_{v} h : 𝓢(E,ℂ)) u) = 0 := by
  rw [smulLeftCLM_smulLeftCLM_apply (∂_{v} h : 𝓢(E,ℂ)).hasTemperateGrowth
    g.hasTemperateGrowth, mul_comm,
    cutoff_derivative_product_zero g h hh v]
  change smulLeftCLM F (fun _ => 0) u = 0
  simp

lemma cutoff_mul_second (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v w : E) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (smulLeftCLM F (∂_{v} (∂_{w} h) : 𝓢(E,ℂ)) u) = 0 := by
  rw [smulLeftCLM_smulLeftCLM_apply (∂_{v} (∂_{w} h) : 𝓢(E,ℂ)).hasTemperateGrowth
    g.hasTemperateGrowth, mul_comm,
    cutoff_second_product_zero g h hh v w]
  change smulLeftCLM F (fun _ => 0) u = 0
  simp

lemma cutoff_secondCommutator_zero (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (v w : E) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (secondCommutator h v w u) = 0 := by
  simp only [secondCommutator, map_add, cutoff_mul_second g h hh,
    cutoff_mul_derivative g h hh, add_zero]

end Locality

end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Charts_SquareCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution Filter
open scoped SchwartzMap LineDeriv Topology
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma directionalPrincipal_locality {ι : Type*} [Fintype ι]
    (v : ι → E) (a : ι → ι → 𝓢(E,ℂ)) (g h : 𝓢(E,ℂ))
    (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F g (directionalPrincipal v a (smulLeftCLM F h u)) =
      smulLeftCLM F g (directionalPrincipal v a u) := by
  simp only [directionalPrincipal,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [coefficient_products_commute g (a i j),distribution_second_product,map_add,
    cutoff_mul_cutoff g h hh,cutoff_secondCommutator_zero g h hh,add_zero]
  exact coefficient_products_commute (a i j) g _
end TamingCompatibility.HilbertSobolev

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Currents_DistributionEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open scoped SchwartzMap
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m n : ℕ}
lemma continuous_system_eval (L : E →L[ℝ] 𝓢'(D,C n))
    (P : 𝓢'(D,C n) →L[ℂ] 𝓢'(D,C m)) (φ : 𝓢(D,ℂ)) (i : Fin m) :
    Continuous (fun w => (P (L w) φ) i) := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp
    ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) (C m) φ).continuous.comp
      (P.continuous.comp L.continuous))
end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TestEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D]
variable {n m : ℕ} {ι : Type*} [Fintype ι]

def componentTest (j : Fin n) (φ : 𝓢(D,ℝ)) : 𝓢(D,R n) :=
  SchwartzMap.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j 1)) φ

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
@[simp] lemma componentTest_apply (j : Fin n) (φ : 𝓢(D,ℝ)) (x : D) :
    componentTest j φ x = φ x • EuclideanSpace.single j 1 := rfl

omit [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] in
lemma componentTest_inner (j : Fin n) (φ : 𝓢(D,ℝ)) (u : R n) (x : D) :
    ⟪u,componentTest j φ x⟫ = φ x * u j := by
  rw [componentTest_apply,real_inner_smul_right]
  rw [EuclideanSpace.inner_single_right]
  simp

lemma embedded_distribution_apply (u : 𝓢(D,R n)) (φ : 𝓢(D,ℝ)) :
    (SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ) = embed n (∫ x, φ x • u x) := by
  rw [SchwartzMap.coe_apply]
  have hi : Integrable (fun x => φ x • u x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth] using
      (SchwartzMap.smulLeftCLM (R n) φ u).integrable (μ := volume)
  rw [← ContinuousLinearMap.integral_comp_comm (embed n) hi]
  apply integral_congr_ae
  filter_upwards [] with x
  ext j
  simp [embed_apply]

lemma embedded_component_apply (u : 𝓢(D,R n)) (φ : 𝓢(D,ℝ)) (j : Fin n) :
    ((SchwartzMap.postcompCLM (embed n) u : 𝓢'(D,C n))
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j =
      ((∫ x, ⟪u x,componentTest j φ x⟫ : ℝ) : ℂ) := by
  rw [embedded_distribution_apply,embed_apply]
  congr 1
  have hi : Integrable (fun x => φ x • u x) := by
    simpa only [SchwartzMap.smulLeftCLM_apply φ.hasTemperateGrowth] using
      (SchwartzMap.smulLeftCLM (R n) φ u).integrable (μ := volume)
  change EuclideanSpace.proj j (∫ x, φ x • u x) = _
  rw [← ContinuousLinearMap.integral_comp_comm _ hi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [componentTest_inner]
  rfl

end TamingCompatibility.ComplexMatrix

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_CompactQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.CompactQuadratic
open Set
variable {Y V : Type*} [TopologicalSpace Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem lower_bound {K : Set Y} (hK : IsCompact K)
    (Q : Y → V →L[ℝ] V →L[ℝ] ℝ) (hQ : ContinuousOn Q K)
    (hpos : ∀ x ∈ K, ∀ v : V, v ≠ 0 → 0 < Q x v v) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ v : V, ‖v‖^2 ≤ C * Q x v v := by
  have hc : IsCompact (K ×ˢ Metric.sphere (0 : V) 1) :=
    hK.prod (isCompact_sphere 0 1)
  have hcont : ContinuousOn (fun xv : Y × V => Q xv.1 xv.2 xv.2)
      (K ×ˢ Metric.sphere (0 : V) 1) :=
    ((hQ.comp continuous_fst.continuousOn (fun _ h => h.1)).clm_apply
      continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  by_cases he : (K ×ˢ Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn he hcont
    have hzNorm : ‖z.2‖ = 1 := by simpa using hz.2
    have hm : 0 < Q z.1 z.2 z.2 := hpos z.1 hz.1 z.2 (by
      intro h; simp only [h,norm_zero] at hzNorm <;> linarith)
    refine ⟨(Q z.1 z.2 z.2)⁻¹,inv_pos.mpr hm,?_⟩
    intro x hx v
    by_cases hv : v=0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have heval : Q x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = Q x v v / ‖v‖^2 := by
      simp only [map_smul,smul_apply,smul_eq_mul]
      ring
    have hmin' := hmin (show (x,‖v‖⁻¹ • v) ∈ K ×ˢ Metric.sphere (0 : V) 1 from ⟨hx,hu⟩)
    change Q z.1 z.2 z.2 ≤ Q x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) at hmin'
    rw [heval] at hmin'
    have hl := (le_div_iff₀ (sq_pos_of_pos hn)).mp hmin'
    calc ‖v‖^2 ≤ Q x v v / Q z.1 z.2 z.2 := (le_div_iff₀ hm).mpr (by nlinarith)
         _ = (Q z.1 z.2 z.2)⁻¹ * Q x v v := by ring
  · refine ⟨1,by norm_num,?_⟩
    intro x hx v
    have hv : v=0 := by
      by_contra hv
      have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
      apply he
      refine ⟨(x,‖v‖⁻¹ • v),hx,?_⟩
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    simp [hv]
end TamingCompatibility.CompactQuadratic

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Functional_PiCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open _root_.MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.CompactPi
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} {F : ι → Type*}
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]

lemma pi_compact (f : ∀ i, E →L[ℝ] F i) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (ContinuousLinearMap.pi f) := by
  classical
  choose K hK hsub using (fun i => (hf i).image_closedBall_subset_compact 1)
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (ContinuousLinearMap.pi f).toLinearMap zero_lt_one).2
  refine ⟨{x | ∀ i, x i ∈ K i}, isCompact_pi_infinite hK, ?_⟩
  rintro _ ⟨x,hx,rfl⟩ i
  exact hsub i ⟨x,hx,rfl⟩

end TamingCompatibility.CompactPi

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_TestLinear
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

namespace TamingCompatibility.ComplexMatrix
open Set
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def realComponent {n : ℕ} (q : 𝓢(E,R n)) (j : Fin n) : 𝓢(E,ℝ) :=
  SchwartzMap.postcompCLM (EuclideanSpace.proj j) q
@[simp] lemma realComponent_apply {n : ℕ} (q : 𝓢(E,R n)) (j : Fin n) (x : E) :
    realComponent q j x = q x j := rfl
end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_DifferentialForms_WeightedRawPairing
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
namespace TamingCompatibility.ComplexMatrix
open _root_.MeasureTheory
open scoped SchwartzMap RealInnerProductSpace BoundedContinuousFunction
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] {n : ℕ}

lemma bounded_real_component (g : D →ᵇ C n) (φ : 𝓢(D,ℝ)) (j : Fin n) :
    ((EuclideanSobolev.boundedDistribution g
      (SchwartzMap.postcompCLM Complex.ofRealCLM φ)) j).re =
      ∫ x, φ x * (g x j).re := by
  rw [EuclideanSobolev.boundedDistribution_apply]
  let L : C n →L[ℝ] ℝ := Complex.reCLM ∘L (EuclideanSpace.proj j).restrictScalars ℝ
  have hi : Integrable (fun x => (SchwartzMap.postcompCLM Complex.ofRealCLM φ) x • g x) :=
    (SchwartzMap.postcompCLM Complex.ofRealCLM φ).integrable.smul_of_top_left g.memLp_top
  change L (∫ x, (SchwartzMap.postcompCLM Complex.ofRealCLM φ) x • g x) = _
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [L]

end TamingCompatibility.ComplexMatrix

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Elliptic_InteriorRegularity
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

def MemSobolevLoc (U : Set E) (s : ℝ) (u : 𝓢'(E,F)) : Prop :=
  ∀ g : 𝓢(E,ℂ), HasCompactSupport (g : E → ℂ) → tsupport g ⊆ U →
    MemSobolev s 2 (smulLeftCLM F g u)

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

def linearDistribution (L : E ≃L[ℝ] E) : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L)

end TamingCompatibility.EuclideanSobolevOperators

end
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeScalarSquare
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
open scoped SchwartzMap LineDeriv RealInnerProductSpace
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} {m : ℕ}
def fullPrincipalScalar (a : ι → 𝓢(D,R 6 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (i j : ι) : 𝓢(D,ℂ) :=
  (1/2:ℂ) • (principalMatrix a ρ i j 0 0 + principalMatrix a ρ j i 0 0)

lemma fullPrincipalScalar_apply (a : ι → 𝓢(D,R 6 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (i j : ι) (x : D) :
    fullPrincipalScalar a ρ i j x = (g i j x : ℂ) := by
  have he := entry_polarized (h i j x) (0 : Fin 6) (0 : Fin 6)
  simp only [ite_true, if_true,mul_one] at he
  simp only [fullPrincipalScalar,_root_.smul_apply,_root_.add_apply,principalMatrix_apply,
    smul_eq_mul,← Complex.ofReal_add,he,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

lemma fullPrincipalMatrix_scalar (a : ι → 𝓢(D,R 6 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ))
    (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (i j : ι) (k l : Fin 6) :
    principalMatrix a ρ i j k l + principalMatrix a ρ j i k l =
      scalarMatrix 6 (fullPrincipalScalar a ρ i j + fullPrincipalScalar a ρ i j) k l := by
  ext x
  have he := entry_polarized (h i j x) k l
  simp only [_root_.add_apply,principalMatrix_apply,← Complex.ofReal_add]
  rw [show entry k l ((ρ x • a i x).adjoint ∘L a j x) +
    entry k l ((ρ x • a j x).adjoint ∘L a i x) = (2*g i j x)*(if k=l then 1 else 0) from he]
  by_cases hkl : k=l
  · simp only [scalarMatrix,ite_eq_left hkl,_root_.add_apply,fullPrincipalScalar_apply a ρ g h,
      mul_one,Complex.ofReal_mul,Complex.ofReal_ofNat]
    ring
  · simp only [scalarMatrix,ite_eq_right hkl,_root_.zero_apply,mul_zero,Complex.ofReal_zero]

variable [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] [Fintype ι]
def fullWeightedAdj (ρ : 𝓢(D,ℝ)) (a : 𝓢(D,R 6 →L[ℝ] R m)) :
    Fin 6 → Fin m → 𝓢(D,ℂ) :=
  coefficient (LocalFormalAdjoint.adjointCoefficient (LocalFormalAdjoint.weightedCoefficient ρ a))

lemma full_square_scalar_expansion (e : ι → D) (a : ι → 𝓢(D,R 6 →L[ℝ] R m))
    (b : 𝓢(D,R 6 →L[ℝ] R m)) (ρ : 𝓢(D,ℝ)) (g : ι → ι → D → ℝ)
    (h : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (u : 𝓢'(D,C 6)) :
    square e a b ρ u =
      -(∑ i, ∑ j, smulLeftCLM (C 6) (fullPrincipalScalar a ρ i j) (∂_{e i} (∂_{e j} u))) +
      (∑ j, multiply (squareFirst e (fun i => coefficient (a i)) (coefficient b)
        (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b) j) (∂_{e j} u)) +
      multiply (squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)) u := by
  simp only [square,formalAdjoint,firstOrder,_root_.add_apply,_root_.neg_apply,
    _root_.sum_apply,ContinuousLinearMap.comp_apply,lineDerivOpCLM_apply]
  rw [divergence_square_expansion]
  have hp := symmetrized_principal e (principalMatrix a ρ) (fullPrincipalScalar a ρ)
    (fullPrincipalMatrix_scalar a ρ g h) u
  simp only [principalMatrix] at hp
  rw [hp]
  rfl

end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeShiftedRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution _root_.MeasureTheory LineDeriv
open EuclideanEnergy Set
open scoped SchwartzMap LineDeriv
variable {m : ℕ}

def fullShiftedSquare (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m))
    (b : 𝓢(V,R 6 →L[ℝ] R m)) (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) :
    𝓢'(V,C 6) →L[ℂ] 𝓢'(V,C 6) := square e a b ρ + smulLeftCLM (C 6) ζ

lemma full_shifted_square_expansion (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m))
    (b : 𝓢(V,R 6 →L[ℝ] R m)) (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ))
    (g : Fin 4 → Fin 4 → V → ℝ)
    (ha : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*g i j x) • ContinuousLinearMap.id ℝ (R 6)) (u : 𝓢'(V,C 6)) :
    fullShiftedSquare a b ρ ζ u =
      -directionalPrincipal e (fullPrincipalScalar a ρ) u +
      matrixLowerOrder
        (fun q : Fin 4 × Fin 6 × Fin 6 =>
          squareFirst e (fun i => coefficient (a i)) (coefficient b)
            (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b) q.1 q.2.1 q.2.2)
        (fun q => unit 6 6 q.2.1 q.2.2) (fun q => e q.1)
        (fun q : Fin 6 × Fin 6 =>
          (squareZero e (coefficient b) (fun i => fullWeightedAdj ρ (a i))
            (fullWeightedAdj ρ b)+scalarMatrix 6 ζ) q.1 q.2)
        (fun q => unit 6 6 q.1 q.2) u := by
  rw [← entries_lowerOrder]
  have hm := multiply_add (squareZero e (coefficient b)
    (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)) (scalarMatrix 6 ζ) u
  rw [multiply_scalarMatrix] at hm
  change multiply (squareZero e (coefficient b)
    (fun i => fullWeightedAdj ρ (a i)) (fullWeightedAdj ρ b)+scalarMatrix 6 ζ) u = _ at hm
  rw [hm]
  change square e a b ρ u + smulLeftCLM (C 6) ζ u = _
  rw [full_square_scalar_expansion e a b ρ g ha]
  simp only [directionalPrincipal,add_assoc]

end TamingCompatibility.ComplexMatrix

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

lemma fiberMap_directionalPrincipal (M : C 6 →L[ℂ] C 6)
    (g : Fin 4 → Fin 4 → 𝓢(V,ℂ)) (u : 𝓢'(V,C 6)) :
    fiberMap M (directionalPrincipal e g u) = directionalPrincipal e g (fiberMap M u) := by
  simp only [directionalPrincipal,map_sum,fiberMap_product,fiberMap_derivative]

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

def LocallyEqual (U : Set V) (u v : 𝓢'(V,C 6)) : Prop :=
  ∀ χ : 𝓢(V,ℂ), HasCompactSupport (χ : V → ℂ) → tsupport χ ⊆ U →
    smulLeftCLM (C 6) χ u = smulLeftCLM (C 6) χ v

lemma LocallyEqual.refl (U : Set V) (u : 𝓢'(V,C 6)) : LocallyEqual U u u :=
  fun _ _ _ => rfl

lemma LocallyEqual.trans {U : Set V} {u v w : 𝓢'(V,C 6)}
    (h : LocallyEqual U u v) (h' : LocallyEqual U v w) : LocallyEqual U u w :=
  fun χ hc hχ => (h χ hc hχ).trans (h' χ hc hχ)

lemma LocallyEqual.sub {U : Set V} {u v w z : 𝓢'(V,C 6)}
    (h : LocallyEqual U u v) (h' : LocallyEqual U w z) : LocallyEqual U (u-w) (v-z) := by
  intro χ hc hχ
  rw [map_sub,map_sub,h χ hc hχ,h' χ hc hχ]

lemma LocallyEqual.fiberMap {U : Set V} {u v : 𝓢'(V,C 6)}
    (h : LocallyEqual U u v) (M : C 6 →L[ℂ] C 6) :
    LocallyEqual U (fiberMap M u) (fiberMap M v) := by
  intro χ hc hχ
  rw [← fiberMap_product,← fiberMap_product,h χ hc hχ]

end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility
open scoped SchwartzMap
namespace ComplexMatrix

def antiMatrix : C 6 →L[ℂ] C 6 :=
  (1/2:ℂ) • (ContinuousLinearMap.id ℂ _ -
    (unit 6 6 0 0 + unit 6 6 1 4 - unit 6 6 2 3 - unit 6 6 3 2 + unit 6 6 4 1 + unit 6 6 5 5))

lemma antiMatrix_embed (v : R 6) :
    antiMatrix (embed 6 v) = embed 6 (UnitaryFrame.antiInvariantPart v) := by
  ext i
  fin_cases i <;> simp [antiMatrix,unit_apply,UnitaryFrame.antiInvariantPart,
    UnitaryFrame.jAction,embed_apply] <;> ring
end ComplexMatrix

end TamingCompatibility

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgePairing
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

def antiPairSelector : C 6 →L[ℂ] C 2 := unit 2 6 0 1 + unit 2 6 1 2
end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeProjectionRaw
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
open TemperedDistribution Set EuclideanEnergy
open scoped SchwartzMap
lemma LocallyEqual.cutoff_self {U : Set V} (ψ : 𝓢(V,ℂ))
    (hψ : ∀ z ∈ U, ψ z = 1) (u : 𝓢'(V,C 6)) :
    LocallyEqual U (smulLeftCLM (C 6) ψ u) u := by
  intro χ _ hc
  rw [smulLeftCLM_smulLeftCLM_apply ψ.hasTemperateGrowth χ.hasTemperateGrowth]
  have he : (ψ : V → ℂ) * χ = (χ : V → ℂ) := by
    ext z
    change ψ z * χ z = χ z
    by_cases hz : z ∈ tsupport χ
    · rw [hψ z (hc hz),one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]
  rw [he]
end TamingCompatibility.ComplexMatrix

end
end

end
end

end OAI
end


