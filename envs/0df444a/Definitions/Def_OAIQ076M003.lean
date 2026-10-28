-- Prove2me | Definitions.Def_OAIQ076M003
-- name    : OAIQ076M003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:00:12.656792+00:00
-- url     : https://prove2.me/theorems/9b408c90-9d37-4cff-a4c4-d392014a8f9d
-- title:
--   Definitions bundle OAIQ076M003 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 365 declarations of OpenAI's Lean: 137 definitions, 8 inductive types or structures, 8 instances and 212 theorems. The definitions and types are `OAI.MinUncut.CubeRows.Other`, `OAI.MinUncut.CubeRows.boolSplitEquiv`, `OAI.MinUncut.CubeRows.cubeExpectation`, `OAI.MinUncut.CubeRows.face`, `OAI.MinUncut.CubeRows.join`, `OAI.MinUncut.CubeRows.rowI`, `OAI.MinUncut.CubeRows.rowJ`, `OAI.MinUncut.CubeRows.splitEquiv`, `OAI.MinUncut.CubeRows.squareProduct`, `OAI.MinUncut.CubeRows.vertex`, `OAI.MinUncut.Enumeration`, `OAI.MinUncut.Enumeration.image`, `OAI.MinUncut.Enumeration.ofList`, `OAI.MinUncut.Enumeration.sigma`, `OAI.MinUncut.Enumeration.subtype`, `OAI.MinUncut.FiniteGaussian.GridData`, `OAI.MinUncut.FiniteGaussian.GridData.Check`, `OAI.MinUncut.FiniteGaussian.GridData.select`, `OAI.MinUncut.FiniteGaussian.algebraicNonneg`, `OAI.MinUncut.FiniteGaussian.coefficient`, `OAI.MinUncut.FiniteGaussian.densityPolynomial`, `OAI.MinUncut.FiniteGaussian.disagreement`, `OAI.MinUncut.FiniteGaussian.error`, `OAI.MinUncut.FiniteGaussian.evenExp`, `OAI.MinUncut.FiniteGaussian.primitive`, `OAI.MinUncut.FiniteGaussian.qError`, `OAI.MinUncut.FiniteGaussian.qIntegral`, `OAI.MinUncut.FiniteProof.Folded`, `OAI.MinUncut.FiniteProof.Query`, `OAI.MinUncut.FiniteProof.QueryDemand`, `OAI.MinUncut.FiniteProof.QueryDemand.failure`, `OAI.MinUncut.FiniteProof.UnitDemand`, `OAI.MinUncut.FiniteProof.Variable`, `OAI.MinUncut.FiniteProof.answer`, `OAI.MinUncut.FiniteProof.multiplicity`, `OAI.MinUncut.FiniteProof.orient`, `OAI.MinUncut.FiniteProof.rep`, `OAI.MinUncut.FiniteProof.vertex`, `OAI.MinUncut.GaussianBudget.Coordinates`, `OAI.MinUncut.GaussianBudget.liftVector` and 105 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_GaussianDistance`, `MinUncut_Analysis_GaussianQuadrature`, `MinUncut_Analysis_GaussianSmallBall`, `MinUncut_Analysis_Gradient`, `MinUncut_Analysis_HermiteComponent`, `MinUncut_Analysis_RationalRowNoise`, `MinUncut_Analysis_SmoothingRho`, `MinUncut_Estimates_AlgebraicSigns`, `MinUncut_Estimates_Assembly`, `MinUncut_Estimates_Away`, `MinUncut_Estimates_Basic`, `MinUncut_Estimates_Bridge`, `MinUncut_Estimates_CoefficientMoments`, `MinUncut_Estimates_ComparisonSoundness`, `MinUncut_Estimates_Convolution`, `MinUncut_Estimates_Density`, `MinUncut_Estimates_EraseAway`, `MinUncut_Estimates_EuclideanInvariantScore`, `MinUncut_Estimates_ExpectResampleRow`, `MinUncut_Estimates_F2`, `MinUncut_Estimates_FaceUpdateSelf`, `MinUncut_Estimates_InnerAssembly`, `MinUncut_Estimates_InnerUniform`, `MinUncut_Estimates_IntegralExpect`, `MinUncut_Estimates_LiftedVectors`, `MinUncut_Estimates_ListDecoding`, `MinUncut_Estimates_MemLpMaskProject`, `MinUncut_Estimates_Rest`, `MinUncut_Estimates_TableTestFunctions`, `MinUncut_Estimates_UniformEquationOutput`, `MinUncut_Estimates_WeightedTestLaw`, `MinUncut_Games_Basic`, `MinUncut_Games_HintSections`, `MinUncut_Games_HintSimulation`, `MinUncut_Games_HintSoundness`, `MinUncut_Games_JointHintSampling`, `MinUncut_Games_Pinsker`, `MinUncut_Games_Sampling`, `MinUncut_Graphs_GraphOutput`, `MinUncut_Graphs_SignedGraph`, `MinUncut_Graphs_VertexInjective`, `MinUncut_Machines_AlphabetBudget`, `MinUncut_PCP_CayleySpectral`, `MinUncut_PCP_CompletedSampling`, `MinUncut_PCP_Completion`, `MinUncut_PCP_DistributionMaps`, `MinUncut_PCP_FinalBooleanVerifier`, `MinUncut_PCP_Overlap`, `MinUncut_PCP_ProfileCorrection`, `MinUncut_PCP_RawInitialTables`, `MinUncut_PCP_SelectedInformation`, `MinUncut_PCP_SelectedMarginal`, `MinUncut_PCP_SelectionSequence`, `MinUncut_Search_ArithmeticTactic`, `MinUncut_Search_FiniteEnumeration`, `MinUncut_Search_OuterParameters`, `MinUncut_Search_ParameterFields`, `MinUncut_Search_Parameters`, `MinUncut_Search_RationalBasics`, `MinUncut_Search_RationalDenominatorArithmetic`, `MinUncut_Search_RationalInner`, `MinUncut_Search_RawRationalArithmetic`, `MinUncut_Search_UniformFiniteSum`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M006`, `OAIQ076M007`, `OAIQ076M008`, `OAIQ076M009`, `OAIQ076M010`, `OAIQ076M011`, `OAIQ076M012` and `OAIQ076M013`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ076_MU.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite

lemma integrable_poly_density (p : ℝ[X]) :
    Integrable (fun x => p.eval x * gaussianPDFReal 0 1 x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [eval_add, add_mul] using hp.fun_add hq
  | monomial n a =>
    have hn := integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
      (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n) : (-1:ℝ) < (n:ℝ))
    have heq : (fun x : ℝ => (monomial n a).eval x * gaussianPDFReal 0 1 x) =
      fun x : ℝ => (a * (Real.sqrt (2 * Real.pi))⁻¹) *
        (x^(n:ℝ) * Real.exp (-(1/2) * x^2)) := by
      funext x
      simp only [eval_monomial, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero,
        Real.rpow_natCast]
      rw [show -x^2 / (2:ℝ) = -(1/2) * x^2 by ring]
      ring
    rw [heq]
    exact hn.const_mul _

lemma density_derivative (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h : HasDerivAt (fun x : ℝ => Real.exp (-(x^2/2)))
      (-x * Real.exp (-(x^2/2))) x := by
    convert (((hasDerivAt_id x).pow 2).div_const 2).neg.exp using 1 <;>
      simp only [id_eq, Pi.pow_apply, Pi.neg_apply]
    ring
  have heq : gaussianPDFReal 0 1 = fun x : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x^2/2)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, neg_div]
  rw [heq]
  apply (h.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)).congr_deriv
  ring

lemma measure_eq_of_moments {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : integrableExpSet id μ = Set.univ) (hν : integrableExpSet id ν = Set.univ)
    (hm : ∀ n : ℕ, (∫ x, x^n ∂μ) = ∫ x, x^n ∂ν) : μ = ν := by
  have haμ : AnalyticOnNhd ℂ (complexMGF id μ) Set.univ := by
    intro z _
    exact analyticAt_complexMGF (by simp [hμ])
  have haν : AnalyticOnNhd ℂ (complexMGF id ν) Set.univ := by
    intro z _
    exact analyticAt_complexMGF (by simp [hν])
  let d := fun z => complexMGF id μ z - complexMGF id ν z
  have hd : AnalyticAt ℂ d 0 := (haμ 0 (Set.mem_univ _)).sub (haν 0 (Set.mem_univ _))
  have hdn (n : ℕ) : iteratedDeriv n d 0 = 0 := by
    rw [show d = fun z => complexMGF id μ z - complexMGF id ν z from rfl,
      iteratedDeriv_fun_sub (haμ 0 (Set.mem_univ _)).contDiffAt
        (haν 0 (Set.mem_univ _)).contDiffAt,
      iteratedDeriv_complexMGF (by simp [hμ]), iteratedDeriv_complexMGF (by simp [hν])]
    simp only [zero_mul, Complex.exp_zero, mul_one, id_eq]
    rw [show (fun x : ℝ => (x:ℂ)^n) = fun x : ℝ => ((x^n:ℝ):ℂ) by ext x; simp,
      integral_complex_ofReal, integral_complex_ofReal, hm n]
    simp
  have ht : analyticOrderAt d (0:ℂ) = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd).mpr (fun i _ => hdn i)
  have he : complexMGF id μ =ᶠ[𝓝 (0:ℂ)] complexMGF id ν := by
    filter_upwards [analyticOrderAt_eq_top.mp ht] with z hz
    exact sub_eq_zero.mp hz
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  exact haμ.eqOn_of_preconnected_of_eventuallyEq haν isPreconnected_univ (Set.mem_univ 0) he
    (Set.mem_univ z)

lemma memLp_positivePart {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    MemLp (fun x => max (f x) 0) 2 μ := by
  apply hf.mono ((hf.aestronglyMeasurable.aemeasurable.max aemeasurable_const).aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Real.norm_eq_abs, abs_of_nonneg (le_max_right (f x) (0:ℝ))]
  exact max_le (le_abs_self _) (abs_nonneg _)

lemma weighted_finite {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {w : Ω → ℝ} (hw : MemLp w 2 μ) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (w x))) :=
  isFiniteMeasure_withDensity (hw.integrable (by norm_num)).lintegral_lt_top.ne

lemma integral_weighted {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {w : Ω → ℝ} (hw : MemLp w 2 μ) (hwn : ∀ x, 0 ≤ w x)
    (q : Ω → ℝ) :
    (∫ x, q x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = ∫ x, w x * q x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (hwn _), smul_eq_mul]

lemma sqrt_factorial_pos (n : ℕ) : 0 < Real.sqrt (n.factorial : ℝ) := by
  positivity

lemma integral_inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp only [hfω, hgω, RCLike.inner_apply, conj_trivial, mul_comm]

section Product
variable {ι : Type*} [Fintype ι]

def polyProdMap : MultilinearMap ℝ (fun _ : ι => ℝ[X]) ((ι → ℝ) → ℝ) :=
  (MultilinearMap.mkPiAlgebra ℝ ι ((ι → ℝ) → ℝ)).compLinearMap (fun i =>
    { toFun := fun p x => p.eval (x i)
      map_add' := by intros; ext x; simp
      map_smul' := by intros; ext x; simp })

lemma polyProdMap_apply (p : ι → ℝ[X]) (x : ι → ℝ) :
    polyProdMap p x = ∏ i, (p i).eval (x i) := by
  simp [polyProdMap, MultilinearMap.mkPiAlgebra_apply]

def linearPoly [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i

lemma eval_linearPoly [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (linearPoly L) = L x := by
  simp only [linearPoly, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  rw [show Pi.single i (x i) = x i • Pi.single i (1:ℝ) by
      simpa only [smul_eq_mul, mul_one] using (Pi.single_smul (f := fun _ : ι => ℝ) i (x i) (1:ℝ))]
  simp [mul_comm]

end Product

def affinePoly (r s : ℝ) : ℝ[X] := C r + C s * X
@[simp] lemma eval_affinePoly (r s x : ℝ) : (affinePoly r s).eval x = r+s*x := by
  simp [affinePoly]
@[simp] lemma derivative_affinePoly (r s : ℝ) : (affinePoly r s).derivative = C s := by
  simp [affinePoly]

variable {ι : Type*} [Fintype ι]

def rotation (ρ s : ℝ) : ((ι → ℝ) × (ι → ℝ)) →L[ℝ] ((ι → ℝ) × (ι → ℝ)) :=
  (ρ • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) +
    s • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)).prod
  (s • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) -
    ρ • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))

omit [Fintype ι] in
@[simp] lemma rotation_apply (ρ s : ℝ) (x : (ι → ℝ) × (ι → ℝ)) :
    rotation ρ s x = (ρ • x.1 + s • x.2, s • x.1 - ρ • x.2) := rfl

omit [Fintype ι] in
lemma rotation_involutive (ρ s : ℝ) (h : ρ^2+s^2=1) :
    Function.Involutive (rotation (ι := ι) ρ s) := by
  intro x
  ext i <;> simp only [rotation_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · calc
      _ = (ρ^2+s^2)*x.1 i := by ring
      _ = x.1 i := by rw [h, one_mul]
  · calc
      _ = (ρ^2+s^2)*x.2 i := by ring
      _ = x.2 i := by rw [h, one_mul]

lemma sqrt_factorial_succ (n : ℕ) :
    Real.sqrt ((n+1).factorial : ℝ) = Real.sqrt (n+1:ℝ)*Real.sqrt (n.factorial : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.sqrt_mul (by positivity)]

def bump [DecidableEq ι] (i : ι) (a : ι → ℕ) : ι → ℕ := Function.update a i (a i+1)

omit [Fintype ι] in
lemma bump_injective [DecidableEq ι] (i : ι) : Function.Injective (bump i : (ι → ℕ) → _) := by
  intro a b h
  funext j
  by_cases hj : j=i
  · subst j
    have heq := congrFun h i
    simpa [bump] using heq
  · simpa [bump, Function.update_of_ne hj] using congrFun h j

end MinUncut.GaussianHermite
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_Gradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma mem_range_bump [DecidableEq ι] (i : ι) (a : ι → ℕ) :
    a ∈ Set.range (bump i) ↔ 0 < a i := by
  constructor
  · rintro ⟨b,rfl⟩
    simp [bump]
  · intro ha
    refine ⟨Function.update a i (a i-1), ?_⟩
    funext j
    by_cases hj : j=i
    · subst j
      simp only [bump, Function.update_self]
      omega
    · simp [bump, Function.update_of_ne hj]

lemma exists_cutoff {ρ ε : ℝ} (hρ : |ρ| < 1) (hε : 0 < ε) :
    ∃ d : ℕ, ∀ k : ℕ, d+2 ≤ k → (k:ℝ)*ρ^(2*k) ≤ ε := by
  have hh : ρ^2 < 1 := by nlinarith [sq_abs ρ, abs_nonneg ρ]
  have ht := tendsto_self_mul_const_pow_of_lt_one (sq_nonneg ρ) hh
  obtain ⟨d, hd⟩ := (eventually_atTop.1 (ht.eventually (gt_mem_nhds hε)))
  refine ⟨d, fun k hk => ?_⟩
  have he := hd k (by omega)
  simpa only [pow_mul] using he.le

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_F2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace MinUncut.GaussianSmoothing

lemma integral_inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp [hfω, hgω, mul_comm]

lemma integral_bessel {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hXX : ∀ i j, (∫ ω, X i ω * X j ω ∂μ) = if i = j then 1 else 0)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∑ i, (∫ ω, X i ω * f ω ∂μ)^2) ≤ ∫ ω, (f ω)^2 ∂μ := by
  have hon : Orthonormal ℝ (fun i => (hX i).toLp (X i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [integral_inner_toLp]
    exact hXX i j
  have h := hon.sum_inner_products_le (s := Finset.univ) (hf.toLp f)
  have hnorm : ‖hf.toLp f‖ ^ 2 = ∫ ω, (f ω)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, integral_inner_toLp]
    simp [sq]
  simpa only [integral_inner_toLp, Real.norm_eq_abs, sq_abs, hnorm, Finset.mem_univ,
    Finset.sum_ite_irrel, ite_true] using h

end MinUncut.GaussianSmoothing

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology

namespace MinUncut.RowNoise
variable {R W : Type*}
  [Fintype R]
  [DecidableEq R]
  [Fintype W]
  [DecidableEq W]
  [AddCommGroup W]

lemma expect_prod {A : R → Type*} [∀ r, Fintype (A r)] (f : ∀ r, A r → ℝ) :
    (𝔼 x : ∀ r, A r, ∏ r, f r (x r)) = ∏ r, 𝔼 a, f r a := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi]
  rw [← Fintype.prod_sum, Nat.cast_prod, Finset.prod_div_distrib]

lemma geometric_bernoulli {a : ℝ} (_ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    (1-a)^k*(1+(k:ℝ)*a) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1-a)^k := pow_nonneg (by linarith) _
    have hh : (1-a)*(1+((k:ℝ)+1)*a) ≤ 1+(k:ℝ)*a := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)+1) (sq_nonneg a)]
    calc
      _ = (1-a)^k*((1-a)*(1+((k:ℝ)+1)*a)) := by rw [pow_succ]; push_cast; ring
      _ ≤ (1-a)^k*(1+(k:ℝ)*a) := mul_le_mul_of_nonneg_left hh hp
      _ ≤ 1 := ih

lemma spectral_weight_ge_one {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (k : ℕ) (hk : 1 ≤ (k:ℝ)*a) : 1 ≤ 2*(1-(1-a)^k) := by
  have hp := pow_nonneg (by linarith : 0 ≤ 1-a) k
  have hb := geometric_bernoulli ha ha1 k
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_SmoothingRho
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def smoothingRho (σ : ℝ) : ℝ := (Real.sqrt (1+σ^2))⁻¹
lemma smoothingRho_pos (σ : ℝ) : 0 < smoothingRho σ := by
  unfold smoothingRho
  positivity
lemma smoothingRho_rotation (σ : ℝ) :
    (smoothingRho σ)^2+(σ*smoothingRho σ)^2=1 := by
  have hs : (Real.sqrt (1+σ^2))^2 = 1+σ^2 := Real.sq_sqrt (by positivity)
  have hn : Real.sqrt (1+σ^2) ≠ 0 := ne_of_gt (by positivity)
  unfold smoothingRho
  field_simp
  nlinarith
lemma smoothingRho_lt_one {σ : ℝ} (hσ : σ ≠ 0) : |smoothingRho σ| < 1 := by
  rw [abs_of_pos (smoothingRho_pos σ)]
  unfold smoothingRho
  apply (inv_lt_one₀ (by positivity : 0 < Real.sqrt (1+σ^2))).2
  have he := Real.sq_sqrt (by positivity : 0 ≤ 1+σ^2)
  nlinarith [Real.sqrt_nonneg (1+σ^2), sq_pos_of_ne_zero hσ]
end MinUncut.GaussianHermite

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
namespace MinUncut.OuterSmoothness

lemma expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (f : ∀ i, A i → ℝ) :
    (𝔼 x : ∀ i, A i, ∏ i, f i (x i)) = ∏ i, 𝔼 a, f i a := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi]
  rw [← Fintype.prod_sum, Nat.cast_prod, Finset.prod_div_distrib]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

namespace JointForms
abbrev F₂ := ZMod 2

end JointForms
end MinUncut.OuterSmoothness

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Rest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open scoped BigOperators
variable {R W : Type*}
  [Fintype R]
  [DecidableEq R]
  [Fintype W]
  [DecidableEq W]
  [AddCommGroup W]

def restMask (r : R) (S : Finset R) : Finset {t : R // t≠r} :=
  Finset.univ.filter (fun t => t.val∈S)

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_IntegralExpect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianHermite
open MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma integral_norm_mul_le_sqrt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, |f x| * |g x| ∂μ) ≤ Real.sqrt (∫ x, f x^2 ∂μ) * Real.sqrt (∫ x, g x^2 ∂μ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num : (2:ℝ).HolderConjugate 2)
    (by simpa using hf) (by simpa using hg)
  simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using h

end MinUncut.GaussianHermite

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_HermiteComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
variable {R W ι : Type*}
  [DecidableEq R]
  [Fintype W]
  [AddCommGroup W]
  [Fintype ι]

lemma memLp_expect {T Ω : Type*} [Fintype T] [MeasurableSpace Ω] {μ : Measure Ω}
    (f : T → Ω → ℝ) (hf : ∀ t, MemLp (f t) 2 μ) :
    MemLp (fun x => 𝔼 t, f t x) 2 μ := by
  simp only [Finset.expect_eq_sum_div_card, div_eq_mul_inv]
  exact (memLp_finsetSum _ (fun t _ => hf t)).mul_const _

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_MemLpMaskProject
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
variable {R W ι : Type*}
  [Fintype R]
  [DecidableEq R]
  [Fintype W]
  [DecidableEq W]
  [AddCommGroup W]
  [Fintype ι]

lemma expect_sqrt_le {T : Type*} [Fintype T] [Nonempty T] (f : T → ℝ) (hf : ∀ t, 0 ≤ f t) :
    (𝔼 t, Real.sqrt (f t)) ≤ Real.sqrt (𝔼 t, f t) := by
  let g := fun t => Real.sqrt (f t)
  have hz := Finset.expect_nonneg (s := Finset.univ) (f := fun t => (g t - (𝔼 u, g u))^2)
    (fun _ _ => sq_nonneg _)
  have hg2 : ∀ t, g t ^ 2 = f t := fun t => Real.sq_sqrt (hf t)
  have hid : (𝔼 t, (g t - (𝔼 u, g u))^2) = (𝔼 t, f t) - (𝔼 t, g t)^2 := by
    simp only [sub_sq, hg2,
      Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.expect_mul,
      ← Finset.mul_expect, Fintype.expect_const]
    ring
  rw [hid] at hz
  exact (Real.le_sqrt (Finset.expect_nonneg (fun t _ => show 0≤g t from Real.sqrt_nonneg _)) (Finset.expect_nonneg (fun t _ => hf t))).2 (by linarith)
end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_EuclideanInvariantScore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianKernel

lemma euclidean_invariant_score {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (v : E) {f : E → ℝ} (hf : Measurable f)
    (hi : ∀ x (t : ℝ), f (x+t • v) = f x) :
    (∫ x, ⟪v,x⟫ * f x ∂stdGaussian E) = 0 := by
  let R := Submodule.reflection (ℝ ∙ v)ᗮ
  have hp : MeasurePreserving R (stdGaussian E) (stdGaussian E) :=
    ⟨by fun_prop, stdGaussian_map R⟩
  have hr (x : E) : f (R x) = f x := by
    have hh : R x = x + (-2*(⟪v,x⟫/‖v‖^2)) • v := by
      simp only [R, Submodule.reflection_orthogonal_apply,
        Submodule.reflection_singleton_apply]
      module
    rw [hh, hi]
  have hs (x : E) : ⟪v,R x⟫ = -⟪v,x⟫ := by
    have hh := R.inner_map_map v (R x)
    simpa only [R, Submodule.reflection_reflection,
      Submodule.reflection_orthogonalComplement_singleton_eq_neg, inner_neg_left] using hh.symm
  have he := integral_map (μ := stdGaussian E) (f := fun x => ⟪v,x⟫ * f x)
    hp.measurable.aemeasurable
    ((measurable_const.inner measurable_id).mul hf).aestronglyMeasurable
  rw [hp.map_eq] at he
  simp_rw [hr, hs, neg_mul, integral_neg] at he
  linarith

lemma invariant_score {ι : Type*} [Fintype ι] (v : ι → ℝ)
    {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (hi : ∀ x (t : ℝ), f (x+t • v) = f x) :
    (∫ x, (∑ i, v i*x i)*f x ∂Measure.pi (fun _ : ι => gaussianReal 0 1))=0 := by
  have h := euclidean_invariant_score (E := EuclideanSpace ℝ ι) (toLp 2 v)
    (f := fun x => f (ofLp x)) (hf.comp (by fun_prop)) (by
      intro x t
      exact hi (ofLp x) t)
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)] at h
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, RCLike.star_def,
    conj_trivial, Pi.star_apply, star_trivial, PiLp.toLp_apply, ofLp_toLp, mul_comm] using h

lemma coupled_score {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (i : ι) (a : κ → ℝ) {f : (ι → ℝ) × (κ → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ u, |f u| ≤ 1)
    (hi : ∀ g l (t : ℝ), f (g+t • Pi.single i 1, l-t • a) = f (g,l)) :
    (∫ g, ∫ l, g i*f (g,l) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ∑ z, a z*(∫ g, ∫ l, l z*f (g,l) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  let μ : Measure (ι → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let ν : Measure (κ → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
  let v : ι ⊕ κ → ℝ := Sum.elim (Pi.single i (1 : ℝ) : ι → ℝ) (-a)
  have he : MeasurePreserving e.symm (μ.prod ν)
      (Measure.pi (fun _ : ι ⊕ κ => gaussianReal 0 1)) :=
    measurePreserving_sumPiEquivProdPi_symm (X := fun _ : ι ⊕ κ => ℝ)
      (fun _ => gaussianReal 0 1)
  have hh := invariant_score v (f := fun u => f (e u)) (hf.comp e.measurable)
    (by
      intro u t
      change f ((fun j => u (.inl j)+t*(Pi.single i (1 : ℝ) : ι → ℝ) j),
        fun z => u (.inr z)+t*(-a z)) = f ((fun j => u (.inl j)), fun z => u (.inr z))
      convert hi (fun j => u (.inl j)) (fun z => u (.inr z)) t using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext z <;> simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg])
  rw [← he.integral_comp e.symm.measurableEmbedding] at hh
  have hg : Integrable (fun u : (ι → ℝ) × (κ → ℝ) => u.1 i*f u) (μ.prod ν) :=
    ((integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable
      (by norm_num))).comp_fst ν).mul_bdd hf.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hb u)
  have hl (z : κ) : Integrable (fun u : (ι → ℝ) × (κ → ℝ) => u.2 z*f u) (μ.prod ν) :=
    ((integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable
      (by norm_num))).comp_snd μ).mul_bdd hf.aestronglyMeasurable
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hb u)
  have hval (u : (ι → ℝ) × (κ → ℝ)) :
      (∑ j, v j * (e.symm u) j)*f (e (e.symm u)) =
        u.1 i*f u - ∑ z, a z*(u.2 z*f u) := by
    simp only [e.apply_symm_apply, Fintype.sum_sum_type, v, Sum.elim_inl, Sum.elim_inr]
    change ((∑ j, (Pi.single i (1 : ℝ) : ι → ℝ) j*u.1 j)+(∑ z, (-a z)*u.2 z))*f u = _
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, neg_mul, Finset.sum_neg_distrib]
    rw [add_mul, neg_mul, Finset.sum_mul]
    simp only [mul_assoc, sub_eq_add_neg]
  simp_rw [hval] at hh
  rw [integral_sub hg (integrable_finsetSum _ (fun z _ => (hl z).const_mul (a z))),
    integral_finsetSum _ (fun z _ => (hl z).const_mul (a z))] at hh
  simp_rw [integral_const_mul] at hh
  have hx := sub_eq_zero.mp hh
  rw [integral_prod _ hg] at hx
  simp_rw [integral_prod _ (hl _)] at hx
  exact hx


open MeasureTheory ProbabilityTheory

lemma scalar_abs_mean_le_one : (∫ t : ℝ, |t| ∂gaussianReal 0 1) ≤ 1 := by
  have h1 : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have h2 : Integrable (fun t : ℝ => t^2) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  have hm : (∫ t : ℝ, t^2 ∂gaussianReal 0 1) = 1 := by
    have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    simpa [variance_id_gaussianReal, integral_id_gaussianReal] using h.symm
  calc
    _ ≤ ∫ t : ℝ, (t^2+1)/2 ∂gaussianReal 0 1 := by
      apply integral_mono h1.abs ((h2.add (integrable_const 1)).div_const 2)
      intro t
      change |t| ≤ (t^2+1)/2
      nlinarith [sq_nonneg (|t|-1), sq_abs t]
    _ = 1 := by rw [integral_div, integral_add h2 (integrable_const 1), hm]; norm_num

lemma bounded_scalar_score {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ t, |f t| ≤ 1) :
    |∫ t : ℝ, t*f t ∂gaussianReal 0 1| ≤ 1 := by
  have ht : Integrable (fun t : ℝ => t) (gaussianReal 0 1) := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)
  have hint := ht.mul_bdd hf.aestronglyMeasurable
    (ae_of_all _ fun t => by simpa only [Real.norm_eq_abs] using hb t)
  calc
    _ ≤ ∫ t : ℝ, |t*f t| ∂gaussianReal 0 1 := abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, |t| ∂gaussianReal 0 1 := by
      apply integral_mono hint.abs ht.abs
      intro t
      change |t*f t| ≤ |t|
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (abs_nonneg t)).trans_eq (mul_one _)
    _ ≤ 1 := scalar_abs_mean_le_one

end MinUncut.GaussianKernel

namespace MinUncut.GaussianKernel
open MeasureTheory ProbabilityTheory GaussianSmoothing
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def thresholdTable (T : ι → ℝ) (η : ℝ) (l : ι → ℝ) : ι → Bool :=
  fun z => decide (0 ≤ T z + η*l z)

def tableSensitivity (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) (l : ι → ℝ) : ℝ :=
  if H (Function.update (thresholdTable T η l) z true) =
      H (Function.update (thresholdTable T η l) z false) then 0 else 1

omit [Fintype ι] in
lemma tableSensitivity_abs_le (H : (ι → Bool) → ℝ) (T : ι → ℝ) (η : ℝ) (z : ι) (l : ι → ℝ) :
    |tableSensitivity H T η z l| ≤ 1 := by unfold tableSensitivity; split <;> norm_num

omit [Fintype ι] in
lemma equal_forced_value (H : (ι → Bool) → ℝ) (P : ι → Bool) (z : ι)
    (he : H (Function.update P z true) = H (Function.update P z false)) :
    H P = H (Function.update P z true) := by
  cases hb : P z
  · calc H P = H (Function.update P z false) := by rw [← hb, Function.update_eq_self]
         _ = _ := he.symm
  · rw [← hb, Function.update_eq_self]

end MinUncut.GaussianKernel

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FaceUpdateSelf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.IndependentSquares
variable {C W : Type*}
  [Fintype C]
  [DecidableEq C]
  [Fintype W]
  [DecidableEq W]
  [AddCommGroup W]

lemma expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (f : ∀ i, A i → ℝ) :
    (𝔼 x : ∀ i, A i, ∏ i, f i (x i)) = ∏ i, 𝔼 a, f i a := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi]
  rw [← Fintype.prod_sum, Nat.cast_prod, Finset.prod_div_distrib]

end MinUncut.IndependentSquares

namespace MinUncut.Slice
open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma tail_probability {q : Ω → ℝ} (hq : Integrable q μ) (hqpos : ∀ x, 0 ≤ q x)
    {γ : ℝ} (hγ : 0 < γ) : μ.real {x | γ < q x} ≤ (∫ x, q x ∂μ)/γ := by
  have h := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hqpos) hq γ
  have hm : μ.real {x | γ < q x} ≤ μ.real {x | γ ≤ q x} :=
    measureReal_mono (fun x hx => (show γ < q x from hx).le)
  rw [le_div_iff₀ hγ]
  nlinarith

lemma integral_tail_loss {ν q : Ω → ℝ} (hν : MemLp ν 2 μ)
    (hq : Measurable q) (hqi : Integrable q μ) (hqpos : ∀ x, 0 ≤ q x)
    {γ : ℝ} (hγ : 0 < γ) :
    (∫ x in {x | γ < q x}, |ν x| ∂μ) ≤
      Real.sqrt (∫ x, (ν x)^2 ∂μ) * Real.sqrt ((∫ x, q x ∂μ)/γ) := by
  let S := {x | γ < q x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hq
  have hg : MemLp (S.indicator (fun _ => (1:ℝ))) 2 μ :=
    (memLp_const (1:ℝ)).indicator hS
  have h := GaussianHermite.integral_norm_mul_le_sqrt hν hg
  have hl : (∫ x, |ν x| * |S.indicator (fun _ => (1:ℝ)) x| ∂μ) = ∫ x in S, |ν x| ∂μ := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by by_cases hx : x ∈ S <;> simp [hx])
  have hr : (∫ x, (S.indicator (fun _ => (1:ℝ)) x)^2 ∂μ) = μ.real S := by
    have he : (fun x => (S.indicator (fun _ => (1:ℝ)) x)^2) = S.indicator (fun _ => (1:ℝ)) := by
      funext x; by_cases hx : x ∈ S <;> simp [hx]
    rw [he, integral_indicator hS]; simp
  rw [hl, hr] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (tail_probability hqi hqpos hγ)) (Real.sqrt_nonneg _))
end MinUncut.Slice

namespace MinUncut.CubeRows
open IndependentSquares
variable {ι A W : Type*}
  [Fintype ι]
  [DecidableEq ι]
  [Fintype W]
  [DecidableEq W]
  [AddCommGroup W]

abbrev Other (i j : ι) := {k : ι // k ≠ i ∧ k ≠ j}

def join (i j : ι) (c : Other i j → Bool) (a b : Bool) (k : ι) : Bool :=
  if hi : k = i then a else if hj : k = j then b else c ⟨k,hi,hj⟩

omit [Fintype ι] in
@[simp] lemma join_i (i j : ι) (c : Other i j → Bool) (a b : Bool) : join i j c a b i = a := by simp [join]
omit [Fintype ι] in
@[simp] lemma join_j (i j : ι) (hij : i ≠ j) (c : Other i j → Bool) (a b : Bool) :
    join i j c a b j = b := by simp [join, hij.symm]
omit [Fintype ι] in
@[simp] lemma join_other (i j : ι) (c : Other i j → Bool) (a b : Bool) (k : Other i j) :
    join i j c a b k = c k := by simp [join, k.property.1, k.property.2]

def splitEquiv (i j : ι) (hij : i ≠ j) : (ι → Bool) ≃ ((Other i j → Bool) × Bool × Bool) where
  toFun ν := (fun k => ν k, ν i, ν j)
  invFun v := join i j v.1 v.2.1 v.2.2
  left_inv ν := by funext k; by_cases hi : k=i <;> by_cases hj : k=j <;> simp [join, hi, hj, hij.symm]
  right_inv v := by ext k <;> simp [hij]

def vertex (ν : ι → Bool) (x y : ι → A) (k : ι) : A := if ν k then x k else y k

def face (i : ι) (x : ι → A) : {k : ι // k ≠ i} → A := fun k => x k

def rowJ (i j : ι) (x y : ι → A) (v : (Other i j → Bool) × Bool) : {k : ι // k ≠ j} → A :=
  face j (vertex (join i j v.1 v.2 false) x y)

def rowI (i j : ι) (x y : ι → A) (v : (Other i j → Bool) × Bool) : {k : ι // k ≠ i} → A :=
  face i (vertex (join i j v.1 false v.2) x y)

lemma bool_choice_injective {x y : A} (hxy : x ≠ y) : Function.Injective (fun b : Bool => if b then x else y) := by
  intro a b h; cases a <;> cases b <;> simp_all

omit [Fintype ι] in
lemma rowJ_injective (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k) :
    Function.Injective (rowJ i j x y) := by
  intro v w h
  apply Prod.ext
  · funext k
    apply bool_choice_injective (hxy k)
    have hh := congrFun h ⟨k,k.property.2⟩
    simpa only [rowJ, face, vertex, join_other] using hh
  · apply bool_choice_injective (hxy i)
    have hh := congrFun h ⟨i,hij⟩
    simpa only [rowJ, face, vertex, join_i] using hh

omit [Fintype ι] in
lemma rowI_injective (i j : ι) (hij : i ≠ j) (x y : ι → A) (hxy : ∀ k, x k ≠ y k) :
    Function.Injective (rowI i j x y) := by
  intro v w h
  apply Prod.ext
  · funext k
    apply bool_choice_injective (hxy k)
    have hh := congrFun h ⟨k,k.property.1⟩
    simpa only [rowI, face, vertex, join_other] using hh
  · apply bool_choice_injective (hxy j)
    have hh := congrFun h ⟨j,hij.symm⟩
    simpa only [rowI, face, vertex, join_j i j hij] using hh

omit [Fintype ι] in
lemma face_join_J (i j : ι) (_hij : i ≠ j) (x y : ι → A)
    (c : Other i j → Bool) (a b : Bool) :
    face j (vertex (join i j c a b) x y) = rowJ i j x y (c,a) := by
  funext k
  dsimp [face, vertex, rowJ]
  congr 1
  unfold join
  split_ifs <;> simp_all [k.property]

omit [Fintype ι] in
lemma face_join_I (i j : ι) (_hij : i ≠ j) (x y : ι → A)
    (c : Other i j → Bool) (a b : Bool) :
    face i (vertex (join i j c a b) x y) = rowI i j x y (c,b) := by
  funext k
  dsimp [face, vertex, rowI]
  congr 1
  unfold join
  split_ifs <;> simp_all [k.property]

lemma prod_split (i j : ι) (hij : i ≠ j) (F : (ι → Bool) → ℝ) :
    (∏ ν, F ν) = ∏ c : Other i j → Bool,
      F (join i j c false false) * F (join i j c false true) *
      F (join i j c true false) * F (join i j c true true) := by
  have h := Fintype.prod_equiv (splitEquiv i j hij)
    F (fun v => F (join i j v.1 v.2.1 v.2.2))
    (fun ν => congrArg F ((splitEquiv i j hij).left_inv ν).symm)
  rw [h, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro c _
  simp only [Fintype.prod_prod_type, Fintype.prod_bool]
  ring

variable {C : Type*} [Fintype C] [DecidableEq C]
def boolSplitEquiv : ((C × Bool) → W) ≃ ((C → W) × (C → W)) where
  toFun t := (fun c => t (c,false), fun c => t (c,true))
  invFun v := fun cb => if cb.2 then v.2 cb.1 else v.1 cb.1
  left_inv t := by funext cb; rcases cb with ⟨c,b⟩; cases b <;> rfl
  right_inv v := by ext c <;> rfl

def cubeExpectation (i j : ι) (x y : ι → A) [Fintype A] [DecidableEq A]
    (V : (ι → Bool) → W → ℝ) : ℝ :=
  𝔼 Bj : ({k : ι // k ≠ j} → A) → W,
  𝔼 Bi : ({k : ι // k ≠ i} → A) → W,
    ∏ ν : ι → Bool, V ν (Bj (face j (vertex ν x y)) + Bi (face i (vertex ν x y)))

def squareProduct (i j : ι) (V : (ι → Bool) → W → ℝ)
    (r s : ((Other i j → Bool) × Bool) → W) : ℝ :=
  ∏ c : Other i j → Bool,
    V (join i j c false false) (r (c,false)+s (c,false)) *
    V (join i j c false true) (r (c,false)+s (c,true)) *
    V (join i j c true false) (r (c,true)+s (c,false)) *
    V (join i j c true true) (r (c,true)+s (c,true))

end MinUncut.CubeRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

def IsProbability (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

def SupportedBy (p q : α → ℝ) : Prop := ∀ a, p a ≠ 0 → q a ≠ 0

noncomputable def totalVariation (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def posterior (p w : α → ℝ) (z : ℝ) : α → ℝ :=
  fun a => p a * w a / z

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

noncomputable def conditionalKernel
    (p : α × β → ℝ) (fallback : β → ℝ) (a : α) (b : β) : ℝ := by
  classical
  exact if firstMarginal p a = 0 then fallback b
    else p (a, b) / firstMarginal p a

theorem kernelProduct_isProbability
    (r : α → ℝ) (k : α → β → ℝ)
    (hr : IsProbability r) (hk : ∀ a, IsProbability (k a)) :
    IsProbability (fun ab : α × β => r ab.1 * k ab.1 ab.2) := by
  constructor
  · intro ab
    exact mul_nonneg (hr.1 ab.1) ((hk ab.1).1 ab.2)
  · simp only [Fintype.sum_prod_type, ← Finset.mul_sum,
      (hk _).2, mul_one, hr.2]

theorem totalVariation_joint_common_kernel (p q : α → ℝ) (k : α → β → ℝ)
    (hk : ∀ a, IsProbability (k a)) :
    totalVariation (fun ab : α × β => p ab.1 * k ab.1 ab.2)
      (fun ab : α × β => q ab.1 * k ab.1 ab.2) = totalVariation p q := by
  have hpoint : ∀ a b, |p a * k a b - q a * k a b| = |p a - q a| * k a b := by
    intro a b
    rw [← sub_mul, abs_mul, abs_of_nonneg ((hk a).1 b)]
  simp only [totalVariation, Fintype.sum_prod_type, hpoint, ← Finset.mul_sum,
    (hk _).2, mul_one]

end MinUncutGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

def patch {X : Type*} (A : I → Prop) (background : I → X) (active : {i // A i} → X) : I → X :=
  fun i => if h : A i then active ⟨i,h⟩ else background i

omit [Fintype I] in
@[simp] lemma patch_active {X : Type*} (A : I → Prop) (background : I → X)
    (active : {i // A i} → X) (i : {i // A i}) : patch A background active i = active i := by
  simp [patch,i.property]

omit [Fintype I] in
@[simp] lemma patch_inactive {X : Type*} (A : I → Prop) (background : I → X)
    (active : {i // A i} → X) (i : I) (hi : ¬A i) : patch A background active i = background i := by
  simp [patch,hi]

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.CorrelatedSampling

noncomputable section

variable {α : Type*} [Fintype α]

variable {σ : Type*} [Fintype σ]

variable [DecidableEq σ]

structure ThresholdInterval where
  lo : ℝ
  hi : ℝ
  valid : lo ≤ hi

end

end MinUncutGames.Foundations.CorrelatedSampling

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_Pinsker
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

noncomputable def coordinateMarginal (p : (ι → α) → ℝ) (i : ι) (a : α) : ℝ := by
  classical
  exact ∑ x, if x i = a then p x else 0

noncomputable def independentProduct (q : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, q i (x i)

theorem independentProduct_isProbability (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) :
    IsProbability (independentProduct q) := by
  classical
  constructor
  · intro x
    exact Finset.prod_nonneg (fun i _ => (hq i).1 (x i))
  · simp only [independentProduct, ← Fintype.prod_sum, (hq _).2, Finset.prod_const_one]

open scoped BigOperators

open scoped BigOperators

end MinUncutGames.Foundations.Information

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_ProfileCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Repetition.ProfileCorrection
open scoped BigOperators
open MinUncutGames.Foundations.Information
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

def seedQuestionMarginal (p : X × (S × Y) → ℝ) : X × S → ℝ :=
  firstMarginal (fun z : (X × S) × Y => p (z.1.1, (z.1.2, z.2)))

theorem seedQuestionMarginal_isProbability (p : X × (S × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (seedQuestionMarginal p) := by
  apply firstMarginal_isProbability
  constructor
  · intro z
    exact hp.1 _
  · have h := hp.2
    simp only [Fintype.sum_prod_type] at h ⊢
    exact h

omit [Fintype X] in
theorem seedQuestionMarginal_first (p : X × (S × Y) → ℝ) :
    firstMarginal (seedQuestionMarginal p) = firstMarginal p := by
  funext x
  simp only [seedQuestionMarginal, firstMarginal, Fintype.sum_prod_type]

theorem totalVariation_triangle {Ω : Type*} [Fintype Ω]
    (p c d : Ω → ℝ) :
    totalVariation p d ≤ totalVariation p c + totalVariation c d := by
  unfold totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (p x) (c x) (d x))
  rw [Finset.sum_add_distrib] at h
  linarith

end
end MinUncutGames.Foundations.Repetition.ProfileCorrection

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Information
noncomputable section

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealEndpoint (q : X × Y) (side : Bool) : X ⊕ Y :=
  if side then Sum.inr q.2 else Sum.inl q.1

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectedInformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Information
noncomputable section

def mergeCoordinates {Ω : Type*} {n : Nat} (selected : Finset (Fin n))
    (fixed : selected → Ω) (remaining : {i : Fin n // i ∉ selected} → Ω) : Fin n → Ω :=
  fun i => if h : i ∈ selected then fixed ⟨i,h⟩ else remaining ⟨i,h⟩

def coordinateSplitEquiv {Ω : Type*} {n : Nat} (selected : Finset (Fin n)) :
    (Fin n → Ω) ≃ ((selected → Ω) × ({i : Fin n // i ∉ selected} → Ω)) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun x := mergeCoordinates selected x.1 x.2
  left_inv x := by funext i; simp [mergeCoordinates]
  right_inv x := by
    apply Prod.ext <;> funext i <;> simp [mergeCoordinates, i.property]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {n : Nat}

abbrev SelectedLabels (selected : Finset (Fin n)) :=
  (selected → A₁) × (selected → A₂)

def selectedQuestionTuple (selected : Finset (Fin n))
    (fixed : selected → Q₁ × Q₂)
    (remaining : {i : Fin n // i ∉ selected} → Q₁ × Q₂) :
    (Fin n → Q₁) × (Fin n → Q₂) :=
  (fun i => (mergeCoordinates selected fixed remaining i).1,
   fun i => (mergeCoordinates selected fixed remaining i).2)

abbrev SelectedInput (Q₁ Q₂ : Type*) {n : Nat} (selected : Finset (Fin n)) :=
  (selected → Q₁ × Q₂) × ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

open scoped BigOperators
open Information

variable {α β : Type*} [Fintype α] [Fintype β]

open scoped BigOperators
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedJoint (p : S × (X × Y) → ℝ) : (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  (if z.1.2 = Sum.inl z.2.1 then p (z.1.1, z.2) / 2 else 0) +
  (if z.1.2 = Sum.inr z.2.2 then p (z.1.1, z.2) / 2 else 0)

theorem sum_maskedJoint (p : S × (X × Y) → ℝ) :
    (∑ z, maskedJoint p z) = ∑ z, p z := by
  classical
  have hrow (s : S) (q : X × Y) :
      (∑ r : X ⊕ Y, maskedJoint p ((s,r),q)) = p (s,q) := by
    simp [maskedJoint]
  calc
    _ = ∑ s : S, ∑ r : X ⊕ Y, ∑ q : X × Y, maskedJoint p ((s,r),q) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ s : S, ∑ q : X × Y, p (s,q) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp_rw [hrow]
    _ = _ := (Fintype.sum_prod_type _).symm

theorem maskedJoint_isProbability_iff (p : S × (X × Y) → ℝ) :
    Information.IsProbability (maskedJoint p) ↔ Information.IsProbability p := by
  classical
  constructor
  · intro h
    constructor
    · intro z
      have hp := h.1 ((z.1,Sum.inl z.2.1),z.2)
      simp [maskedJoint] at hp
      linarith
    · rw [← sum_maskedJoint]
      exact h.2
  · intro h
    constructor
    · intro z
      have hp : 0 ≤ p (z.1.1,z.2) / 2 := div_nonneg (h.1 _) (by norm_num)
      dsimp [maskedJoint]
      split_ifs <;> linarith
    · rw [sum_maskedJoint]
      exact h.2

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def mergeAt {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) : I → R :=
  fun i => if h : i = j then a else rest ⟨i,h⟩

omit [Fintype I] in
@[simp] theorem mergeAt_self {R : Type*} (j : I) (a : R) (rest : {i : I // i ≠ j} → R) :
    mergeAt j a rest j = a := by simp [mergeAt]

omit [Fintype I] in
@[simp] theorem mergeAt_other {R : Type*} (j : I) (a : R)
    (rest : {i : I // i ≠ j} → R) (i : {i : I // i ≠ j}) :
    mergeAt j a rest i.1 = rest i := by simp [mergeAt, i.property]

def revealSplitEquiv (j : I) :
    ((T × (I → X ⊕ Y)) × (X × Y)) ≃
      (((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) × (X × Y)) where
  toFun z := (((z.1.1, fun i => z.1.2 i.1), z.1.2 j), z.2)
  invFun z := ((z.1.1.1, mergeAt j z.1.2 z.1.1.2), z.2)
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        by_cases h : i = j <;> simp [mergeAt, h]
    · rfl
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          exact mergeAt_other j z.1.2 z.1.1.2 i
      · exact mergeAt_self j z.1.2 z.1.1.2
    · rfl

theorem totalVariation_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p q : B → ℝ) :
    Information.totalVariation (fun a => p (e a)) (fun a => q (e a)) =
      Information.totalVariation p q := by
  unfold Information.totalVariation
  congr 1
  exact e.sum_comp (fun b => |p b - q b|)

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectedMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Information
noncomputable section
variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationEquiv (selected : Finset (Fin n)) :
    ((SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      (Q₁ × Q₂)) ≃
    ((((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
      ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) × (Q₁ × Q₂)) where
  toFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  invFun z := (((z.1.1.1,z.1.2),z.1.1.2),z.2)
  left_inv _ := rfl
  right_inv _ := rfl

end

end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_DistributionMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open Information
noncomputable section

theorem isProbability_comp_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (p : B → ℝ) (hp : IsProbability p) :
    IsProbability (fun a => p (e a)) := by
  constructor
  · intro a
    exact hp.1 _
  · rw [e.sum_comp]
    exact hp.2

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

abbrev SelectedCommonData (selected : Finset (Fin n))
    (j : {i : Fin n // i ∉ selected}) :=
  ((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
    ({i : {i : Fin n // i ∉ selected} // i ≠ j} → Q₁ ⊕ Q₂)

variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem firstMarginal_totalVariation_le (r t : X × Y → ℝ) :
    totalVariation (firstMarginal r) (firstMarginal t) ≤ totalVariation r t := by
  unfold totalVariation firstMarginal
  simp_rw [← Finset.sum_sub_distrib]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => Finset.abs_sum_le_sum_abs (fun y : Y => r (x,y)-t (x,y)) Finset.univ)
  rw [Fintype.sum_prod_type]
  linarith

def leftCommonMarginal (p : S × (X × Y) → ℝ) : X × S → ℝ :=
  fun z => ∑ y, p (z.2,(z.1,y))

def leftCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : X → S → ℝ :=
  conditionalKernel (leftCommonMarginal p) fallback

def swapSeedLeft : (X × (S × Y)) ≃ (S × (X × Y)) where
  toFun z := (z.2.1,(z.1,z.2.2))
  invFun z := (z.2.1,(z.1,z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

theorem leftCommonMarginal_isProbability (p : S × (X × Y) → ℝ)
    (hp : IsProbability p) : IsProbability (leftCommonMarginal p) := by
  exact ProfileCorrection.seedQuestionMarginal_isProbability
    (fun z => p (swapSeedLeft z)) (isProbability_comp_equiv swapSeedLeft p hp)

def swapQuestionEndpoints : (S × (Y × X)) ≃ (S × (X × Y)) where
  toFun z := (z.1,(z.2.2,z.2.1))
  invFun z := (z.1,(z.2.2,z.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

def rightCommonMarginal (p : S × (X × Y) → ℝ) : Y × S → ℝ :=
  fun z => ∑ x, p (z.2,(x,z.1))

def rightCommonProfile (p : S × (X × Y) → ℝ) (fallback : S → ℝ) : Y → S → ℝ :=
  conditionalKernel (rightCommonMarginal p) fallback

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Overlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition

open scoped BigOperators
open Information

open scoped BigOperators
noncomputable section

universe u

open CorrelatedSampling

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]
  [Nonempty S] [DecidableEq S]

open scoped BigOperators
open Information

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

variable {I T X Y : Type*} [Fintype I] [DecidableEq I] [Fintype T]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

def revealDataSplitEquiv (j : I) :
    (T × (I → X ⊕ Y)) ≃ ((T × ({i : I // i ≠ j} → X ⊕ Y)) × (X ⊕ Y)) where
  toFun z := ((z.1, fun i => z.2 i.1), z.2 j)
  invFun z := (z.1.1, mergeAt j z.2 z.1.2)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      by_cases h : i = j <;> simp [mergeAt, h]
  right_inv z := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        exact mergeAt_other j z.2 z.1.2 i
    · exact mergeAt_self j z.2 z.1.2

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : Nat}

def selectedObservationDataEquiv (selected : Finset (Fin n)) :
    (SelectedInput Q₁ Q₂ selected × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ≃
      (((selected → Q₁ × Q₂) × SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) ×
        ({i : Fin n // i ∉ selected} → Q₁ ⊕ Q₂)) where
  toFun z := ((z.1.1,z.2),z.1.2)
  invFun z := ((z.1.1,z.2),z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

end
end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CompletedSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition
open scoped BigOperators
open CorrelatedSampling

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

@[simp] theorem logTwo_one : logTwo 1 = 0 := by simp [logTwo]

theorem logTwo_inv_le_of_half_pow_le {p : ℝ} (m : ℕ)
    (h : (1 / 2 : ℝ) ^ m ≤ p) : logTwo (1 / p) ≤ m := by
  have hp : 0 < p := (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m).trans_le h
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m) h
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [Real.log_pow, hhalf] at hlog
  unfold logTwo
  rw [one_div, Real.log_inv]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  nlinarith

theorem contraction_step {v ell : ℝ} {n m : ℕ} {p next : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : 1 ≤ m) (hmn : m < n) (hp : 0 ≤ p)
    (hmono : next ≤ p)
    (hprev : p ≤ ((1 + v) / 2) ^ m)
    (hcut : 2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m))
    (hstep : next ≤ p * (v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)))) :
    next ≤ ((1 + v) / 2) ^ (m + 1) := by
  by_cases hsmall : p ≤ ((1 + v) / 2) ^ (m + 1)
  · exact hmono.trans hsmall
  have hq : (1 / 2 : ℝ) ≤ (1 + v) / 2 := by linarith
  have hhalf : (1 / 2 : ℝ) ^ (m + 1) ≤ p :=
    (pow_le_pow_left₀ (by norm_num) hq (m + 1)).trans (le_of_not_ge hsmall)
  have hlog := logTwo_inv_le_of_half_pow_le (m + 1) hhalf
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (n : ℝ) - m := by
    have hmnreal : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hmell : (m : ℝ) ≤ (m : ℝ) * ell := by nlinarith
  have hbudget : (m : ℝ) * ell + logTwo (1 / p) ≤ 3 * (m : ℝ) * ell := by
    simp only [Nat.cast_add, Nat.cast_one] at hlog
    nlinarith
  have hsqrt : Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 - v) / 30 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ (1 - v) / 30)).2
    apply (div_le_iff₀ hden).2
    nlinarith
  have hfactor : v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 + v) / 2 := by
    linarith
  calc
    next ≤ p * (v + 15 * Real.sqrt
        (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m))) := hstep
    _ ≤ p * ((1 + v) / 2) := mul_le_mul_of_nonneg_left hfactor hp
    _ ≤ ((1 + v) / 2) ^ m * ((1 + v) / 2) :=
      mul_le_mul_of_nonneg_right hprev (by linarith)
    _ = ((1 + v) / 2) ^ (m + 1) := (pow_succ _ _).symm

theorem cutoff_step {v ell : ℝ} {n m : ℕ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : (m : ℝ) < (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :
    2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m) := by
  have hell0 : 0 < ell := by linarith
  have hd : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hmul : (m : ℝ) * (2925 * ell) < (n : ℝ) * (1 - v) ^ 2 :=
    (lt_div_iff₀ (by positivity : 0 < 2925 * ell)).1 hm
  have hdell : (1 - v) ^ 2 ≤ 225 * ell := by linarith
  have hprod := mul_le_mul_of_nonneg_left hdell (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith

theorem cutoff_le_length {v ell : ℝ} (n : ℕ)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell) :
    (n : ℝ) * (1 - v) ^ 2 / (2925 * ell) ≤ n := by
  have hell0 : 0 < ell := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 2925 * ell)).2
  have hd : (1 - v) ^ 2 ≤ 2925 * ell := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

def ScalarRecurrence (p : ℕ → ℝ) (n : ℕ) (v ell : ℝ) : Prop :=
  ∀ m, m < n → p (m + 1) ≤ p m * (v + 15 * Real.sqrt
    (((m : ℝ) * ell + logTwo (1 / p m)) / ((n : ℝ) - m)))

theorem decay_to_cutoff (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ ((1 + v) / 2) ^
      ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) := by
  let T : ℝ := (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)
  let M : ℕ := Nat.ceil T
  have hMn : M ≤ n := Nat.ceil_le.mpr (cutoff_le_length n hv0 hv1 hell)
  have hind : ∀ m, m ≤ M → p m ≤ ((1 + v) / 2) ^ m := by
    intro m
    induction m with
    | zero => intro _; simp [hp0]
    | succ m ih =>
        intro hmM
        have hmM' : m < M := Nat.lt_of_succ_le hmM
        have hmn : m < n := hmM'.trans_le hMn
        have hprev := ih (Nat.le_of_lt hmM')
        by_cases hm0 : m = 0
        · subst m
          have hinit : p 1 ≤ v := by
            have hs := hrec 0 hmn
            simpa [hp0] using hs
          simpa using hinit.trans (by linarith : v ≤ (1 + v) / 2)
        · have hmT : (m : ℝ) < T := Nat.lt_ceil.mp hmM'
          exact contraction_step hv0 hv1 hell (Nat.one_le_iff_ne_zero.mpr hm0)
            hmn (hpnonneg m) (hpmono (Nat.le_succ m)) hprev
            (cutoff_step hv0 hv1 hell hmT) (hrec m hmn)
  have hq0 : 0 < (1 + v) / 2 := by linarith
  have hq1 : (1 + v) / 2 ≤ 1 := by linarith
  calc
    p n ≤ p M := hpmono hMn
    _ ≤ ((1 + v) / 2) ^ M := hind M le_rfl
    _ = ((1 + v) / 2) ^ (M : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ((1 + v) / 2) ^ T :=
      Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (Nat.le_ceil T)

theorem block_contraction {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ) ≤
      1 - (1 - v) ^ 3 / 5850 := by
  have hd : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hb := rpow_one_add_le_one_add_mul_self
    (s := -(1 - v) / 2) (p := (1 - v) ^ 2 / 2925)
    (by linarith) (by positivity) (by nlinarith)
  have hbase : 1 + -(1 - v) / 2 = (1 + v) / 2 := by ring
  have hrhs : 1 + (1 - v) ^ 2 / 2925 * (-(1 - v) / 2) =
      1 - (1 - v) ^ 3 / 5850 := by ring
  rwa [hbase, hrhs] at hb

theorem scalar_bound_6000 (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) := by
  have hell0 : 0 < ell := by linarith
  have hq0 : 0 ≤ (1 + v) / 2 := by linarith
  have hexp : 0 ≤ (n : ℝ) / ell := by positivity
  have hblock := block_contraction hv0 hv1
  have hweak : 1 - (1 - v) ^ 3 / 5850 ≤ 1 - (1 - v) ^ 3 / 6000 := by
    have : 0 ≤ (1 - v) ^ 3 := by positivity
    nlinarith
  calc
    p n ≤ ((1 + v) / 2) ^
        ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :=
      decay_to_cutoff p n hv0 hv1 hell hp0 hpnonneg hpmono hrec
    _ = (((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ)) ^ ((n : ℝ) / ell) := by
      rw [← Real.rpow_mul hq0]
      congr 1
      ring
    _ ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hq0 _) (hblock.trans hweak) hexp

end MinUncutGames.Foundations.Repetition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_AlphabetBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Repetition

open scoped BigOperators
noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq Q₁] [DecidableEq Q₂] {n : ℕ}

theorem selectedLabels_card (selected : Finset (Fin n)) :
    Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) =
      (Fintype.card A₁ * Fintype.card A₂) ^ selected.card := by
  simp [SelectedLabels, Fintype.card_prod, mul_pow]

theorem unusedCoordinates_card (selected : Finset (Fin n)) :
    Fintype.card {i : Fin n // i ∉ selected} = n - selected.card := by
  classical
  simp [Fintype.card_subtype_compl]

theorem unusedCoordinates_card_real (selected : Finset (Fin n)) :
    (Fintype.card {i : Fin n // i ∉ selected} : ℝ) = (n : ℝ) - selected.card := by
  have hs : selected.card ≤ n := by simpa using Finset.card_le_univ selected
  rw [unusedCoordinates_card, Nat.cast_sub hs]

theorem log_le_logTwo {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ logTwo x := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo_le : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  unfold logTwo
  apply (le_div_iff₀ htwo).2
  simpa using mul_le_mul_of_nonneg_left htwo_le hlog

theorem selectedLabels_log_le [Nonempty A₁] [Nonempty A₂]
    (selected : Finset (Fin n)) (ell : ℝ)
    (hell : logTwo ((Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ)) ≤ ell) :
    Real.log (Fintype.card (SelectedLabels (A₁ := A₁) (A₂ := A₂) selected) : ℝ) ≤
      (selected.card : ℝ) * ell := by
  have ha : (1 : ℝ) ≤ Fintype.card A₁ := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hb : (1 : ℝ) ≤ Fintype.card A₂ := by exact_mod_cast Fintype.card_pos (α := A₂)
  have hab : (1 : ℝ) ≤ (Fintype.card A₁ : ℝ) * (Fintype.card A₂ : ℝ) := by nlinarith
  rw [selectedLabels_card, Nat.cast_pow, Nat.cast_mul, Real.log_pow]
  exact mul_le_mul_of_nonneg_left ((log_le_logTwo hab).trans hell) (Nat.cast_nonneg _)

theorem sqrt_budget_factor (a b : ℝ) (ha : 0 < a) :
    Real.sqrt (a * b) = a * Real.sqrt (b / a) := by
  have he : a * b = a ^ 2 * (b / a) := by
    field_simp
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq (le_of_lt ha)]

end
end MinUncutGames.Foundations.Repetition

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_SelectionSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Repetition.SelectionSequence

theorem exists_unused {n : Nat} (S : Finset (Fin n)) (hcard : S.card < n) :
    ∃ j : Fin n, j ∉ S := by
  classical
  apply Classical.byContradiction
  intro h
  have hall : ∀ j : Fin n, j ∈ S := by
    intro j
    apply Classical.byContradiction
    intro hj
    exact h ⟨j, hj⟩
  have hfull : S = Finset.univ :=
    Finset.ext (fun j => iff_of_true (hall j) (Finset.mem_univ j))
  have hbad : n < n := by
    simpa only [hfull, Finset.card_univ, Fintype.card_fin] using hcard
  exact Nat.lt_irrefl n hbad

noncomputable def nextSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  if hs : S.card < n then insert (Classical.choose (witness S hs)) S else S

noncomputable def selectedSet {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) : Nat → Finset (Fin n)
  | 0 => ∅
  | m + 1 => nextSet Step witness (selectedSet Step witness m)

theorem selectedSet_card {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) (m : Nat) :
    (selectedSet Step witness m).card = min m n := by
  induction m with
  | zero => simp [selectedSet]
  | succ m ih =>
    by_cases hm : m < n
    · have hc : (selectedSet Step witness m).card = m := by
        simpa only [Nat.min_eq_left (Nat.le_of_lt hm)] using ih
      have hs : (selectedSet Step witness m).card < n := by
        simpa only [hc] using hm
      rw [selectedSet, nextSet, dite_eq_left hs,
        Finset.card_insert_of_notMem ((Classical.choose_spec (witness _ hs)).1),
        hc, Nat.min_eq_left (Nat.succ_le_of_lt hm)]
    · have hc : (selectedSet Step witness m).card = n := by
        simpa only [Nat.min_eq_right (Nat.le_of_not_gt hm)] using ih
      have hs : ¬(selectedSet Step witness m).card < n := by
        rw [hc]
        exact Nat.not_lt.mpr (Nat.le_refl n)
      rw [selectedSet, nextSet, dite_eq_right hs, hc,
        Nat.min_eq_right (Nat.le_trans (Nat.le_of_not_gt hm) (Nat.le_succ m))]

theorem selectedSet_subset_succ {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) (m : Nat) :
    selectedSet Step witness m ⊆ selectedSet Step witness (m + 1) := by
  change selectedSet Step witness m ⊆ nextSet Step witness (selectedSet Step witness m)
  unfold nextSet
  split
  · exact Finset.subset_insert _ _
  · exact le_rfl

theorem selectedSet_monotone {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) :
    Monotone (selectedSet Step witness) :=
  monotone_nat_of_le_succ (selectedSet_subset_succ Step witness)

theorem selectedSet_univ {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j) :
    selectedSet Step witness n = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [selectedSet_card]

theorem selectedSet_step {n : Nat}
    (Step : Finset (Fin n) → Fin n → Prop)
    (witness : ∀ S, S.card < n → ∃ j, j ∉ S ∧ Step S j)
    (m : Nat) (hm : m < n) :
    ∃ j, j ∉ selectedSet Step witness m ∧
      selectedSet Step witness (m + 1) = insert j (selectedSet Step witness m) ∧
      Step (selectedSet Step witness m) j := by
  have hc : (selectedSet Step witness m).card = m := by
    rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
  have hs : (selectedSet Step witness m).card < n := by simpa only [hc] using hm
  let j := Classical.choose (witness (selectedSet Step witness m) hs)
  have hj := Classical.choose_spec (witness (selectedSet Step witness m) hs)
  refine ⟨j, hj.1, ?_, hj.2⟩
  simp only [selectedSet, nextSet, dite_eq_left hs, j]

def SetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (S : Finset (Fin n)) (j : Fin n) : Prop :=
  P (insert j S) ≤ P S *
    (v + 15 * Real.sqrt (((S.card : ℝ) * ell + logTwo (1 / P S)) /
      ((n : ℝ) - S.card)))

theorem totalSetStep {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∀ S, S.card < n → ∃ j, j ∉ S ∧ SetStep P v ell S j := by
  intro S hcard
  by_cases hp : 0 < P S
  · exact hpositive S hcard hp
  · obtain ⟨j, hj⟩ := exists_unused S hcard
    have hz : P S = 0 := le_antisymm (le_of_not_gt hp) (hnonneg S)
    have hnext : P (insert j S) = 0 := le_antisymm
      ((hanti (Finset.subset_insert j S)).trans (le_of_eq hz)) (hnonneg (insert j S))
    refine ⟨j, hj, ?_⟩
    simpa only [SetStep, hnext, hz, zero_mul] using (le_refl (0 : ℝ))

theorem exists_scalar_sequence {n : Nat} (P : Finset (Fin n) → ℝ) (v ell : ℝ)
    (hempty : P ∅ = 1) (hnonneg : ∀ S, 0 ≤ P S) (hanti : Antitone P)
    (hpositive : ∀ S, S.card < n → 0 < P S →
      ∃ j, j ∉ S ∧ SetStep P v ell S j) :
    ∃ p : Nat → ℝ, p 0 = 1 ∧ (∀ m, 0 ≤ p m) ∧ Antitone p ∧
      ScalarRecurrence p n v ell ∧ p n = P Finset.univ := by
  let witness := totalSetStep P v ell hnonneg hanti hpositive
  let sets := selectedSet (SetStep P v ell) witness
  let p := fun m => P (sets m)
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · change P (selectedSet (SetStep P v ell) witness 0) = 1
    simpa only [selectedSet] using hempty
  · intro m
    exact hnonneg (sets m)
  · intro i j hij
    exact hanti (selectedSet_monotone (SetStep P v ell) witness hij)
  · intro m hm
    obtain ⟨j, _, hnext, hbound⟩ :=
      selectedSet_step (SetStep P v ell) witness m hm
    have hc : (selectedSet (SetStep P v ell) witness m).card = m := by
      rw [selectedSet_card, Nat.min_eq_left (Nat.le_of_lt hm)]
    change P (selectedSet (SetStep P v ell) witness (m + 1)) ≤ _
    rw [hnext]
    simpa only [SetStep, hc] using hbound
  · change P (selectedSet (SetStep P v ell) witness n) = P Finset.univ
    rw [selectedSet_univ]

end MinUncutGames.Foundations.Repetition.SelectionSequence

noncomputable section
namespace MinUncut.Outer
open MinUncutGames.Foundations.Repetition

def repetitionRate : ℝ := 99999999/100000000
lemma repetitionRate_pos : 0 < repetitionRate := by norm_num [repetitionRate]
lemma repetitionRate_lt_one : repetitionRate<1 := by norm_num [repetitionRate]
lemma repetitionRate_fourth : 1-(1-(11/12 : ℝ))^3/6000 ≤ repetitionRate^4 := by
  norm_num [repetitionRate]

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CoefficientMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
attribute [local instance] Classical.propDecidable 
variable {I : Type*} [Fintype I]

def hintRate (q : ℕ) : ℝ := 1-(1/(2:ℝ)^q)*(1-repetitionRate)

lemma hintRate_nonnegative (q : ℕ) : 0 ≤ hintRate q := by
  have hp : (1 : ℝ) ≤ 2^q := one_le_pow₀ (by norm_num)
  have hd : 0 ≤ 1/(2:ℝ)^q := by positivity
  have hd' : 1/(2:ℝ)^q ≤ 1 := (div_le_one (by positivity)).2 hp
  have hr := repetitionRate_pos.le
  have hr' := repetitionRate_lt_one.le
  unfold hintRate
  nlinarith

lemma hintRate_lt_one (q : ℕ) : hintRate q<1 := by
  unfold hintRate
  have h : 0<(1/(2:ℝ)^q)*(1-repetitionRate) :=
    mul_pos (by positivity) (sub_pos.mpr repetitionRate_lt_one)
  linarith

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
attribute [local instance] Classical.propDecidable
variable {Name I S : Type*} [Fintype Name] [Fintype I] [Fintype S] [Nonempty S]

def sampledPositions (w : I → S × Fin 3) : I → Fin 3 := fun j => (w j).2

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_HintSoundness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
attribute [local instance] Classical.propDecidable 
variable {Name I S : Type*} [Fintype Name] [Fintype I] [Fintype S] [Nonempty S]

lemma shared_hint_rate_vanishes (q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ n : ℕ, hintRate q ^ n < ε := by
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (hintRate_nonnegative q)
    (hintRate_lt_one q)).eventually (gt_mem_nhds hε) |>.exists

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ListDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
attribute [local instance] Classical.propDecidable 

def paddedChoice {A : Type*} [Nonempty A] (S : Finset A) {L : ℕ} (i : Fin L) : A :=
  if h : i.val<S.card then ((Finset.equivFin S).symm ⟨i.val,h⟩).val else Classical.ofNonempty

lemma paddedChoice_covers {A : Type*} [Nonempty A] (S : Finset A) {L : ℕ}
    (hS : S.card≤L) (a : A) (ha : a ∈ S) : ∃ i : Fin L, paddedChoice S i=a := by
  let j := (Finset.equivFin S) ⟨a,ha⟩
  let i : Fin L := ⟨j.val,j.isLt.trans_le hS⟩
  refine ⟨i,?_⟩
  simp only [paddedChoice,i,dite_eq_left j.isLt]
  exact congrArg Subtype.val ((Finset.equivFin S).symm_apply_apply ⟨a,ha⟩)


open scoped BigOperators
attribute [local instance] Classical.propDecidable

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_JointHintSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open OuterSmoothness
attribute [local instance] Classical.propDecidable 
variable {Name I : Type*} [Fintype I]

def hiddenSet (H : Finset I) : I → Bool := fun i => decide (i ∈ H)

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Away
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A ι W : Type*}
  [Fintype A]
  [DecidableEq A]
  [Nonempty A]
  [Fintype ι]
  [DecidableEq ι]
  [Fintype W]
  [DecidableEq W]
  [AddCommGroup W]

def positiveSupport (I : (ι → A) → ℕ) : Finset (ι → A) := Finset.univ.filter (fun u => 0 < I u)

omit [DecidableEq A] [Nonempty A] in
lemma positiveSupport_card (I : (ι → A) → ℕ) : (positiveSupport I).card ≤ ∑ u, I u := by
  calc
    _ = ∑ u ∈ positiveSupport I, 1 := by simp
    _ ≤ ∑ u ∈ positiveSupport I, I u := Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2)
    _ ≤ ∑ u, I u := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)

end MinUncut.Subbox

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_VertexInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.CubeRows
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Nonempty A]

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Nonempty A] in
lemma vertex_injective (x y : ι → A) (hxy : ∀ i, x i≠y i) :
    Function.Injective (fun ν : ι → Bool => vertex ν x y) := by
  intro ν ω he
  funext i
  exact bool_choice_injective (hxy i) (congrFun he i)

omit [DecidableEq A] [Nonempty A] in
lemma independent_points (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : (ι → A) → ℝ → ℝ) (hV : ∀ x, Measurable (V x))
    (x y : ι → A) (hxy : ∀ i, x i≠y i) :
    (∫ c, ∏ ν : ι → Bool, V (vertex ν x y) (c (vertex ν x y)) ∂Measure.pi (fun _ : ι → A => μ)) =
      ∏ ν : ι → Bool, ∫ t, V (vertex ν x y) t ∂μ := by
  have hi := (iIndepFun_pi (μ := fun _ : ι → A => μ) (X := fun z t => V z t)
    (fun z => (hV z).aemeasurable)).precomp (vertex_injective x y hxy)
  rw [hi.integral_fun_prod_eq_prod_integral (fun ν => ((hV _).comp (measurable_pi_apply _)).aestronglyMeasurable)]
  apply Finset.prod_congr rfl
  intro ν _
  have hh := integral_map (μ := Measure.pi (fun _ : ι → A => μ))
    (measurable_pi_apply (vertex ν x y)).aemeasurable (hV (vertex ν x y)).aestronglyMeasurable
  rw [(measurePreserving_eval (fun _ : ι → A => μ) (vertex ν x y)).map_eq] at hh
  exact hh.symm

omit [DecidableEq A] [Nonempty A] in
lemma centered_point_cube_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : (ι → A) → ℝ → ℝ) (hV : ∀ x, Measurable (V x))
    (hmean : ∀ x, (∫ t, V x t ∂μ)=0) (x y : ι → A) (hxy : ∀ i, x i≠y i) :
    (∫ c, ∏ ν : ι → Bool, V (vertex ν x y) (c (vertex ν x y)) ∂Measure.pi (fun _ : ι → A => μ))=0 := by
  rw [independent_points μ V hV x y hxy]
  apply Finset.prod_eq_zero (Finset.mem_univ (fun _ => false))
  exact hmean _
end MinUncut.CubeRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_EraseAway
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Subbox
open OuterSmoothness
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A ι : Type*} [Fintype A] [DecidableEq A] [Fintype ι] [DecidableEq ι]

lemma expect_sigma_const {T : Type*} [Fintype T] {B : T → Type*} [∀ t, Fintype (B t)]
    (D : ℕ) (hD : ∀ t, Fintype.card (B t)=D) (f : (t : T) → B t → ℝ) :
    (𝔼 t, 𝔼 b, f t b)=(𝔼 p : Sigma B, f p.fst p.snd) := by
  have hc : Fintype.card (Sigma B)=Fintype.card T*D := by simp [Fintype.card_sigma,hD]
  simp only [Fintype.expect_eq_sum_div_card,hD,hc,Nat.cast_mul,Fintype.sum_sigma]
  rw [← Finset.sum_div, div_div]
  congr 1
  ring

open OuterSmoothness
open scoped BigOperators
end MinUncut.Subbox

namespace MinUncut.Slice
open MeasureTheory
open scoped BigOperators
variable {W Ω : Type*}
  [Fintype W]
  [DecidableEq W]
  [AddCommGroup W]
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]

def energy (v : Ω → W → ℝ) (t : Ω) : ℝ := 𝔼 w, (v t w)^2

end MinUncut.Slice

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ExpectResampleRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.CubeRows
lemma card_other {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) (hij : i≠j) :
    Fintype.card {k : ι // k≠i ∧ k≠j}=Fintype.card ι-2 := by
  let e : {k : ι // k≠i ∧ k≠j} ≃ {k : ι // k∈({i,j}:Finset ι)ᶜ} :=
    Equiv.subtypeEquivRight (fun k => by simp only [Finset.mem_compl,Finset.mem_insert,
      Finset.mem_singleton,not_or])
  calc
    _ = (({i,j}:Finset ι)ᶜ).card := (Fintype.card_congr e).trans (Fintype.card_coe _)
    _ = _ := by simp [Finset.card_compl,hij]; omega
end MinUncut.CubeRows

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
variable {m n : ℕ}

open scoped BigOperators
variable {m n : ℕ}

open scoped BigOperators
variable {m n : ℕ}
namespace MinUncut.Slice

def lossBound (H γ A E q : ℝ) : ℝ := E/H+Real.sqrt E*Real.sqrt (q/γ)+E/A

lemma lossBound_mono {H γ A E E' q q' : ℝ} (hH : 0≤H) (hγ : 0≤γ) (hA : 0≤A)
    (hE : E≤E') (hq : q≤q') : lossBound H γ A E q ≤ lossBound H γ A E' q' := by
  unfold lossBound
  gcongr

end MinUncut.Slice

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace MinUncut.Outer
open OuterSmoothness RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

def listTerm (M u θ : ℝ) (q k : ℕ) : ℝ :=
  (⌈M^2/u^2⌉₊ : ℝ)*(⌈M^2/θ^2⌉₊ : ℝ)*hintRate q^k

def remainderTerm (M u θ : ℝ) (q k t : ℕ) : ℝ :=
  (256/θ^4)*(u^2*M^2+Real.sqrt (((2 : ℝ)^(4*(q+3)*k)-1)*(k : ℝ)^2/t)*(M+M^2/u)^4)

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RawRationalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess
namespace RawRat

lemma product_denominator (a b : ℕ) : (((a+1)*(b+1)-1:ℕ):ℚ)+1=((a:ℚ)+1)*((b:ℚ)+1) := by
  have h : 1≤(a+1)*(b+1) := by nlinarith
  rw [Nat.cast_sub h]
  push_cast
  ring

end RawRat

lemma primrec_pow : Primrec₂ (fun a n : ℕ=>a^n) := by
  have h : Primrec₂ (fun a n : ℕ=> Nat.rec (motive := fun _ => ℕ) 1 (fun _ r=>r*a) n) :=
    Primrec.nat_rec (Primrec.const 1) ((Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂)
  apply h.of_eq
  intro a n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih,pow_succ]

lemma primrec_factorial : Primrec Nat.factorial := by
  have h : Primrec (Nat.rec 1 (fun n r=> (n+1)*r)) :=
    Primrec.nat_rec₁ 1 ((Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂)
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih,Nat.factorial_succ]

end MinUncut.Preprocess

namespace MinUncut.Preprocess

lemma primrec_gcd : Primrec₂ Nat.gcd := by
  have hd : PrimrecRel (fun a b : ℕ=>a ∣ b) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
      (by intro p; exact Nat.dvd_iff_mod_eq_zero.symm)
  have hf : Primrec (fun p : ℕ × ℕ => Nat.findGreatest (fun k=>k∣p.1 ∧ k∣p.2) p.2) :=
    Primrec.nat_findGreatest Primrec.snd
      ((hd.comp Primrec.snd (Primrec.fst.comp Primrec.fst)).and
       (hd.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
  apply (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst hf).to₂.of_eq
  intro m n
  by_cases hn : n=0
  · simp [hn]
  · simp only [hn,ite_false]
    have hgn : m.gcd n≤n := Nat.gcd_le_right m (by omega)
    have hdvd : (Nat.findGreatest (fun k=>k∣m ∧ k∣n) n) ∣ m.gcd n := by
      have hh := Nat.findGreatest_spec (P:=fun k=>k∣m ∧ k∣n) hgn ⟨Nat.gcd_dvd_left m n,Nat.gcd_dvd_right m n⟩
      exact Nat.dvd_gcd hh.1 hh.2
    apply Nat.le_antisymm
    · exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_right m (by omega)) hdvd
    · exact Nat.le_findGreatest hgn ⟨Nat.gcd_dvd_left m n,Nat.gcd_dvd_right m n⟩

lemma primrec_intCode : Primrec (Equiv.intEquivNat : ℤ → ℕ) := Primrec.encode

lemma intCode_nat (n : ℕ) : Equiv.intEquivNat (Int.ofNat n)=2*n := by
  rfl
lemma intCode_negSucc (n : ℕ) : Equiv.intEquivNat (Int.negSucc n)=2*n+1 := by
  simp [Equiv.intEquivNat,Equiv.intEquivNatSumNat]

lemma primrec_intAbs : Primrec Int.natAbs := by
  apply (Primrec.nat_div.comp (Primrec.succ.comp primrec_intCode) (Primrec.const 2)).of_eq
  intro z
  cases z with
  | ofNat n => rw [intCode_nat]; change (2*n).succ/2=n; omega
  | negSucc n => rw [intCode_negSucc]; simp only [Int.natAbs_negSucc]; omega

lemma primrec_intToNat : Primrec Int.toNat := by
  apply (Primrec.ite (Primrec.eq.comp
      (Primrec.nat_mod.comp primrec_intCode (Primrec.const 2)) (Primrec.const 0))
      (Primrec.nat_div.comp primrec_intCode (Primrec.const 2)) (Primrec.const 0)).of_eq
  intro z
  cases z with
  | ofNat n => rw [intCode_nat]; simp
  | negSucc n => rw [intCode_negSucc]; simp

lemma primrec_intNegToNat : Primrec (fun z : ℤ=>(-z).toNat) := by
  apply (Primrec.ite (Primrec.eq.comp
      (Primrec.nat_mod.comp primrec_intCode (Primrec.const 2)) (Primrec.const 0))
      (Primrec.const 0)
      (Primrec.succ.comp (Primrec.nat_div.comp primrec_intCode (Primrec.const 2)))).of_eq
  intro z
  cases z with
  | ofNat n => rw [intCode_nat]; simp
  | negSucc n => rw [intCode_negSucc]; simp; omega

abbrev RationalPair := {p : ℤ × ℕ // 0<p.2 ∧ p.1.natAbs.Coprime p.2}
lemma rationalPair_prim : PrimrecPred (fun p : ℤ × ℕ=>0<p.2 ∧ p.1.natAbs.Coprime p.2) := by
  exact (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd).and
    ((Primrec.eq.comp (primrec_gcd.comp (primrec_intAbs.comp Primrec.fst) Primrec.snd)
      (Primrec.const 1)).of_eq (by intro p; rfl))

instance rationalPairPrimcodable : Primcodable RationalPair := Primcodable.subtype rationalPair_prim

def rationalEquiv : ℚ ≃ RationalPair where
  toFun q := ⟨(q.num,q.den),Rat.den_pos q,q.reduced⟩
  invFun p := ⟨p.val.1,p.val.2,by exact Nat.ne_of_gt p.prop.1,p.prop.2⟩
  left_inv q := rfl
  right_inv p := rfl

instance rationalPrimcodable : Primcodable ℚ := Primcodable.ofEquiv RationalPair rationalEquiv

lemma primrec_ratNum : Primrec Rat.num :=
  Primrec.fst.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e:=rationalEquiv)))
lemma primrec_ratDen : Primrec Rat.den :=
  Primrec.snd.comp (Primrec.subtype_val.comp (Primrec.of_equiv (e:=rationalEquiv)))

open Encodable
local instance instEncodableRat_solutions : Encodable ℚ := rationalPrimcodable.toEncodable

end MinUncut.Preprocess

section
attribute [fun_prop] Computable ComputablePred

namespace MinUncut.Preprocess
variable {α : Type} [Primcodable α]

@[fun_prop] lemma ca_id : Computable (fun a : α=>a) := Computable.id
@[fun_prop] lemma ca_const {β : Type} [Primcodable β] (b : β) : Computable (fun _ : α=>b) := Computable.const b
@[fun_prop] lemma ca_fst {β : Type} [Primcodable β] : Computable (Prod.fst : α × β → α) := Computable.fst
@[fun_prop] lemma ca_snd {β : Type} [Primcodable β] : Computable (Prod.snd : α × β → β) := Computable.snd
@[fun_prop] lemma ca_comp {β γ : Type} [Primcodable β] [Primcodable γ] {g : β → γ} {f : α → β}
    (hg : Computable g) (hf : Computable f) : Computable (fun x=>g (f x)) := hg.comp hf
@[fun_prop] lemma ca_pair {β γ : Type} [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x=>(f x,g x)) := hf.pair hg
@[fun_prop] lemma ca_add {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x+g x) :=
  Primrec.nat_add.to_comp.comp hf hg
@[fun_prop] lemma ca_sub {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x-g x) :=
  Primrec.nat_sub.to_comp.comp hf hg
@[fun_prop] lemma ca_mul {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x*g x) :=
  Primrec.nat_mul.to_comp.comp hf hg
@[fun_prop] lemma ca_pow {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x^g x) :=
  primrec_pow.to_comp.comp hf hg
@[fun_prop] lemma ca_div {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x/g x) :=
  Primrec.nat_div.to_comp.comp hf hg
@[fun_prop] lemma ca_mod {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x%g x) :=
  Primrec.nat_mod.to_comp.comp hf hg
@[fun_prop] lemma ca_factorial {f : α → ℕ} (hf : Computable f) : Computable (fun x=>(f x).factorial) :=
  primrec_factorial.to_comp.comp hf

@[fun_prop] lemma ca_and {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun x=>p x ∧ q x) := by
  rcases hp with ⟨dp,hp⟩
  rcases hq with ⟨dq,hq⟩
  apply Computable.computablePred
  exact (Primrec.and.to_comp.comp hp hq).of_eq (by intro x; simp)
@[fun_prop] lemma ca_natLe {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x≤g x) :=
  (Primrec.nat_le.computablePred.decide.comp (hf.pair hg)).computablePred
@[fun_prop] lemma ca_natLt {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x<g x) :=
  (Primrec.nat_lt.computablePred.decide.comp (hf.pair hg)).computablePred
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianSmallBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open scoped BigOperators Topology
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

def evenExp (r : ℕ) (u : ℝ) : ℝ := ∑ j ∈ Finset.range (2*r+1), (-u)^j/(j.factorial:ℝ)

def densityPolynomial (r : ℕ) (v : ℝ) : ℝ := evenExp r (v^2/2)

def error (r : ℕ) (U : ℝ) : ℝ := U^(2*r+1)/((2*r+1).factorial:ℝ)

lemma taylor_exp (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    taylorWithinEval Real.exp n (Set.uIcc 0 x) 0 x =
      ∑ j ∈ Finset.range (n+1), x^j/(j.factorial:ℝ) := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hx.symm)
    Real.contDiff_exp.contDiffAt (by simp)]
  simp [iteratedDeriv_eq_iterate,Real.iter_deriv_exp,div_eq_mul_inv,mul_comm]

lemma evenExp_error {u : ℝ} (hu : 0 ≤ u) (r : ℕ) :
    0 ≤ evenExp r u-Real.exp (-u) ∧
      evenExp r u-Real.exp (-u) ≤ error r u := by
  rcases hu.eq_or_lt with he|hu
  · subst u
    simp [evenExp,error,Finset.sum_range_succ']
  have hx : (0:ℝ) ≠ -u := by linarith
  obtain ⟨z,hz,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (f := Real.exp) (n := 2*r)
    hx (Real.contDiff_exp.contDiffOn)
  rw [taylor_exp (2*r) hx.symm] at he
  simp only [iteratedDeriv_eq_iterate,Real.iter_deriv_exp,sub_zero] at he
  have hz0 : z < 0 := by
    have hh := hz
    rw [Set.uIoo_of_ge (by linarith : -u ≤ 0)] at hh
    exact hh.2
  have hpow : (-u)^(2*r+1) = -(u^(2*r+1)) := by
    rw [pow_succ,pow_mul,neg_sq,pow_succ]
    ring
  rw [hpow] at he
  have heq : evenExp r u-Real.exp (-u)=Real.exp z*error r u := by
    dsimp [evenExp,error,Finset.sum_range_succ']
    linear_combination -he
  rw [heq]
  have herror : 0 ≤ error r u := by unfold error; positivity
  exact ⟨mul_nonneg (Real.exp_nonneg _) herror,
    by simpa only [one_mul] using (mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr hz0.le) herror)⟩

lemma density_positive (r : ℕ) (v : ℝ) : 0 < densityPolynomial r v := by
  have h := (evenExp_error (by positivity : 0 ≤ v^2/2) r).1
  have := Real.exp_pos (-(v^2/2))
  dsimp [densityPolynomial]
  linarith

lemma exists_error {U ε : ℝ} (hε : 0 < ε) : ∃ r : ℕ, error r U < ε := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop U
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (h.eventually_lt_const hε)
  refine ⟨N,?_⟩
  exact hN (2*N+1) (by omega)

open scoped BigOperators
open MeasureTheory

def coefficient (j : ℕ) : ℚ := (-1)^j/((2:ℚ)^j*j.factorial)
def primitive (r : ℕ) (v : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (2*r+1), coefficient j*v^(2*j+1)/(2*j+1)
def qIntegral (r : ℕ) (a b : ℚ) : ℚ := primitive r b-primitive r a

lemma density_sum (r : ℕ) (v : ℝ) :
    densityPolynomial r v=∑ j ∈ Finset.range (2*r+1), (coefficient j:ℝ)*v^(2*j) := by
  unfold densityPolynomial evenExp
  apply Finset.sum_congr rfl
  intro j _
  unfold coefficient
  push_cast
  rw [neg_eq_neg_one_mul,mul_pow,div_pow,pow_mul]
  ring

lemma continuous_density (r : ℕ) : Continuous (densityPolynomial r) := by
  simp_rw [funext (density_sum r)]
  fun_prop

lemma qIntegral_cast (r : ℕ) (a b : ℚ) :
    (qIntegral r a b:ℝ)=∫ v in (a:ℝ)..(b:ℝ), densityPolynomial r v := by
  simp_rw [density_sum]
  rw [intervalIntegral.integral_finsetSum (f := fun (j : ℕ) (v : ℝ) => (coefficient j:ℝ)*v^(2*j))
    (fun j _ => (show Continuous (fun v : ℝ => (coefficient j:ℝ)*v^(2*j)) by fun_prop).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul,integral_pow]
  unfold qIntegral primitive
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma qIntegral_pos (r : ℕ) {a b : ℚ} (hab : a < b) : 0 < qIntegral r a b := by
  apply (Rat.cast_pos (K := ℝ)).mp
  rw [qIntegral_cast]
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  exact intervalIntegral.integral_pos hab' (continuous_density r).continuousOn
    (fun v _ => (density_positive r v).le) ⟨a,⟨le_rfl,hab'.le⟩,density_positive r a⟩

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianQuadrature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.FiniteGaussian

def qError (r : ℕ) (U : ℚ) : ℚ := U^(2*r+1)/(2*r+1).factorial

lemma qError_cast (r : ℕ) (U : ℚ) : (qError r U:ℝ)=error r U := by
  unfold qError error
  push_cast
  rfl

structure GridData where
  T : ℕ
  L : ℕ
  r : ℕ
  deriving DecidableEq, Encodable

namespace GridData

def Check (d S : ℕ) (A ε : ℚ) (g : GridData) : Prop :=
  1 ≤ g.T ∧ 1 ≤ g.L ∧ (d:ℚ)/(g.T:ℚ)^2 < ε/4 ∧
    2*(S:ℚ)*A*g.T/g.L < ε/4 ∧
    2*(d:ℚ)*g.T*qError g.r ((g.T:ℚ)^2/2) < ε/4

instance instDecidableCheck (d S : ℕ) (A ε : ℚ) (g : GridData) : Decidable (Check d S A ε g) := by
  unfold Check; infer_instance

lemma exists_check (d S : ℕ) {A ε : ℚ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ g : GridData, g.Check d S A ε := by
  obtain ⟨T,hT⟩ := exists_nat_gt (4*(d:ℚ)/ε+1)
  have hnonnegT : 0 ≤ 4*(d:ℚ)/ε := by positivity
  have hT1 : (1:ℚ)<T := lt_of_le_of_lt (by linarith : 1 ≤ 4*(d:ℚ)/ε+1) hT
  have hTpos : (0:ℚ)<T := by linarith
  have hTnat : 1 ≤ T := by exact_mod_cast hT1.le
  have hT2 : (T:ℚ) ≤ (T:ℚ)^2 := by nlinarith
  have htail : (d:ℚ)/(T:ℚ)^2 < ε/4 := by
    have hh : 4*(d:ℚ) < ε*T := by
      have hh : 4*(d:ℚ)/ε < (T:ℚ) := by linarith
      have := (div_lt_iff₀ hε).mp hh
      nlinarith
    apply (div_lt_iff₀ (sq_pos_of_pos hTpos)).mpr
    have := mul_le_mul_of_nonneg_left hT2 hε.le
    nlinarith
  obtain ⟨L,hL⟩ := exists_nat_gt (8*(S:ℚ)*A*T/ε+1)
  have hnonnegL : 0 ≤ 8*(S:ℚ)*A*T/ε := by positivity
  have hL1 : (1:ℚ)<L := lt_of_le_of_lt (by linarith : 1 ≤ 8*(S:ℚ)*A*T/ε+1) hL
  have hLpos : (0:ℚ)<L := by linarith
  have hLnat : 1 ≤ L := by exact_mod_cast hL1.le
  have hmesh : 2*(S:ℚ)*A*T/L < ε/4 := by
    have hh : 8*(S:ℚ)*A*T < ε*L := by
      have hh : 8*(S:ℚ)*A*T/ε < (L:ℚ) := by linarith
      have := (div_lt_iff₀ hε).mp hh
      nlinarith
    apply (div_lt_iff₀ hLpos).mpr
    nlinarith
  have hden : 0 < 4*(2*(d:ℚ)*T+1) := by positivity
  obtain ⟨r,hr⟩ := exists_error (U := (((T:ℚ)^2/2:ℚ):ℝ))
    (by exact_mod_cast (div_pos hε hden) : (0:ℝ) < (ε/(4*(2*(d:ℚ)*T+1)):ℚ))
  have hr' : qError r ((T:ℚ)^2/2) < ε/(4*(2*(d:ℚ)*T+1)) := by
    exact_mod_cast (show (qError r ((T:ℚ)^2/2):ℝ) < (ε/(4*(2*(d:ℚ)*T+1)):ℚ) by
      rw [qError_cast]; exact hr)
  have herr : 0 ≤ qError r ((T:ℚ)^2/2) := by unfold qError; positivity
  refine ⟨⟨T,L,r⟩,hTnat,hLnat,htail,hmesh,?_⟩
  change 2*(d:ℚ)*T*qError r ((T:ℚ)^2/2) < ε/4
  have hh := (lt_div_iff₀ hden).mp hr'
  nlinarith

def select (d S : ℕ) (A ε : ℚ) (hA : 0 ≤ A) (hε : 0 < ε) : GridData :=
  Encodable.choose (exists_check d S hA hε)

lemma select_check (d S : ℕ) (A ε : ℚ) (hA : 0 ≤ A) (hε : 0 < ε) :
    (select d S A ε hA hε).Check d S A ε :=
  Encodable.choose_spec (exists_check d S hA hε)

end GridData
end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_RationalRowNoise
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.RowNoise
attribute [local instance] Classical.propDecidable
variable {R W : Type*} [Fintype R] [Fintype W] [DecidableEq W]

def rationalRowDensity (a : ℚ) (b c : W) : ℚ :=
  (1-a)*(if c=b then (Fintype.card W:ℚ) else 0)+a

def rationalDensity (a : ℚ) (B C : R → W) : ℚ :=
  ∏ r, rationalRowDensity a (B r) (C r)

lemma rationalDensity_nonneg {a : ℚ} (ha : 0≤a) (ha1 : a≤1) (B C : R → W) :
    0 ≤ rationalDensity a B C := by
  apply Finset.prod_nonneg
  intro r _
  unfold rationalRowDensity
  split_ifs <;> positivity

end MinUncut.RowNoise

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_AlgebraicSigns
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.FiniteGaussian

def algebraicNonneg (a b : ℚ) (N : ℕ) : Bool :=
  if 0 ≤ b then
    if 0 ≤ a then true else decide (a^2 ≤ (N:ℚ)*b^2)
  else
    if a < 0 then false else decide ((N:ℚ)*b^2 ≤ a^2)

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_Parameters
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sourceSigma (J : ℝ) : ℝ := 1/(2560*J)
def sourceEta (J : ℝ) : ℝ := (sourceSigma J)^2/(2560*J)
def sourceR (J : ℝ) : ℕ := ⌈(sourceEta J)⁻¹^2⌉₊
def sourceT (J : ℝ) : ℕ := ⌈32*J/(sourceEta J*(sourceSigma J)^4)⌉₊

lemma sourceSigma_pos {J : ℝ} (hJ : 1 ≤ J) : 0 < sourceSigma J := by
  unfold sourceSigma
  positivity
lemma sourceEta_pos {J : ℝ} (hJ : 1 ≤ J) : 0 < sourceEta J := by
  unfold sourceEta
  have hs := sourceSigma_pos hJ
  positivity
lemma sourceSigma_le_one {J : ℝ} (hJ : 1 ≤ J) : sourceSigma J ≤ 1 := by
  unfold sourceSigma
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2560*J)).mpr
  linarith
lemma sourceEta_le_sigma {J : ℝ} (hJ : 1 ≤ J) : sourceEta J ≤ sourceSigma J := by
  have hs := sourceSigma_pos hJ
  have hs1 := sourceSigma_le_one hJ
  have hJpos : 0 < J := by linarith
  unfold sourceEta
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 2560*J)).mpr
  nlinarith
lemma sourceR_bound {J : ℝ} (hJ : 1 ≤ J) : 1 ≤ (sourceR J:ℝ)*(sourceEta J)^2 := by
  have hη := sourceEta_pos hJ
  have hh := Nat.le_ceil ((sourceEta J)⁻¹^2)
  have hw := mul_le_mul_of_nonneg_right hh (sq_nonneg (sourceEta J))
  have he : (sourceEta J)⁻¹^2*(sourceEta J)^2=1 := by field_simp
  simpa only [he,sourceR] using hw
lemma sourceT_pos {J : ℝ} (hJ : 1 ≤ J) : 0 < sourceT J := by
  apply Nat.ceil_pos.mpr
  have hη := sourceEta_pos hJ
  have hσ := sourceSigma_pos hJ
  positivity
lemma sourceT_bound {J : ℝ} (hJ : 1 ≤ J) :
    32*J ≤ (sourceT J:ℝ)*sourceEta J*(sourceSigma J)^4 := by
  have hη := sourceEta_pos hJ
  have hσ := sourceSigma_pos hJ
  have hh := Nat.le_ceil (32*J/(sourceEta J*(sourceSigma J)^4))
  exact (div_le_iff₀ (by positivity)).mp hh |>.trans_eq (by unfold sourceT; ring)

lemma source_row_rate {J : ℝ} (hJ : 1 ≤ J) {m : ℕ} (hm : 0 < m) :
    0 ≤ (sourceEta J)^2/(m:ℝ) ∧ (sourceEta J)^2/(m:ℝ) ≤ 1 ∧
    ∀ k : ℕ, sourceR J*m < k → 1 ≤ (k:ℝ)*((sourceEta J)^2/(m:ℝ)) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hetapos := sourceEta_pos hJ
  have heta1 : sourceEta J ≤ 1 := (sourceEta_le_sigma hJ).trans (sourceSigma_le_one hJ)
  refine ⟨by positivity,?_,?_⟩
  · apply (div_le_iff₀ hm').mpr
    nlinarith
  · intro k hk
    have hk' : (sourceR J:ℝ)*(m:ℝ) ≤ k := by exact_mod_cast hk.le
    have hh := mul_le_mul_of_nonneg_right hk' (show 0 ≤ (sourceEta J)^2/(m:ℝ) by positivity)
    have he : (sourceR J:ℝ)*(m:ℝ)*((sourceEta J)^2/(m:ℝ)) =
        (sourceR J:ℝ)*(sourceEta J)^2 := by field_simp
    rw [he] at hh
    exact (sourceR_bound hJ).trans hh
end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Assembly
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*}
  [AddCommGroup V]
  [AddTorsor V A]
  [Fintype A]
variable {m n : ℕ}

open MeasureTheory ProbabilityTheory RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {V A : Type*}
  [AddCommGroup V]
  [AddTorsor V A]
  [Fintype A]
variable {m n : ℕ}

open MeasureTheory ProbabilityTheory RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {Ξ : Type*}
  [Fintype Ξ]
  (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)]
  [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)]
  {m n : ℕ}

open MeasureTheory ProbabilityTheory RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

lemma exists_dimension (R s : ℕ) : ∃ m : ℕ, 2 ≤ m ∧ s+1 < m ∧ R*m < (m-s).choose 2 := by
  let m := 4*(R+s+1)
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hs : s+1 < m := by dsimp [m]; omega
  have ha : m-s = 4*R+3*s+4 := by dsimp [m]; omega
  have hb : m-s-1 = 4*R+3*s+3 := by omega
  have hprod : 2*(R*m+1) ≤ (m-s)*(m-s-1) := by
    rw [hb,ha]
    dsimp [m]
    nlinarith
  refine ⟨m,hm,hs,?_⟩
  rw [Nat.choose_two_right]
  omega

lemma exists_positive_nat_div_lt {E e : ℝ} (he : 0 < e) :
    ∃ H : ℕ, 0 < H ∧ E/(H:ℝ) < e := by
  obtain ⟨H,hH⟩ := exists_nat_gt (max 0 (E/e))
  have hH0 : (0:ℝ) < H := lt_of_le_of_lt (le_max_left _ _) hH
  have hEH : E < e*(H:ℝ) := by
    have := (div_lt_iff₀ he).mp (lt_of_le_of_lt (le_max_right _ _) hH)
    linarith
  exact ⟨H,by exact_mod_cast hH0,(div_lt_iff₀ hH0).mpr hEH⟩

lemma exists_reciprocal_processing {E e : ℝ} (he : 0 < e) :
    ∃ (H A₀ : ℕ) (γ : ℚ), 0 < H ∧ 0 < A₀ ∧ 0 < (γ:ℝ) ∧ (γ:ℝ) < 1 ∧
      E/(H:ℝ) < e ∧ 2*E/(A₀:ℝ) < e ∧
      Real.sqrt ((H:ℝ)*((γ:ℝ)+(H:ℝ)^2/(A₀:ℝ))) < e := by
  obtain ⟨H,hH,hHbound⟩ := exists_positive_nat_div_lt (E := E) he
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  obtain ⟨γ,hγ,hγub⟩ := exists_rat_btwn (show (0:ℝ) < min 1 (e^2/(4*(H:ℝ))) by positivity)
  have hg1 := (lt_min_iff.mp hγub).1
  have hgE : (H:ℝ)*(γ:ℝ) < e^2/4 := by
    have hh := (lt_div_iff₀ (show (0:ℝ) < 4*(H:ℝ) by positivity)).mp (lt_min_iff.mp hγub).2
    nlinarith
  obtain ⟨A₀,hA⟩ := exists_nat_gt (max 0 (max (2*E/e) (4*(H:ℝ)^3/e^2)))
  have hAr : (0:ℝ) < A₀ := lt_of_le_of_lt (le_max_left _ _) hA
  have hAE : 2*E/(A₀:ℝ) < e := by
    apply (div_lt_iff₀ hAr).mpr
    have hh := (div_lt_iff₀ he).mp (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hA)
    linarith
  have hAH : (H:ℝ)^3/(A₀:ℝ) < e^2/4 := by
    have hh := (div_lt_iff₀ (show 0 < e^2 by positivity)).mp
      (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hA)
    apply (div_lt_iff₀ hAr).mpr
    nlinarith
  refine ⟨H,A₀,γ,hH,by exact_mod_cast hAr,hγ,hg1,hHbound,hAE,?_⟩
  apply Real.sqrt_lt' he |>.mpr
  have heq : (H:ℝ)*((γ:ℝ)+(H:ℝ)^2/(A₀:ℝ)) = (H:ℝ)*(γ:ℝ)+(H:ℝ)^3/(A₀:ℝ) := by ring
  rw [heq]
  nlinarith

lemma exists_box_scale (m : ℕ) {A₀ e : ℝ} (hA : 0 < A₀) (he : 0 < e) :
    ∃ k : ℕ, 1 ≤ k ∧ 2*A₀*((m:ℝ)/(k+1))^(((2^m:ℕ):ℝ)⁻¹) < e := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 ((m:ℝ)/(e/(2*A₀))^(2^m)))
  have hk1 : (1:ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hk0 : (0:ℝ) < (k:ℝ)+1 := by linarith
  have hq : (m:ℝ)/(e/(2*A₀))^(2^m) < (k:ℝ)+1 :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hk) (by linarith)
  have hratio : (m:ℝ)/((k:ℝ)+1) < (e/(2*A₀))^(2^m) := by
    apply (div_lt_iff₀ hk0).mpr
    have hh := (div_lt_iff₀ (show (0:ℝ) < (e/(2*A₀))^(2^m) by positivity)).mp hq
    linarith
  have hroot : ((m:ℝ)/((k:ℝ)+1))^(((2^m:ℕ):ℝ)⁻¹) < e/(2*A₀) := by
    apply (Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity) (by positivity)).mpr
    rwa [Real.rpow_natCast]
  refine ⟨k,by exact_mod_cast hk1.le,?_⟩
  simpa only [mul_comm] using (lt_div_iff₀ (show 0 < 2*A₀ by positivity)).mp hroot

lemma exists_ambient_scale (s D k : ℕ) {σ e : ℝ} (hσ : 0 < σ) (he : 0 < e) :
    ∃ n : ℕ, k+2 ≤ n ∧ σ⁻¹*Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) < e := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (k+2:ℝ) (((s+D:ℕ):ℝ)*(k:ℝ)/(e*σ)^2+1))
  have hnK : (k:ℝ)+2 < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0:ℝ) < (n:ℝ)-1 := by have : (0:ℝ) ≤ k := Nat.cast_nonneg _; linarith
  have hnB : ((s+D:ℕ):ℝ)*(k:ℝ)/(e*σ)^2 < (n:ℝ)-1 := by
    have := lt_of_le_of_lt (le_max_right _ _) hn
    linarith
  have hr : ((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1)) < (e*σ)^2 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hn0).mpr
    have := (div_lt_iff₀ (show 0 < (e*σ)^2 by positivity)).mp hnB
    linarith
  have hh := (Real.sqrt_lt' (show 0 < e*σ by positivity)).mpr hr
  refine ⟨n,?_,?_⟩
  · exact_mod_cast hnK.le
  · calc
      _ = Real.sqrt (((s+D:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1)))/σ := by ring
      _ < e := (div_lt_iff₀ hσ).mpr hh

lemma exists_small_rational_atoms {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    ∃ p θ : ℚ, 0 < (p:ℝ) ∧ (p:ℝ) < 1 ∧ 0 < (θ:ℝ) ∧ (θ:ℝ) < 1 ∧
      (θ:ℝ)^2+L*(p:ℝ) < B := by
  obtain ⟨θ,hθ,hθb⟩ := exists_rat_btwn (show (0:ℝ) < min 1 (B/4) by positivity)
  obtain ⟨p,hp,hpb⟩ := exists_rat_btwn (show (0:ℝ) < min 1 (B/(4*L)) by positivity)
  obtain ⟨hθ1,hθB⟩ := lt_min_iff.mp hθb
  obtain ⟨hp1,hpB⟩ := lt_min_iff.mp hpb
  have hLp : L*(p:ℝ) < B/4 := by
    have hh := (lt_div_iff₀ (show 0 < 4*L by positivity)).mp hpB
    nlinarith
  exact ⟨p,θ,hp,hp1,hθ,hθ1,by nlinarith⟩

lemma nested_atom_lt {σ e γ C Q : ℝ} (hσ : 0 < σ) (he : 0 < e) (hγ : 0 < γ) (hC : 0 < C)
    (hQ : Q < (e^2*σ^2*γ/C)^2) :
    Real.sqrt (σ⁻¹^2)*Real.sqrt (C*Real.sqrt Q/γ) < e := by
  have h1 := (Real.sqrt_lt' (show 0 < e^2*σ^2*γ/C by positivity)).mpr hQ
  have h2 : C*Real.sqrt Q/γ < (e*σ)^2 := by
    have hh := (lt_div_iff₀ hC).mp h1
    apply (div_lt_iff₀ hγ).mpr
    nlinarith
  have h3 := (Real.sqrt_lt' (show 0 < e*σ by positivity)).mpr h2
  rw [Real.sqrt_sq (by positivity : 0 ≤ σ⁻¹)]
  rw [mul_comm,← div_eq_mul_inv]
  exact (div_lt_iff₀ hσ).mpr h3
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_SignedGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.FiniteProof

def orient (b x : Bool) : Bool := if b then x else !x

def rep {A : Type*} (a : A) (P : A → Bool) : {R : A → Bool // R a=true} :=
  ⟨fun x => P a == P x, by simp⟩

lemma rep_not {A : Type*} (a : A) (P : A → Bool) :
    rep a (fun x => !(P x))=rep a P := by
  apply Subtype.ext
  funext x
  simp [rep]

variable {Q : Type*} {A : Q → Type*} (base : ∀ q, A q)

abbrev Query := Σ q, A q → Bool
abbrev Variable := Σ q, {R : A q → Bool // R (base q)=true}

def vertex (p : Query (A := A)) : Variable base := ⟨p.1,rep (base p.1) p.2⟩

def answer (y : Variable base → Bool) (q : Q) (P : A q → Bool) : Bool :=
  orient (P (base q)) (y (vertex base ⟨q,P⟩))

def Folded (f : ∀ q, (A q → Bool) → Bool) : Prop :=
  ∀ q P, f q (fun x => !(P x))= !(f q P)

lemma answer_folded (y : Variable base → Bool) : Folded (answer base y) := by
  intro q P
  simp only [answer,vertex,rep_not]
  cases h : P (base q) <;> simp [orient]

structure QueryDemand where
  left : Query (A := A)
  right : Query (A := A)
  equal : Bool

def QueryDemand.failure (d : QueryDemand (A := A))
    (f : ∀ q, (A q → Bool) → Bool) : ℕ :=
  if (f d.left.1 d.left.2 == f d.right.1 d.right.2)=d.equal then 0 else 1

end MinUncut.FiniteProof

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace MinUncut.FiniteProof
variable {E V : Type*} [Fintype E]

def multiplicity (D : ℕ) (w : ℚ) : ℕ := w.num.toNat*(D/w.den)

lemma multiplicity_cast {D : ℕ} {w : ℚ} (hw : 0≤w) (hD : w.den ∣ D) :
    (multiplicity D w:ℚ)=(D:ℚ)*w := by
  have hn : 0≤w.num := Rat.num_nonneg.mpr hw
  have hncast : (w.num.toNat:ℚ)=(w.num:ℚ) := by exact_mod_cast Int.toNat_of_nonneg hn
  calc
    (multiplicity D w:ℚ)=(w.num:ℚ)*((D:ℚ)/(w.den:ℚ)) := by
      unfold multiplicity
      rw [Nat.cast_mul,Nat.cast_div_charZero hD,hncast]
    _ = (D:ℚ)*((w.num:ℚ)/(w.den:ℚ)) := by ring
    _ = (D:ℚ)*w := by rw [Rat.num_div_den]

abbrev UnitDemand (D : ℕ) (w : E → ℚ) := Σ e, Fin (multiplicity D (w e))


open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V]

lemma threshold_positive {D : ℕ} (hD : 0<D) : 1≤5*D := by omega

end MinUncut.FiniteProof

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_InnerUniform
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner

lemma uniformWeight_sum {Ξ : Type*} [Fintype Ξ] (F : Ξ → ℝ) :
    (∑ ξ, (Fintype.card Ξ:ℝ)⁻¹*F ξ) = 𝔼 ξ,F ξ := by
  rw [← Finset.mul_sum,Fintype.expect_eq_sum_div_card]
  ring

end MinUncut.Inner

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_OuterParameters
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner

lemma exists_list_scale (M u θ : ℝ) (q : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ k : ℕ, listTerm M u θ q k < ε := by
  let C : ℝ := (⌈M^2/u^2⌉₊ : ℝ)*(⌈M^2/θ^2⌉₊ : ℝ)
  have hC : 0≤C := by dsimp [C]; positivity
  obtain ⟨k,hk⟩ := shared_hint_rate_vanishes q (show 0<ε/(C+1) by positivity)
  refine ⟨k,?_⟩
  have hr := pow_nonneg (hintRate_nonnegative q) k
  have hx := (lt_div_iff₀ (show 0<C+1 by positivity)).mp hk
  change C*hintRate q^k<ε
  nlinarith

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ComparisonSoundness
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

inductive Test | first | second | third | fourth deriving DecidableEq
instance instFintypeTest : Fintype Test where
  elems := {.first,.second,.third,.fourth}
  complete := by intro j; cases j <;> simp

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LiftedVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.GaussianBudget
attribute [local instance] Classical.propDecidable
variable {X C : Type*} [Fintype X] [Fintype C]

abbrev Coordinates (X C : Type*) := X ⊕ (X ⊕ C)

def liftVector (v : X → ℝ) (σ η : ℝ) (z : C) : Coordinates X C → ℝ
  | .inl x => v x
  | .inr (.inl x) => σ*v x
  | .inr (.inr c) => if c=z then η else 0

end MinUncut.GaussianBudget

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TableTestFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {V A V' A' : Type*}
  [AddCommGroup V]
  [AddTorsor V A]
  [Fintype A]
  [AddCommGroup V']
  [AddTorsor V' A']
  [Fintype A']
  {m n : ℕ}

def disagreement (b c : Bool) : ℝ := if b=c then 0 else 1

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_WeightedTestLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable 
variable {Name I : Type*} [Fintype I] {m n : ℕ}

lemma sum_invcard_mul {X : Type*} [Fintype X] (f : X → ℝ) :
    (∑ x, (Fintype.card X:ℝ)⁻¹*f x)=𝔼 x, f x := by
  rw [← Finset.mul_sum,Fintype.expect_eq_sum_div_card,mul_comm,div_eq_mul_inv]

end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable 
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n k : ℕ}

lemma expect_prod_type {X Y : Type*} [Fintype X] [Fintype Y] (f : X × Y → ℝ) :
    (𝔼 p, f p)=𝔼 x, 𝔼 y, f (x,y) := by
  simp only [Fintype.expect_eq_sum_div_card,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    Finset.sum_div,div_div]
  rw [mul_comm (Fintype.card X:ℝ)]

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Inner
open scoped BigOperators
open GaussianHermite RowNoise

def rationalSigma (J : ℕ) : ℚ := 1/(2560*(J:ℚ))
def rationalEta (J : ℕ) : ℚ := rationalSigma J^2/(2560*(J:ℚ))
def rationalR (J : ℕ) : ℕ := ⌈(rationalEta J)⁻¹^2⌉₊
def rationalT (J : ℕ) : ℕ := ⌈32*(J:ℚ)/(rationalEta J*rationalSigma J^4)⌉₊

lemma ceil_rat_real (q : ℚ) : ⌈(q:ℝ)⌉₊=⌈q⌉₊ := by
  apply Nat.le_antisymm
  · exact Nat.ceil_le.mpr (by exact_mod_cast Nat.le_ceil q)
  · exact Nat.ceil_le.mpr (by exact_mod_cast Nat.le_ceil (q:ℝ))

@[simp] lemma rationalSigma_cast (J : ℕ) : (rationalSigma J:ℝ)=sourceSigma J := by
  simp [rationalSigma,sourceSigma]
@[simp] lemma rationalEta_cast (J : ℕ) : (rationalEta J:ℝ)=sourceEta J := by
  simp [rationalEta,sourceEta]
@[simp] lemma rationalR_eq (J : ℕ) : rationalR J=sourceR J := by
  simp only [rationalR,sourceR,← rationalEta_cast J,← Rat.cast_inv,← Rat.cast_pow,ceil_rat_real]
@[simp] lemma rationalT_eq (J : ℕ) : rationalT J=sourceT J := by
  rw [rationalT,sourceT,← ceil_rat_real]
  congr 1
  simp

lemma rho_even (σ : ℝ) (t : ℕ) : (smoothingRho σ)^(2*t)=((1+σ^2)⁻¹)^t := by
  rw [pow_mul]
  congr 1
  unfold smoothingRho
  rw [inv_pow,Real.sq_sqrt (by positivity)]

lemma cutoff_tail {r : ℝ} (hr : 0 ≤ r) {s : ℕ}
    (hstep : ((s:ℝ)+3)*r ≤ (s:ℝ)+2) (hbase : ((s:ℝ)+2)*r^(s+2) ≤ 1/16) :
    ∀ t : ℕ, s+2 ≤ t → (t:ℝ)*r^t ≤ 1/16 := by
  have hr1 : r ≤ 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) s]
  intro t ht
  induction t,ht using Nat.le_induction with
  | base => simpa only [Nat.cast_add,Nat.cast_ofNat] using hbase
  | succ t ht ih =>
    have ht' : (s:ℝ)+2 ≤ t := by exact_mod_cast ht
    have hd : ((t:ℝ)+1)*r ≤ t := by nlinarith
    calc
      ((t+1:ℕ):ℝ)*r^(t+1) = (((t:ℝ)+1)*r)*r^t := by push_cast; rw [pow_succ]; ring
      _ ≤ (t:ℝ)*r^t := mul_le_mul_of_nonneg_right hd (pow_nonneg hr _)
      _ ≤ _ := ih

lemma exists_finite_cutoff {σ : ℝ} (hσ : 0 < σ) :
    ∃ s : ℕ, ((s:ℝ)+3)*(1+σ^2)⁻¹ ≤ (s:ℝ)+2 ∧
      ((s:ℝ)+2)*((1+σ^2)⁻¹)^(s+2) ≤ 1/16 := by
  obtain ⟨s,hs⟩ := exists_cutoff (smoothingRho_lt_one hσ.ne') (by norm_num : (0:ℝ) < 1/16)
  obtain ⟨a,ha⟩ := exists_nat_gt ((σ^2)⁻¹)
  refine ⟨max s a,?_,?_⟩
  · have hb : (a:ℝ)*σ^2 > 1 := by
      have := (div_lt_iff₀ (show 0 < σ^2 by positivity)).mp (show 1/σ^2 < a by simpa using ha)
      linarith
    have hc : (a:ℝ) ≤ max s a := by exact_mod_cast le_max_right s a
    apply (mul_inv_le_iff₀ (show 0 < 1+σ^2 by positivity)).mpr
    nlinarith [sq_nonneg σ]
  · have hh := hs (max s a+2) (by omega)
    rw [rho_even] at hh
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hh

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Inner
open GaussianHermite

structure InnerData where
  s : ℕ
  m : ℕ
  k : ℕ
  n : ℕ
  H : ℕ
  A : ℕ
  γ : ℚ
  p : ℚ
  θ : ℚ
  deriving DecidableEq, Encodable

namespace InnerData

def epsilon (J m : ℕ) : ℚ := 1/(40*(rationalT J:ℚ)*(m^2+1))
def atomConstant (s m n : ℕ) : ℕ := 4^(m*n^(m-1))*(n^m+s).choose s

def Check (J : ℕ) (d : InnerData) : Prop :=
  2 ≤ d.m ∧ d.k+2 ≤ d.n ∧ 1 ≤ d.k ∧ 0 < d.H ∧ 0 < d.A ∧
  0 < d.γ ∧ 0 < d.p ∧ d.p < 1 ∧ 0 < d.θ ∧ d.θ < 1 ∧
  ((d.s:ℚ)+3)*(1+rationalSigma J^2)⁻¹ ≤ (d.s:ℚ)+2 ∧
  ((d.s:ℚ)+2)*((1+rationalSigma J^2)⁻¹)^(d.s+2) ≤ 1/16 ∧
  rationalR J*d.m < (d.m-d.s).choose 2 ∧
  ((d.s+rationalR J*d.m:ℕ):ℚ)*(d.k:ℚ)/((d.n:ℚ)-1) < (epsilon J d.m*rationalSigma J)^2 ∧
  (rationalSigma J)⁻¹^2/(d.H:ℚ) < epsilon J d.m ∧
  2*(rationalSigma J)⁻¹^2/(d.A:ℚ) < epsilon J d.m ∧
  (d.m:ℚ)/((d.k:ℚ)+1) < (epsilon J d.m/(2*(d.A:ℚ)))^(2^d.m) ∧
  (d.H:ℚ)*(d.γ+(d.H:ℚ)^2/(d.A:ℚ)) < epsilon J d.m^2 ∧
  d.θ^2+(d.m:ℚ)*d.p*(d.n^d.m:ℕ)/(rationalSigma J)^2 <
    (epsilon J d.m^2*(rationalSigma J)^2*d.γ/(atomConstant d.s d.m d.n:ℚ))^2

instance instDecidableCheck (J : ℕ) (d : InnerData) : Decidable (Check J d) := by unfold Check; infer_instance

lemma epsilon_pos {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) : 0 < (epsilon J m:ℝ) := by
  have hT : (0:ℝ) < rationalT J := by
    rw [rationalT_eq]
    exact_mod_cast sourceT_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
  unfold epsilon
  push_cast
  positivity

end InnerData
end MinUncut.Inner

end
section
namespace MinUncut.Inner.InnerData
open MinUncut.Inner

lemma check_exists {J : ℕ} (hJ : 1 ≤ J) : ∃ d : InnerData, d.Check J := by
  have hJr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hσ := sourceSigma_pos hJr
  obtain ⟨s,hstep,hbase⟩ := exists_finite_cutoff hσ
  obtain ⟨m,hm,_,hroom⟩ := exists_dimension (sourceR J) s
  let e : ℝ := epsilon J m
  have he : 0 < e := epsilon_pos hJ m
  obtain ⟨H,A,γ,hH,hA,hγ,_,henergy,hclip,hfourth⟩ :=
    exists_reciprocal_processing (E := (sourceSigma J)⁻¹^2) he
  have hAr : (0:ℝ) < A := by exact_mod_cast hA
  obtain ⟨k,hk,hcollision⟩ := exists_box_scale m hAr he
  obtain ⟨n,hn,hloc⟩ := exists_ambient_scale s (sourceR J*m) k hσ he
  let C : ℝ := atomConstant s m n
  have hchoose : 0 < (n^m+s).choose s := Nat.choose_pos (by omega)
  have hC : 0 < C := by dsimp [C,atomConstant]; positivity
  let L : ℝ := (m:ℝ)*(n^m:ℕ)/(sourceSigma J)^2
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by omega
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨p,θ,hp,hp1,hθ,hθ1,hQ⟩ := exists_small_rational_atoms hL
    (show 0 < (e^2*(sourceSigma J)^2*(γ:ℝ)/C)^2 by positivity)
  have hloc' : (((s+sourceR J*m:ℕ):ℝ)*(k:ℝ)/((n:ℝ)-1)) < (e*sourceSigma J)^2 := by
    apply (Real.sqrt_lt' (show 0 < e*sourceSigma J by positivity)).mp
    have hx : Real.sqrt (((s+sourceR J*m:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1)))/sourceSigma J < e := by
      simpa only [div_eq_mul_inv,mul_comm] using hloc
    simpa only [mul_div_assoc] using (div_lt_iff₀ hσ).mp hx
  have hcol' : (m:ℝ)/((k:ℝ)+1) < (e/(2*(A:ℝ)))^(2^m) := by
    have hx : ((m:ℝ)/((k:ℝ)+1))^(((2^m:ℕ):ℝ)⁻¹) < e/(2*(A:ℝ)) :=
      (lt_div_iff₀ (show 0 < 2*(A:ℝ) by positivity)).mpr (by simpa only [mul_comm] using hcollision)
    have hh := (Real.rpow_inv_lt_iff_of_pos (by positivity : (0:ℝ) ≤ (m:ℝ)/((k:ℝ)+1))
      (by positivity : (0:ℝ) ≤ e/(2*(A:ℝ))) (by positivity : (0:ℝ) < (2^m:ℕ))).mp hx
    simpa only [Real.rpow_natCast] using hh
  have hfour' := (Real.sqrt_lt' he).mp hfourth
  have hat' : (θ:ℝ)^2+(m:ℝ)*(p:ℝ)*(n^m:ℕ)/(sourceSigma J)^2 <
      (e^2*(sourceSigma J)^2*(γ:ℝ)/C)^2 := by
    convert hQ using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [L]
    ring
  refine ⟨⟨s,m,k,n,H,A,γ,p,θ⟩,hm,hn,hk,hH,hA,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast hγ
  · exact_mod_cast hp
  · exact_mod_cast hp1
  · exact_mod_cast hθ
  · exact_mod_cast hθ1
  · rw [← rationalSigma_cast J] at hstep
    exact_mod_cast hstep
  · rw [← rationalSigma_cast J] at hbase
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hbase
  · simpa only [rationalR_eq] using hroom
  · rw [← rationalSigma_cast J,← rationalR_eq J] at hloc'
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    simpa only [e,Nat.cast_add,Nat.cast_mul] using hloc'
  · rw [← rationalSigma_cast J] at henergy
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact henergy
  · rw [← rationalSigma_cast J] at hclip
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact hclip
  · apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact hcol'
  · apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact hfour'
  · rw [← rationalSigma_cast J] at hat'
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    simpa only [e,C,Nat.cast_pow] using hat'

end MinUncut.Inner.InnerData

end
section
namespace MinUncut.Outer
open MinUncut.Inner

lemma listTerm_mono {M M' u θ : ℝ} (hM : 0 ≤ M) (hM' : M ≤ M') (q k : ℕ) :
    listTerm M u θ q k ≤ listTerm M' u θ q k := by
  have hsq : M^2 ≤ M'^2 := sq_le_sq₀ hM (hM.trans hM') |>.mpr hM'
  have h1 : ⌈M^2/u^2⌉₊ ≤ ⌈M'^2/u^2⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hsq (sq_nonneg u))
  have h2 : ⌈M^2/θ^2⌉₊ ≤ ⌈M'^2/θ^2⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hsq (sq_nonneg θ))
  unfold listTerm
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (hintRate_nonnegative q) k)
  exact mul_le_mul (by exact_mod_cast h1) (by exact_mod_cast h2) (by positivity) (by positivity)

lemma remainderTerm_mono {M M' u θ : ℝ} (hM : 0 ≤ M) (hM' : M ≤ M') (hu : 0 < u) (q k t : ℕ) :
    remainderTerm M u θ q k t ≤ remainderTerm M' u θ q k t := by
  have hsq : M^2 ≤ M'^2 := sq_le_sq₀ hM (hM.trans hM') |>.mpr hM'
  unfold remainderTerm
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add (mul_le_mul_of_nonneg_left hsq (sq_nonneg u))
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  gcongr

structure OuterData where
  u : ℚ
  b4 : ℚ
  v : ℚ
  k : ℕ
  t : ℕ
  deriving DecidableEq, Encodable

namespace OuterData

def amplitude (J : ℕ) (d : InnerData) : ℚ := (d.n^d.m+1)/(rationalSigma J)
def hints (d : InnerData) : ℕ := d.m*d.n^(d.m-1)-1
def rate (q : ℕ) : ℚ := 1-1/(2:ℚ)^q*(1-99999999/100000000)
def listBound (J : ℕ) (d : InnerData) (o : OuterData) : ℚ :=
  (⌈amplitude J d^2/o.u^2⌉₊:ℚ)*(⌈amplitude J d^2/d.θ^2⌉₊:ℚ)*rate (hints d)^o.k
def radicand (d : InnerData) (k t : ℕ) : ℚ :=
  ((2:ℚ)^(4*(hints d+3)*k)-1)*(k:ℚ)^2/(t:ℚ)

def Check (J : ℕ) (d : InnerData) (o : OuterData) : Prop :=
  0 < o.u ∧ 0 < o.b4 ∧ 0 < o.v ∧ 1 ≤ o.t ∧ o.k ≤ o.t ∧
  listBound J d o < d.p/4 ∧
  (64/(d.θ^2*rationalSigma J^2))*(J:ℚ)*o.b4 < d.p/4 ∧
  radicand d o.k o.t < o.v^2 ∧
  (256/d.θ^4)*(o.u^2*amplitude J d^2+o.v*(amplitude J d+amplitude J d^2/o.u)^4) < d.p/2

instance instDecidableCheck (J : ℕ) (d : InnerData) (o : OuterData) : Decidable (Check J d o) := by
  unfold Check; infer_instance

@[simp] lemma rate_cast (q : ℕ) : (rate q:ℝ)=hintRate q := by simp [rate,hintRate,repetitionRate]
end OuterData
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalDenominatorArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped BigOperators
namespace MinUncut.RationalDenominator
lemma mul_dvd {a b : ℚ} {A B : ℕ} (ha : a.den∣A) (hb : b.den∣B) : (a*b).den∣A*B :=
  (Rat.mul_den_dvd a b).trans (Nat.mul_dvd_mul ha hb)

lemma add_dvd {a b : ℚ} {D : ℕ} (ha : a.den∣D) (hb : b.den∣D) : (a+b).den∣D :=
  (Rat.add_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

lemma sub_dvd {a b : ℚ} {D : ℕ} (ha : a.den∣D) (hb : b.den∣D) : (a-b).den∣D :=
  (Rat.sub_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

lemma prod_dvd {X : Type*} (s : Finset X) (f : X → ℚ) (D : X → ℕ)
    (h : ∀ x∈s, (f x).den∣D x) : (∏ x∈s, f x).den∣∏ x∈s, D x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx,Finset.prod_insert hx]
    exact mul_dvd (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma inv_nat {N : ℕ} (hN : 0<N) : ((N:ℚ)⁻¹).den=N := Rat.inv_natCast_den_of_pos hN

lemma mul_nat_dvd (a : ℚ) (N : ℕ) : (a*N).den∣a.den := by
  simpa only [Rat.den_natCast,mul_one] using Rat.mul_den_dvd a (N:ℚ)

lemma denominatorProduct_pos {X : Type*} [Fintype X] (f : X → ℚ) : 0<∏ x, (f x).den :=
  Finset.prod_pos (fun x _ => Rat.den_pos (f x))

lemma denominator_dvd_product {X : Type*} [Fintype X] (f : X → ℚ) (x : X) :
    (f x).den∣∏ x, (f x).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ x)
end MinUncut.RationalDenominator

end
section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof RationalDenominator OuterSmoothness
attribute [local instance] Classical.propDecidable 
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n k : ℕ}

lemma rationalRowDensity_den {W : Type*} [Fintype W] [DecidableEq W] (a : ℚ) (b c : W) :
    (RowNoise.rationalRowDensity a b c).den∣a.den := by
  unfold RowNoise.rationalRowDensity
  apply add_dvd _ (dvd_refl _)
  split_ifs
  · exact (mul_nat_dvd (1-a) _).trans (sub_dvd (by simp) (dvd_refl _))
  · simp

lemma rationalDensity_den {R W : Type*} [Fintype R] [Fintype W] [DecidableEq W]
    (a : ℚ) (B C : R → W) : (RowNoise.rationalDensity a B C).den∣a.den^Fintype.card R := by
  have hh := prod_dvd (Finset.univ : Finset R) (fun r => RowNoise.rationalRowDensity a (B r) (C r))
    (fun _ => a.den) (fun r _ => rationalRowDensity_den a (B r) (C r))
  simpa only [RowNoise.rationalDensity,Finset.prod_const,Finset.card_univ] using hh

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_CayleySpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section


namespace MinUncutGames.Foundations.PCP.Expanders

open scoped BigOperators

def baseDimension : Nat := 448

end MinUncutGames.Foundations.PCP.Expanders

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.VerifierToCNF

abbrev BoolTriple := Bool × Bool × Bool

def tripleValue (t : BoolTriple) : Bool := (t.1 || t.2.1) || t.2.2

def chainView : List Bool → List Bool → List BoolTriple
  | [a, b, c], [] => [(a, b, c)]
  | a :: b :: rest, y :: ys => (a, b, y) :: chainView ((!y) :: rest) ys
  | _, _ => []

def fillBits (bits : List Bool) : List Bool :=
  match bits with
  | a :: b :: c :: d :: rest =>
      (!(a || b)) :: fillBits ((a || b) :: c :: d :: rest)
  | _ => []
termination_by bits.length
decreasing_by simp_wf

theorem chainView_length (bits ys : List Bool)
    (size : bits.length = ys.length + 3) :
    (chainView bits ys).length = ys.length + 1 := by
  induction ys generalizing bits with
  | nil =>
    match bits with
    | [a, b, c] => rfl
    | [] => simp at size
    | [_] => simp at size
    | [_, _] => simp at size
    | _ :: _ :: _ :: _ :: rest =>
      simp only [List.length_cons, List.length_nil] at size
      omega
  | cons y ys ih =>
    match bits with
    | [] => simp at size
    | [_] => simp only [List.length_cons, List.length_nil] at size; omega
    | a :: b :: rest =>
      have smaller : ((!y) :: rest).length = ys.length + 3 := by
        simp only [List.length_cons] at *
        omega
      have h := ih ((!y) :: rest) smaller
      simpa only [chainView, List.length_cons] using congrArg (fun n => n + 1) h

theorem fillBits_length (bits : List Bool) (size : 3 ≤ bits.length) :
    (fillBits bits).length + 3 = bits.length := by
  match bits with
  | [] => simp at size
  | [_] => simp at size
  | [_, _] => simp at size
  | [a, b, c] => simp [fillBits]
  | a :: b :: c :: d :: rest =>
    have ih := fillBits_length ((a || b) :: c :: d :: rest) (by simp)
    rw [fillBits]
    change (fillBits ((a || b) :: c :: d :: rest)).length + 1 + 3 = rest.length + 4
    simp only [List.length_cons] at ih
    omega
termination_by bits.length
decreasing_by simp_wf

abbrev Pattern (q : Nat) := Fin q → Bool

def patterns : (q : Nat) → List (Pattern q)
  | 0 => [Fin.elim0]
  | q + 1 => (patterns q).flatMap (fun p => [Fin.cases false p, Fin.cases true p])

theorem flatMap_pair_length {α β : Type*} (xs : List α) (f g : α → β) :
    (xs.flatMap (fun x => [f x, g x])).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem patterns_length (q : Nat) : (patterns q).length = 2 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [patterns, flatMap_pair_length, ih, Nat.pow_succ]
    exact Nat.mul_comm _ _

abbrev PatternIndex (q : Nat) := Fin (patterns q).length
def patternAt (q : Nat) (p : PatternIndex q) : Pattern q := (patterns q)[p.val]

structure FiniteVerifier (q : Nat) where
  «variables» : Nat
  events : Nat
  query : Fin events → Fin q → Fin «variables»
  accepts : Fin events → Pattern q → Bool

def auxiliaryCount {q : Nat} (V : FiniteVerifier q) : Nat :=
  V.events * (patterns q).length * (q - 3)

def outputVariables {q : Nat} (V : FiniteVerifier q) : Nat := V.«variables» + auxiliaryCount V

def oldIndex {q : Nat} (V : FiniteVerifier q) (v : Fin V.«variables») : Fin (outputVariables V) :=
  Fin.castAdd (auxiliaryCount V) v

def freshIndex {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (j : Fin (q - 3)) : Fin (outputVariables V) :=
  Fin.natAdd V.«variables» (finProdFinEquiv (finProdFinEquiv (e, p), j))

def auxiliaryNames {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Fin (outputVariables V)) :=
  List.ofFn (freshIndex V e p)

def restrictAssignment {q : Nat} (V : FiniteVerifier q)
    (B : Fin (outputVariables V) → Bool) : Fin V.«variables» → Bool :=
  fun v => B (oldIndex V v)

theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (k : Nat)
    (lengths : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := lengths x (by simp)
    have ht := ih (fun y hy => lengths y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, hx, ht,
      Nat.add_mul, Nat.one_mul]
    omega

theorem twelve_query_factor : 2 ^ 12 * (12 - 2) = 40960 := by decide

end MinUncutGames.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_FinalBooleanVerifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.FinalBooleanVerifier

variable {V E : Type*} {n m : Nat}

theorem twelve_query_auxiliary_factor : 2 ^ 12 * (12 - 3) = 36864 := by decide

end MinUncutGames.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteEnumeration
attribute [-instance] _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut

structure Enumeration (A : Type) where
  values : List A
  nodup : values.Nodup
  complete : ∀ a, a∈values

namespace Enumeration
variable {A B : Type}

def ofList [DecidableEq A] (l : List A) (h : ∀a, a∈l) : Enumeration A where
  values := l.dedup
  nodup := List.nodup_dedup l
  complete a := List.mem_dedup.mpr (h a)

def image [DecidableEq B] (E : Enumeration A) (f : A → B) (h : Function.Surjective f) : Enumeration B :=
  ofList (E.values.map f) (by intro b; obtain ⟨a,rfl⟩ := h b; exact List.mem_map.mpr ⟨a,E.complete a,rfl⟩)

def subtype [DecidableEq A] (E : Enumeration A) (p : A → Prop) [DecidablePred p] : Enumeration {a // p a} :=
  ofList ((E.values.filter (fun a => decide (p a))).attach.map (fun a =>
    (⟨a.val, by
      have hm : a.val ∈ E.values ∧ decide (p a.val) = true := List.mem_filter.mp a.property
      exact of_decide_eq_true hm.2⟩ : {a // p a}))) (by
    intro a
    apply List.mem_map.mpr
    exact ⟨⟨a.val,List.mem_filter.mpr ⟨E.complete a.val,by simpa only [decide_eq_true_eq] using a.property⟩⟩,List.mem_attach _ _,rfl⟩)

def sigma [DecidableEq A] (E : Enumeration A) {B : A → Type} [∀a, DecidableEq (B a)]
    (F : ∀a, Enumeration (B a)) : Enumeration (Σa, B a) :=
  ofList (E.values.flatMap (fun a => (F a).values.map (fun b => Sigma.mk a b))) (by
    rintro ⟨a,b⟩
    exact List.mem_flatMap.mpr ⟨a,E.complete a,List.mem_map.mpr ⟨b,(F a).complete b,rfl⟩⟩)

lemma sum_values [Fintype A] (E : Enumeration A) (f : A → ℕ) :
    (E.values.map f).sum=∑a, f a := by
  classical
  have he : E.values.toFinset=Finset.univ := by ext a; simp [E.complete]
  rw [← List.sum_toFinset f E.nodup]
  rw [he]
end Enumeration
end MinUncut

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Bridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable

variable {I Name : Type*}

def width (h : Bool) : ℕ := if h then 1 else 3

end MinUncut.Outer.LocalTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ParameterFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian
abbrev InnerDataRaw := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℚ × ℚ × ℚ
abbrev OuterDataRaw := ℚ × ℚ × ℚ × ℕ × ℕ
def outerDataEquiv : OuterData ≃ OuterDataRaw where
  toFun d := (d.u,d.b4,d.v,d.k,d.t)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
abbrev GridDataRaw := ℕ × ℕ × ℕ
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquationOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable

variable {t k m n : ℕ} {g : MinUncut.FiniteGaussian.GridData}

lemma sum_flatMap_nat {A : Type*} (l : List A) (f : A → List ℕ) :
    (l.flatMap f).sum=(l.map (fun a=>(f a).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_UniformFiniteSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess

variable {α β : Type} [Primcodable α] [Primcodable β]

def decodeGood (dec : ℕ → Option β) (p : α → β → Prop) (x : α) (n : ℕ) : Prop :=
  (dec n).elim False (p x)

instance instDecidableDecodeGoodOfDecidableRel {dec : ℕ → Option β} {p : α → β → Prop} [DecidableRel p] (x : α) (n : ℕ) :
    Decidable (decodeGood dec p x n) := by
  unfold decodeGood
  cases dec n <;> simp only [Option.elim] <;> infer_instance

lemma c_searchProj : Computable (fun q : (α × ℕ) × β=>(q.1.1,q.2)) :=
  (Computable.fst.comp Computable.fst).pair Computable.snd
lemma c_searchEval {p : α → β → Prop} [DecidableRel p]
    (hp : ComputablePred (fun q : α × β=>p q.1 q.2)) :
    Computable (fun q : (α × ℕ) × β=>decide (p q.1.1 q.2)) :=
  by
  have hh : Computable (fun q : α × β=>decide (p q.1 q.2)) := hp.decide
  exact @Computable.comp ((α × ℕ) × β) (α × β) Bool _ _ _
    (fun q=>decide (p q.1 q.2)) (fun q=>(q.1.1,q.2)) hh c_searchProj
lemma c_searchDecode {dec : ℕ → Option β} (hd : Computable dec) :
    Computable (fun q : α × ℕ=>dec q.2) := hd.comp Computable.snd
lemma c_searchBool {dec : ℕ → Option β} {p : α → β → Prop} [DecidableRel p]
    (hd : Computable dec) (hp : ComputablePred (fun q : α × β=>p q.1 q.2)) :
    Computable (fun q : α × ℕ=>(dec q.2).elim false (fun b=>decide (p q.1 b))) :=
  (Computable.option_casesOn (c_searchDecode hd) (ca_const false) ((c_searchEval hp).to₂)).of_eq
    (fun q=>by cases dec q.2 <;> rfl)
omit [Primcodable α] [Primcodable β] in
lemma searchBool_eq {dec : ℕ → Option β} {p : α → β → Prop} [DecidableRel p] (q : α × ℕ) :
    (dec q.2).elim false (fun b=>decide (p q.1 b))=decide (decodeGood dec p q.1 q.2) := by
  cases he : dec q.2 <;> simp only [decodeGood,he,Option.elim,decide_false]
lemma computable_decodeGood {dec : ℕ → Option β} {p : α → β → Prop}
    [DecidableRel p] (hd : Computable dec)
    (hp : ComputablePred (fun q : α × β=>p q.1 q.2)) :
    ComputablePred (fun q : α × ℕ=>decodeGood dec p q.1 q.2) :=
  ⟨inferInstance,(c_searchBool hd hp).of_eq searchBool_eq⟩

instance option_elim_decidable {p : β → Prop} [DecidablePred p] (o : Option β) :
    Decidable (o.elim False p) := by
  cases o <;> simp only [Option.elim] <;> infer_instance

lemma choose_getD {γ : Type} [Encodable γ] {p : γ → Prop} [DecidablePred p] (h : ∃b,p b) (d : γ) :
    Encodable.choose h =
      ((Encodable.decode (α:=γ) (Nat.find (show ∃n,(Encodable.decode (α:=γ) n).elim False p from by
        obtain ⟨b,hb⟩:=h
        exact ⟨Encodable.encode b,by simp [hb]⟩)))).getD d := by
  unfold Encodable.choose
  conv_lhs => arg 1; whnf
  split
  next oldPredicate decoded valid value validValue equation compatibility =>
    have decodedValue : (Encodable.decode (α := γ) (Nat.find (show
        ∃ index, (Encodable.decode (α := γ) index).elim False p from by
          obtain ⟨witness, validWitness⟩ := h
          exact ⟨Encodable.encode witness, by simp [validWitness]⟩))) = some value := by
      convert equation using 2
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext index
      cases Encodable.decode (α := γ) index <;> rfl
    rw [decodedValue]
    rfl

noncomputable def search {p : α → β → Prop} [DecidableRel p]
    (h : ∀a,∃b,p a b) (a : α) : β := Encodable.choose (h a)

omit [Primcodable α] in
lemma search_spec {p : α → β → Prop} [DecidableRel p]
    (h : ∀a,∃b,p a b) (a : α) : p a (search h a) :=
  Encodable.choose_spec (h a)

lemma computable_search {p : α → β → Prop} [DecidableRel p]
    (hp : ComputablePred (fun q : α × β=>p q.1 q.2))
    (h : ∀a,∃b,p a b) (d : β) : Computable (search h) := by
  have hn : ∀a,∃n,decodeGood (Encodable.decode (α:=β)) p a n := by
    intro a
    obtain ⟨b,hb⟩:=h a
    exact ⟨Encodable.encode b,by simp [decodeGood,hb]⟩
  have hc : Computable (fun a=>Nat.find (hn a)) :=
    Computable.find (computable_decodeGood Computable.decode hp) hn
  exact (Computable.option_getD (Computable.decode.comp hc) (ca_const d)).of_eq (by
    intro a
    convert (choose_getD (h a) d).symm using 3
    all_goals try with_reducible_and_instances rfl
    all_goals congr 1)
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ArithmeticTactic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

set_option maxHeartbeats 1000000
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian

def parameterJ (K : ℕ) : ℕ := 10*(max K 2)
lemma parameterJ_pos (K : ℕ) : 1≤parameterJ K := by unfold parameterJ; omega
@[fun_prop] lemma c_parameterJ : Computable parameterJ := by
  have h : Computable (fun K : ℕ=>10*(K+(2-K))) := by fun_prop
  exact h.of_eq (by intro K; unfold parameterJ; congr 1; omega)
end MinUncut.Preprocess

end

end OAI
end


