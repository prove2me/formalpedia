-- Prove2me | Definitions.Def_OAIQ3Vx001
-- name    : OAIQ3Vx001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:24:18.900992+00:00
-- url     : https://prove2.me/theorems/d6df3021-034a-4466-8584-0807a6fd69c2
-- title:
--   Definitions bundle OAIQ3Vx001 of the split of OpenAI, Strongly rational unitary vertex operator algebras and conformal nets
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinimalVertex.main`, carved from OpenAI's openai/math development (OpenAI, *Strongly rational unitary vertex operator algebras and conformal nets*, OpenAI Math Release, September 25, 2026, result family 280, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 350 declarations of OpenAI's Lean: 66 definitions, 2 inductive types or structures, 5 instances and 277 theorems. The definitions and types are `OAI.StronglyRationalVOA.CFTTypeVOA.UnitaryStructure.adjointMass`, `OAI.StronglyRationalVOA.CFTTypeVOA.sharpCorrectionMass`, `OAI.StronglyRationalVOA.CutoffPowerControl`, `OAI.StronglyRationalVOA.FourierAnalysis.coefficientCLM`, `OAI.StronglyRationalVOA.LocalSkewFlow.commutatorOperator`, `OAI.StronglyRationalVOA.LocalSkewFlow.insertedExp`, `OAI.StronglyRationalVOA.LocalSkewFlow.insertedExpTerm`, `OAI.StronglyRationalVOA.LocalSkewFlow.skewExp`, `OAI.StronglyRationalVOA.LocalSkewFlow.skewExpTerm`, `OAI.StronglyRationalVOA.LocalSkewFlow.skewTaylor`, `OAI.StronglyRationalVOA.MobiusCoefficients.InRange`, `OAI.StronglyRationalVOA.MobiusCoefficients.Nonnegative`, `OAI.StronglyRationalVOA.MobiusCoefficients.coeff`, `OAI.StronglyRationalVOA.MobiusCoefficients.mean`, `OAI.StronglyRationalVOA.MobiusCoefficients.representation`, `OAI.StronglyRationalVOA.MobiusCoefficients.step`, `OAI.StronglyRationalVOA.MobiusCoefficients.total`, `OAI.StronglyRationalVOA.PolynomialCutoffControl`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.Field`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.Field.frequency`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.Field.normalizedCoordinate`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.Field.stressScalar`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.Field.totalTime`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.Field.unitParameter`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.anomalyShift`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.degreeOne`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.density`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.identity`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.identityError`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.interpolate`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.inverse`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.isotopy`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.jacobian`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.jet`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.normalizedAnomaly`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.orderIso`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.realAngularDensity`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.realAngularVelocity`, `OAI.StronglyRationalVOA.PositiveCircleGeometry.SmoothLift.velocity` and 28 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory/VertexAlgebra, in whole or in part: `VertexAlgebra_AdjointMass`, `VertexAlgebra_ApproximatingFlowDerivative`, `VertexAlgebra_BoundedFlows`, `VertexAlgebra_BoundedMultiplierSingle`, `VertexAlgebra_CoefficientDifferentiated`, `VertexAlgebra_CoefficientSummableBound`, `VertexAlgebra_ColumnControl`, `VertexAlgebra_ConstrainedSquareBound`, `VertexAlgebra_CutoffPowerControl`, `VertexAlgebra_DiffeomorphismStressSmooth`, `VertexAlgebra_EnergyCutoffNorm`, `VertexAlgebra_EnergyShiftPow`, `VertexAlgebra_GeneratorSharpGrowth`, `VertexAlgebra_GeometryContinuation`, `VertexAlgebra_GraphEquiv`, `VertexAlgebra_GraphInvariantOf`, `VertexAlgebra_HilbertCore`, `VertexAlgebra_InverseEnergySelf`, `VertexAlgebra_MulLeftPow`, `VertexAlgebra_PrimaryStressWeak`, `VertexAlgebra_RegularizerFactorAdd`, `VertexAlgebra_RotationConjugateCommutant`, `VertexAlgebra_SmoothConjugateInner`, `VertexAlgebra_SmoothConjugatePrimary`, `VertexAlgebra_SmoothEnergyPower`, `VertexAlgebra_SmoothTopology`, `VertexAlgebra_StressCutoffNormalized2`, `VertexAlgebra_StressEvolution`, `VertexAlgebra_StressPropagatorDerivative`, `VertexAlgebra_StressSmoothness`, `VertexAlgebra_SummableNormSobolev`, `VertexAlgebra_SymmetricWeakCommute`, `VertexAlgebra_TimeAverageGraph`.
--
--   **Imports.** It imports the published bundle `Def_VertexAlgebraNet`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Vx003`, `OAIQ3Vx004` and `OAIQ3Vx005`.
-- source:
--   OpenAI, Strongly rational unitary vertex operator algebras and conformal nets, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 280; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strongly-rational-unitary-vertex-operator-algebras-and-conformal-nets-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory/VertexAlgebra at commit adc7f12

import Mathlib
import Definitions.Def_VertexAlgebraNet

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_EnergyShiftPow
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v

namespace LocalSkewFlow
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma inner_tsum_left (u : ℕ → E) (hu : Summable u) (w : E) :
    inner ℂ (∑' n, u n) w = ∑' n, inner ℂ (u n) w := by
  exact ((innerSL ℂ).flip w).map_tsum hu

lemma inner_tsum_right (v : ℕ → E) (hv : Summable v) (w : E) :
    inner ℂ w (∑' n, v n) = ∑' n, inner ℂ w (v n) := by
  exact (innerSL ℂ w).map_tsum hv

variable [CompleteSpace E]

lemma inner_tsum_prod (u v : ℕ → E) (hu : Summable (fun n => ‖u n‖))
    (hv : Summable (fun n => ‖v n‖)) :
    inner ℂ (∑' n, u n) (∑' n, v n) =
      ∑' p : ℕ × ℕ, inner ℂ (u p.1) (v p.2) := by
  have hs : Summable (fun p : ℕ × ℕ => inner ℂ (u p.1) (v p.2)) := by
    have hp : Summable (fun p : ℕ × ℕ => ‖u p.1‖ * ‖v p.2‖) :=
      hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    apply Summable.of_norm_bounded hp
    intro p
    exact norm_inner_le_norm _ _
  rw [hs.tsum_prod, inner_tsum_left _ hu.of_norm]
  apply tsum_congr
  intro n
  exact inner_tsum_right _ hv.of_norm _

lemma tsum_prod_antidiagonal (f : ℕ × ℕ → ℂ) (hf : Summable f) :
    (∑' p, f p) = ∑' n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, f p := by
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f]
  have hs := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff).mpr hf
  change (∑' p, (f ∘ Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd) p) = _
  rw [hs.tsum_sigma]
  apply tsum_congr
  intro n
  exact (tsum_fintype _).trans (Finset.sum_finset_coe _ _)

lemma exp_antidiagonal (s t : ℂ) (k : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
       (s^p.1 / (p.1.factorial : ℂ)) * (t^p.2 / (p.2.factorial : ℂ))) =
      (s + t)^k / (k.factorial : ℂ) := by
  rw [(Commute.all s t).add_pow', Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← he]
  simp only [nsmul_eq_mul]
  rw [Nat.cast_add_choose ℂ]
  have h1 : (p.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (p.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : ((p.1 + p.2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

section SkewFlow
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K : Module.End ℂ V)

def skewExpTerm (t : ℝ) (n : ℕ) (v : V) : UniformSpace.Completion V :=
  ((t : ℂ)^n / (n.factorial : ℂ)) • (((K^n) v : V) : UniformSpace.Completion V)

def skewExp (t : ℝ) (v : V) : UniformSpace.Completion V :=
  ∑' n, skewExpTerm K t n v

lemma skewExpTerm_norm_bound {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (t : ℝ) (n : ℕ) :
    ‖skewExpTerm K t n v‖ ≤ (2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖ := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hc : ((N + n).choose n : ℝ) ≤ (2 : ℝ)^(N + n) := by
    exact_mod_cast Nat.choose_le_two_pow (N + n) n
  calc
    _ = (|t|^n / (n.factorial : ℝ)) * ‖(K^n) v‖ := by
      simp [skewExpTerm, norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (|t|^n / (n.factorial : ℝ)) *
        (C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖) := by gcongr; exact hb n
    _ = (|t| * C)^n * ((N + n).choose n : ℝ) * ‖v‖ := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose]
      push_cast
      rw [mul_pow]
      field_simp
    _ ≤ (|t| * C)^n * (2 : ℝ)^(N + n) * ‖v‖ := by gcongr
    _ = _ := by rw [pow_add]; simp only [mul_pow]; ring

lemma summable_norm_skewExpTerm {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    {t : ℝ} (ht : 2 * |t| * C < 1) :
    Summable (fun n => ‖skewExpTerm K t n v‖) := by
  have hg := (summable_geometric_of_lt_one (by positivity : 0 ≤ 2 * |t| * C) ht).mul_left ((2 : ℝ)^N)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (skewExpTerm_norm_bound K hC hb t)
    (hg.mul_right ‖v‖)

lemma skew_pow_inner
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (n m : ℕ) (v w : V) :
    inner ℂ ((K^n) v) ((K^m) w) = (-1 : ℂ)^n * inner ℂ v ((K^(n + m)) w) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, hs]
    rw [← Module.End.mul_apply, ← pow_succ', ih (m + 1)]
    rw [show n + (m + 1) = n + 1 + m by omega, pow_succ]
    ring

lemma inner_skewExpTerm
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (n m : ℕ) (v w : V) :
    inner ℂ (skewExpTerm K t n v) (skewExpTerm K t m w) =
      (((-t : ℝ) : ℂ)^n / (n.factorial : ℂ)) *
        ((t : ℂ)^m / (m.factorial : ℂ)) * inner ℂ v ((K^(n + m)) w) := by
  simp only [skewExpTerm, inner_smul_left, inner_smul_right,
    UniformSpace.Completion.inner_coe, skew_pow_inner K hs,
    map_div₀, map_pow, Complex.conj_ofReal, map_natCast]
  push_cast
  rw [neg_pow]
  ring

lemma inner_skewExp
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (v w : V)
    (hv : Summable (fun n => ‖skewExpTerm K t n v‖))
    (hw : Summable (fun n => ‖skewExpTerm K t n w‖)) :
    inner ℂ (skewExp K t v) (skewExp K t w) = inner ℂ v w := by
  have hf : Summable (fun p : ℕ × ℕ =>
      inner ℂ (skewExpTerm K t p.1 v) (skewExpTerm K t p.2 w)) := by
    apply Summable.of_norm_bounded
      (hv.mul_of_nonneg hw (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    intro p
    exact norm_inner_le_norm _ _
  rw [skewExp, skewExp, inner_tsum_prod _ _ hv hw, tsum_prod_antidiagonal _ hf]
  have he : ∀ k, (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
      inner ℂ (skewExpTerm K t p.1 v) (skewExpTerm K t p.2 w)) =
      if k = 0 then inner ℂ v w else 0 := by
    intro k
    simp_rw [inner_skewExpTerm K hs]
    calc
      _ = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          (((-t : ℝ) : ℂ)^p.1 / (p.1.factorial : ℂ)) *
          ((t : ℂ)^p.2 / (p.2.factorial : ℂ))) * inner ℂ v ((K^k) w) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
      _ = _ := by rw [exp_antidiagonal]; push_cast; split_ifs with hk <;> simp [hk]
  simp_rw [he]
  simp
end SkewFlow

section SkewFlowNorm
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K : Module.End ℂ V)

lemma norm_skewExp
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (v : V) (hv : Summable (fun n => ‖skewExpTerm K t n v‖)) :
    ‖skewExp K t v‖ = ‖v‖ := by
  have h := inner_skewExp K hs t v v hv hv
  simp only [inner_self_eq_norm_sq_to_K] at h
  have he : ‖skewExp K t v‖^2 = ‖v‖^2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

lemma skewExp_add (t : ℝ) (v w : V)
    (hv : Summable (fun n => ‖skewExpTerm K t n v‖))
    (hw : Summable (fun n => ‖skewExpTerm K t n w‖)) :
    skewExp K t (v + w) = skewExp K t v + skewExp K t w := by
  simp only [skewExp, skewExpTerm, map_add, UniformSpace.Completion.coe_add, smul_add]
  exact hv.of_norm.tsum_add hw.of_norm

lemma skewExp_smul (t : ℝ) (z : ℂ) (v : V) :
    skewExp K t (z • v) = z • skewExp K t v := by
  simp only [skewExp, skewExpTerm, map_smul, UniformSpace.Completion.coe_smul,
    smul_comm (_ / _) z, tsum_const_smul'']

end SkewFlowNorm

lemma summable_shifted_pow_geometric (a : ℝ) (ha : 0 ≤ a) (r : ℕ)
    {q : ℝ} (hq : 0 ≤ q) (hql : q < 1) :
    Summable (fun n : ℕ => (a + n)^r * q^n) := by
  have he : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq] using hql
  have h1 := (summable_geometric_of_lt_one hq hql).mul_left (a^r)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one r he
  have hsum := (h1.add h2).mul_left ((2 : ℝ)^(r - 1))
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
  intro n
  change (a + (n : ℝ))^r * q^n ≤ 2^(r - 1) * (a^r*q^n + (n : ℝ)^r*q^n)
  calc
    _ ≤ (2 : ℝ)^(r - 1) * (a^r + (n : ℝ)^r) * q^n := by
      gcongr
      exact add_pow_le ha (Nat.cast_nonneg n) r
    _ = _ := by ring

lemma shifted_pow_geometric_tail_uniform (r N n : ℕ) (hn : N ≤ n) {q : ℝ} (hq : 0 ≤ q) :
    (2 : ℝ)^N * (1 + (N : ℝ) + n)^r * q^n ≤
      (2 : ℝ)^r * (1 + (n : ℝ))^r * (2*q)^n := by
  have hN : (N : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ (2 : ℝ)^n * (2 * (1 + (n : ℝ)))^r * q^n := by
      gcongr
      · norm_num
      · linarith
    _ = _ := by simp only [mul_pow]; ring

end LocalSkewFlow
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_MulLeftPow
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace LocalSkewFlow
open Finset
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
section Algebra
variable {R B : Type*} [CommRing R] [Ring B] [Algebra R B]
lemma mulLeft_pow_apply (x y : B) (n : ℕ) :
    ((LinearMap.mulLeft R x)^n) y = x^n * y := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, ih, LinearMap.mulLeft_apply, mul_assoc]

lemma mulRight_pow_apply (x y : B) (n : ℕ) :
    ((LinearMap.mulRight R x)^n) y = y * x^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, LinearMap.mulRight_apply, mul_assoc,
      ← pow_succ, pow_succ']

def commutatorOperator (x : B) : Module.End R B :=
  LinearMap.mulLeft R x + LinearMap.mulRight R (-x)

lemma commutatorOperator_apply (x y : B) : commutatorOperator (R := R) x y = x*y-y*x := by
  simp [commutatorOperator, sub_eq_add_neg]

lemma commutatorOperator_pow (x y : B) (n : ℕ) :
    (commutatorOperator (R := R) x ^ n) y =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        n.choose p.1 • (x^p.1 * y * (-x)^p.2) := by
  rw [commutatorOperator, (LinearMap.commute_mulLeft_right x (-x)).add_pow']
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    mulLeft_pow_apply, mulRight_pow_apply, mul_assoc]

end Algebra

section Normalized
variable {B : Type*} [Ring B] [Algebra ℂ B]

lemma commutatorOperator_pow_normalized (x y : B) (t : ℂ) (n : ℕ) :
    (t^n / (n.factorial : ℂ)) • ((commutatorOperator (R := ℂ) x)^n) y =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        ((t^p.1 / (p.1.factorial : ℂ)) * ((-t)^p.2 / (p.2.factorial : ℂ))) •
          (x^p.1 * y * x^p.2) := by
  rw [commutatorOperator_pow, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have he : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← he]
  have hn : (-x)^p.2 = (-1 : ℂ)^p.2 • x^p.2 := by
    rw [← neg_one_smul ℂ x, smul_pow]
  rw [hn, mul_smul_comm]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul, Nat.cast_add_choose ℂ]
  have h1 : (p.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (p.2.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h3 : ((p.1 + p.2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  congr 1
  rw [pow_add, neg_pow t p.2]
  field_simp

end Normalized

section BCHFlow
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K T : Module.End ℂ V)

def insertedExpTerm (t : ℝ) (n : ℕ) (v : V) : UniformSpace.Completion V :=
  ((t : ℂ)^n / (n.factorial : ℂ)) • ((T ((K^n) v) : V) : UniformSpace.Completion V)

def insertedExp (t : ℝ) (v : V) : UniformSpace.Completion V :=
  ∑' n, insertedExpTerm K T t n v

lemma inner_insertedExpTerm
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (i j : ℕ) (v w : V) :
    inner ℂ (skewExpTerm K (-t) i v) (insertedExpTerm K T (-t) j w) =
      ((t : ℂ)^i / (i.factorial : ℂ)) * (((-t : ℝ) : ℂ)^j / (j.factorial : ℂ)) *
        inner ℂ v ((K^i * T * K^j) w) := by
  have hmove : inner ℂ ((K^i) v) (T ((K^j) w)) =
      (-1 : ℂ)^i * inner ℂ v ((K^i) (T ((K^j) w))) := by
    simpa using skew_pow_inner K hs i 0 v (T ((K^j) w))
  simp only [skewExpTerm, insertedExpTerm, inner_smul_left, inner_smul_right,
    UniformSpace.Completion.inner_coe, map_div₀, map_pow, Complex.conj_ofReal, map_natCast,
    hmove, Module.End.mul_apply]
  have hi : (((-t : ℝ) : ℂ)^i) * (-1 : ℂ)^i = (t : ℂ)^i := by
    rw [← mul_pow]
    simp
  calc
    _ = ((((-t : ℝ) : ℂ)^i) * (-1 : ℂ)^i) / (i.factorial : ℂ) *
        (((-t : ℝ) : ℂ)^j / (j.factorial : ℂ)) *
        inner ℂ v ((K^i) (T ((K^j) w))) := by ring
    _ = _ := by rw [hi]

lemma inner_skewExp_inserted
    (hs : ∀ v w, inner ℂ (K v) w = - inner ℂ v (K w))
    (t : ℝ) (v w : V)
    (hv : Summable (fun n => ‖skewExpTerm K (-t) n v‖))
    (hw : Summable (fun n => ‖insertedExpTerm K T (-t) n w‖)) :
    inner ℂ (skewExp K (-t) v) (insertedExp K T (-t) w) =
      ∑' n, ((t : ℂ)^n / (n.factorial : ℂ)) *
        inner ℂ v (((commutatorOperator (R := ℂ) K)^n) T w) := by
  have hf : Summable (fun p : ℕ × ℕ =>
      inner ℂ (skewExpTerm K (-t) p.1 v) (insertedExpTerm K T (-t) p.2 w)) := by
    apply Summable.of_norm_bounded
      (hv.mul_of_nonneg hw (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
    intro p
    exact norm_inner_le_norm _ _
  rw [skewExp, insertedExp, inner_tsum_prod _ _ hv hw, tsum_prod_antidiagonal _ hf]
  apply tsum_congr
  intro n
  simp_rw [inner_insertedExpTerm K T hs]
  have h := congrArg (fun f : Module.End ℂ V => inner ℂ v (f w))
    (commutatorOperator_pow_normalized K T (t : ℂ) n)
  simp only [LinearMap.smul_apply, inner_smul_right, LinearMap.sum_apply, inner_sum,
    Complex.ofReal_neg] at h ⊢
  exact h.symm

end BCHFlow

section InsertedEstimates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K T : Module.End ℂ V)

lemma insertedExpTerm_norm_bound {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N r : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (hT : ∀ n : ℕ, ‖T ((K^n) v)‖ ≤ D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖)
    (t : ℝ) (n : ℕ) :
    ‖insertedExpTerm K T t n v‖ ≤
      D * (1 + (N : ℝ) + n)^r * (2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖ := by
  have hn := skewExpTerm_norm_bound K hC hb t n
  have hcoef : 0 ≤ ‖(t : ℂ)^n / (n.factorial : ℂ)‖ := norm_nonneg _
  calc
    _ = ‖(t : ℂ)^n / (n.factorial : ℂ)‖ * ‖T ((K^n) v)‖ := by
      simp [insertedExpTerm, norm_smul]
    _ ≤ ‖(t : ℂ)^n / (n.factorial : ℂ)‖ *
        (D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖) := by gcongr; exact hT n
    _ = D * (1 + (N : ℝ) + n)^r * ‖skewExpTerm K t n v‖ := by
      simp only [skewExpTerm, norm_smul, UniformSpace.Completion.norm_coe]
      ring
    _ ≤ D * (1 + (N : ℝ) + n)^r * ((2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖) := by
      gcongr
    _ = _ := by ring

lemma summable_norm_insertedExpTerm {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N r : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (hT : ∀ n : ℕ, ‖T ((K^n) v)‖ ≤ D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖)
    {t : ℝ} (ht : 2 * |t| * C < 1) :
    Summable (fun n => ‖insertedExpTerm K T t n v‖) := by
  have hg := summable_shifted_pow_geometric (1 + (N : ℝ)) (by positivity) r
    (by positivity : 0 ≤ 2 * |t| * C) ht
  have hg' : Summable (fun n : ℕ => D * (1 + (N : ℝ) + n)^r *
      (2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖) := by
    have he : (fun n : ℕ => D * (1 + (N : ℝ) + n)^r *
        (2 : ℝ)^N * (2 * |t| * C)^n * ‖v‖) =
        (fun n : ℕ => (D * (2 : ℝ)^N * ‖v‖) *
          ((1 + (N : ℝ) + n)^r * (2 * |t| * C)^n)) := by
      funext n
      ring
    rw [he]
    exact hg.mul_left (D * (2 : ℝ)^N * ‖v‖)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (insertedExpTerm_norm_bound K T hC hD hb hT t) hg'

lemma insertedExpTerm_tail_bound {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N r : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (hT : ∀ n : ℕ, ‖T ((K^n) v)‖ ≤ D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖)
    (t : ℝ) (n : ℕ) (hn : N ≤ n) :
    ‖insertedExpTerm K T t n v‖ ≤
      D * (2 : ℝ)^r * (1 + (n : ℝ))^r * (4 * |t| * C)^n * ‖v‖ := by
  apply (insertedExpTerm_norm_bound K T hC hD hb hT t n).trans
  have h := shifted_pow_geometric_tail_uniform r N n hn
    (by positivity : 0 ≤ 2 * |t| * C)
  calc
    _ = D * ((2 : ℝ)^N * (1 + (N : ℝ) + n)^r * (2 * |t| * C)^n) * ‖v‖ := by ring
    _ ≤ D * ((2 : ℝ)^r * (1 + (n : ℝ))^r * (2 * (2 * |t| * C))^n) * ‖v‖ := by gcongr
    _ = _ := by congr 1; ring

end InsertedEstimates

section Tails
variable {E : Type*} [NormedAddCommGroup E]

lemma norm_tsum_tail_le {f : ℕ → E} {g : ℕ → ℝ}
    (hf : Summable (fun n => ‖f n‖)) (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n)
    (N : ℕ) (H : ∀ n, N ≤ n → ‖f n‖ ≤ g n) :
    ‖∑' n, f (n + N)‖ ≤ ∑' n, g n := by
  have hfN := (summable_nat_add_iff N).mpr hf
  have hgN := (summable_nat_add_iff N).mpr hg
  apply (norm_tsum_le_tsum_norm hfN).trans
  apply (hfN.tsum_le_tsum (fun n => H (n + N) (by omega)) hgN).trans
  have hs := hg.sum_add_tsum_nat_add N
  have hpos : 0 ≤ ∑ i ∈ Finset.range N, g i := Finset.sum_nonneg (fun i _ => hg0 i)
  linarith

end Tails

section Taylor
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (K T : Module.End ℂ V)

 
def skewTaylor (t : ℝ) (N : ℕ) (v : V) : V :=
  ∑ n ∈ Finset.range N, ((t : ℂ)^n / (n.factorial : ℂ)) • (K^n) v

lemma coe_skewTaylor (t : ℝ) (N : ℕ) (v : V) :
    ((skewTaylor K t N v : V) : UniformSpace.Completion V) =
      ∑ n ∈ Finset.range N, skewExpTerm K t n v := by
  unfold skewTaylor
  change UniformSpace.Completion.toCompl (∑ n ∈ Finset.range N,
    ((t : ℂ)^n / (n.factorial : ℂ)) • (K^n) v) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact UniformSpace.Completion.coe_smul _ _

lemma coe_apply_skewTaylor (t : ℝ) (N : ℕ) (v : V) :
    (T (skewTaylor K t N v) : UniformSpace.Completion V) =
      ∑ n ∈ Finset.range N, insertedExpTerm K T t n v := by
  simp only [skewTaylor, map_sum, map_smul]
  change UniformSpace.Completion.toCompl (∑ n ∈ Finset.range N,
    ((t : ℂ)^n / (n.factorial : ℂ)) • T ((K^n) v)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact UniformSpace.Completion.coe_smul _ _

lemma skewTaylor_add_tail {t : ℝ} {N : ℕ} {v : V}
    (hf : Summable (fun n => ‖skewExpTerm K t n v‖)) :
    ((skewTaylor K t N v : V) : UniformSpace.Completion V) +
      ∑' n, skewExpTerm K t (n + N) v = skewExp K t v := by
  rw [coe_skewTaylor, skewExp]
  exact hf.of_norm.sum_add_tsum_nat_add N

lemma apply_skewTaylor_add_tail {t : ℝ} {N : ℕ} {v : V}
    (hf : Summable (fun n => ‖insertedExpTerm K T t n v‖)) :
    (T (skewTaylor K t N v) : UniformSpace.Completion V) +
      ∑' n, insertedExpTerm K T t (n + N) v = insertedExp K T t v := by
  rw [coe_apply_skewTaylor, insertedExp]
  exact hf.of_norm.sum_add_tsum_nat_add N

lemma skewExp_tail_bound {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    {t : ℝ} (ht : 4 * |t| * C < 1) :
    ‖∑' n, skewExpTerm K t (n + N) v‖ ≤ (1 - 4 * |t| * C)⁻¹ * ‖v‖ := by
  have hq0 : 0 ≤ 4 * |t| * C := by positivity
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hf := summable_norm_skewExpTerm K hC hb hq
  have hg := (summable_geometric_of_lt_one hq0 ht).mul_right ‖v‖
  have hbnd : ∀ n, N ≤ n → ‖skewExpTerm K t n v‖ ≤ (4 * |t| * C)^n * ‖v‖ := by
    intro n hn
    apply (skewExpTerm_norm_bound K hC hb t n).trans
    calc
      _ ≤ (2 : ℝ)^n * (2 * |t| * C)^n * ‖v‖ := by gcongr; norm_num
      _ = _ := by rw [← mul_pow]; congr 2; ring
  have h := norm_tsum_tail_le hf hg (fun _ => by positivity) N hbnd
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 ht] at h
  exact h

lemma skewTaylor_norm_bound
    (hs : ∀ v w, inner ℂ (K v) w = -inner ℂ v (K w))
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    {t : ℝ} (ht : 4 * |t| * C < 1) :
    ‖skewTaylor K t N v‖ ≤ (1 + (1 - 4 * |t| * C)⁻¹) * ‖v‖ := by
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hf := summable_norm_skewExpTerm K hC hb hq
  have he := skewTaylor_add_tail K (N := N) hf
  have hne := norm_skewExp K hs t v hf
  have htbd := skewExp_tail_bound K hC hb ht
  have he' : ((skewTaylor K t N v : V) : UniformSpace.Completion V) =
      skewExp K t v - ∑' n, skewExpTerm K t (n + N) v := (eq_sub_iff_add_eq).mpr he
  rw [← UniformSpace.Completion.norm_coe, he']
  calc
    _ ≤ ‖skewExp K t v‖ + ‖∑' n, skewExpTerm K t (n + N) v‖ := norm_sub_le _ _
    _ ≤ ‖v‖ + (1 - 4 * |t| * C)⁻¹ * ‖v‖ := by rw [hne]; gcongr
    _ = _ := by ring

lemma insertedExp_tail_norm_bound {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    {N r : ℕ} {v : V}
    (hb : ∀ n, ‖(K^n) v‖ ≤ C^n * ((N + 1).ascFactorial n : ℝ) * ‖v‖)
    (hT : ∀ n : ℕ, ‖T ((K^n) v)‖ ≤ D * (1 + (N : ℝ) + n)^r * ‖(K^n) v‖)
    {t : ℝ} (ht : 4 * |t| * C < 1) :
    ‖∑' n, insertedExpTerm K T t (n + N) v‖ ≤
      (D * (2 : ℝ)^r * ∑' n : ℕ, (1 + (n : ℝ))^r * (4 * |t| * C)^n) * ‖v‖ := by
  have hq0 : 0 ≤ 4 * |t| * C := by positivity
  have hq : 2 * |t| * C < 1 := by nlinarith [mul_nonneg (abs_nonneg t) hC]
  have hf := summable_norm_insertedExpTerm K T hC hD hb hT hq
  have hg₀ := summable_shifted_pow_geometric 1 (by norm_num) r hq0 ht
  have hg := (hg₀.mul_left (D * (2 : ℝ)^r)).mul_right ‖v‖
  have hbnd : ∀ n, N ≤ n → ‖insertedExpTerm K T t n v‖ ≤
      D * (2 : ℝ)^r * ((1 + (n : ℝ))^r * (4 * |t| * C)^n) * ‖v‖ := by
    intro n hn
    convert insertedExpTerm_tail_bound K T hC hD hb hT t n hn using 1 <;> first | rfl | ring
  have h := norm_tsum_tail_le hf hg (fun _ => by positivity) N hbnd
  rw [tsum_mul_right, tsum_mul_left] at h
  exact h

end Taylor

end LocalSkewFlow

namespace MobiusCoefficients

 
def step (d : ℕ) : Module.End ℝ (ℤ →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun m =>
    Finsupp.single (m + 1) (((d : ℝ) - 1 - m) / 2) +
    Finsupp.single (m - 1) (((d : ℝ) - 1 + m) / 2))

def InRange (d : ℕ) (f : ℤ →₀ ℝ) : Prop :=
  ∀ m ∈ f.support, -((d : ℤ) - 1) ≤ m ∧ m ≤ (d : ℤ) - 1

def Nonnegative (f : ℤ →₀ ℝ) : Prop := ∀ m, 0 ≤ f m

def total : (ℤ →₀ ℝ) →ₗ[ℝ] ℝ := Finsupp.linearCombination ℝ (fun _ => 1)

lemma step_single (d : ℕ) (m : ℤ) (c : ℝ) :
    step d (Finsupp.single m c) = c •
      (Finsupp.single (m + 1) (((d : ℝ) - 1 - m) / 2) +
       Finsupp.single (m - 1) (((d : ℝ) - 1 + m) / 2)) := by
  exact Finsupp.linearCombination_single ℝ c m

lemma total_single (m : ℤ) (x : ℝ) : total (Finsupp.single m x) = x := by
  simp [total]

lemma total_step (d : ℕ) (f : ℤ →₀ ℝ) : total (step d f) = ((d : ℝ) - 1) * total f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]; ring
  | single m c =>
      rw [step_single, map_smul, map_add, total_single, total_single, total_single]
      simp only [smul_eq_mul]
      ring

lemma step_apply (d : ℕ) (f : ℤ →₀ ℝ) (m : ℤ) :
    step d f m = f.sum (fun j x => x *
      ((Finsupp.single (j + 1) (((d : ℝ) - 1 - j) / 2) : ℤ →₀ ℝ) m +
       (Finsupp.single (j - 1) (((d : ℝ) - 1 + j) / 2) : ℤ →₀ ℝ) m)) := by
  rw [step, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  apply Finsupp.sum_congr
  intro j _
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul]

lemma step_range {d : ℕ} {f : ℤ →₀ ℝ} (hf : InRange d f) : InRange d (step d f) := by
  classical
  intro m hm
  by_contra h
  have hz : step d f m = 0 := by
    rw [step_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hjr := hf j hj
    have hplus : (Finsupp.single (j + 1) (((d : ℝ) - 1 - j) / 2) : ℤ →₀ ℝ) m = 0 := by
      by_cases he : j + 1 = m
      · rw [← he, Finsupp.single_eq_same]
        have heq : j = (d : ℤ) - 1 := by omega
        rw [heq]
        push_cast
        ring
      · exact Finsupp.single_eq_of_ne (Ne.symm he)
    have hminus : (Finsupp.single (j - 1) (((d : ℝ) - 1 + j) / 2) : ℤ →₀ ℝ) m = 0 := by
      by_cases he : j - 1 = m
      · rw [← he, Finsupp.single_eq_same]
        have heq : j = -((d : ℤ) - 1) := by omega
        rw [heq]
        push_cast
        ring
      · exact Finsupp.single_eq_of_ne (Ne.symm he)
    dsimp only
    rw [hplus, hminus]
    ring
  exact Finsupp.mem_support_iff.mp hm hz

lemma step_nonnegative {d : ℕ} {f : ℤ →₀ ℝ} (hr : InRange d f) (hf : Nonnegative f) :
    Nonnegative (step d f) := by
  classical
  intro m
  rw [step_apply]
  apply Finsupp.sum_nonneg
  intro j hj
  have hjr := hr j hj
  have hl : -((d : ℝ) - 1) ≤ (j : ℝ) := by exact_mod_cast hjr.1
  have hu : (j : ℝ) ≤ (d : ℝ) - 1 := by exact_mod_cast hjr.2
  apply mul_nonneg (hf j)
  apply add_nonneg
  · by_cases he : j + 1 = m
    · rw [← he, Finsupp.single_eq_same]
      linarith
    · rw [Finsupp.single_eq_of_ne (Ne.symm he)]
  · by_cases he : j - 1 = m
    · rw [← he, Finsupp.single_eq_same]
      linarith
    · rw [Finsupp.single_eq_of_ne (Ne.symm he)]

def coeff (d n : ℕ) : ℤ →₀ ℝ := (step d ^ n) (Finsupp.single 1 1)

lemma coeff_range {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : InRange d (coeff d n) := by
  induction n with
  | zero =>
      intro m hm
      have he : m = 1 := by simpa [coeff] using hm
      subst m
      constructor <;> omega
  | succ n ih => simpa only [coeff, pow_succ', Module.End.mul_apply] using step_range ih

lemma coeff_nonnegative {d : ℕ} (hd : 2 ≤ d) (n : ℕ) : Nonnegative (coeff d n) := by
  induction n with
  | zero => intro m; simp [coeff, Finsupp.single_apply]; split_ifs <;> norm_num
  | succ n ih =>
      simpa only [coeff, pow_succ', Module.End.mul_apply] using
        step_nonnegative (coeff_range hd n) ih

lemma total_coeff (d n : ℕ) : total (coeff d n) = ((d : ℝ) - 1)^n := by
  induction n with
  | zero => simp [coeff, total_single]
  | succ n ih =>
      simp only [coeff, pow_succ', Module.End.mul_apply]
      rw [total_step]
      change ((d : ℝ) - 1) * total (coeff d n) = _
      rw [ih]

lemma coeff_le_total {d : ℕ} (hd : 2 ≤ d) (n : ℕ) (m : ℤ) :
    coeff d n m ≤ ((d : ℝ) - 1)^n := by
  classical
  rw [← total_coeff]
  by_cases hm : m ∈ (coeff d n).support
  · change coeff d n m ≤ (coeff d n).sum (fun _ x => x • (1 : ℝ))
    simpa only [Finsupp.sum, smul_eq_mul, mul_one] using
      (Finset.single_le_sum (fun j _ => coeff_nonnegative hd n j) hm)
  · rw [Finsupp.notMem_support_iff.mp hm]
    change 0 ≤ (coeff d n).sum (fun _ x => x • (1 : ℝ))
    apply Finsupp.sum_nonneg
    intro i _
    simpa using coeff_nonnegative hd n i

lemma coeff_one_zero (d : ℕ) : coeff d 1 0 = (d : ℝ) / 2 := by
  simp [coeff, step_single]

 
def mean (d : ℕ) (t : ℝ) : ℝ := ∑' n, t^n / (n.factorial : ℝ) * coeff d n 0

lemma summable_mean {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n => t^n / (n.factorial : ℝ) * coeff d n 0) := by
  have hd0 : 0 ≤ (d : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) ≤ (d : ℤ) - 1 by omega)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (coeff_nonnegative hd n 0)) _
    (Real.summable_pow_div_factorial (t * ((d : ℝ) - 1)))
  intro n
  calc
    _ ≤ t^n / (n.factorial : ℝ) * ((d : ℝ) - 1)^n := by
      gcongr
      exact coeff_le_total hd n 0
    _ = _ := by rw [mul_pow]; ring

lemma mean_pos {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 0 < t) : 0 < mean d t := by
  have hsum := summable_mean hd ht.le
  have hle := hsum.le_tsum 1 (fun n _ =>
    mul_nonneg (by positivity) (coeff_nonnegative hd n 0))
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [coeff_one_zero] at hle
  norm_num only [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hle
  exact lt_of_lt_of_le (by positivity) hle

section Representation
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

 
def representation (B : ℤ → E) : (ℤ →₀ ℝ) →ₗ[ℝ] E := Finsupp.linearCombination ℝ B

lemma representation_single (B : ℤ → E) (m : ℤ) (c : ℝ) :
    representation B (Finsupp.single m c) = c • B m :=
  Finsupp.linearCombination_single ℝ c m

lemma representation_step (B : ℤ → E) (L : Module.End ℝ E) (d : ℕ)
    (h : ∀ m, L (B m) = (((d : ℝ) - 1 - m) / 2) • B (m + 1) +
      (((d : ℝ) - 1 + m) / 2) • B (m - 1)) (f : ℤ →₀ ℝ) :
    L (representation B f) = representation B (step d f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m c =>
      rw [representation_single, map_smul, h, step_single, map_smul,
        map_add, representation_single, representation_single]

lemma representation_coeff (B : ℤ → E) (L : Module.End ℝ E) (d : ℕ)
    (h : ∀ m, L (B m) = (((d : ℝ) - 1 - m) / 2) • B (m + 1) +
      (((d : ℝ) - 1 + m) / 2) • B (m - 1)) (n : ℕ) :
    (L^n) (B 1) = representation B (coeff d n) := by
  induction n with
  | zero => simp [coeff, representation_single]
  | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, representation_step B L d h]
      simp only [coeff, pow_succ', Module.End.mul_apply]

 
lemma diagonal_representation (B : ℤ → E) (l : E →ₗ[ℝ] ℂ)
    (h : ∀ m : ℤ, m ≠ 0 → l (B m) = 0) (f : ℤ →₀ ℝ) :
    l (representation B f) = (f 0) • l (B 0) := by
  classical
  rw [representation, Finsupp.linearCombination_apply, map_finsuppSum]
  simp only [map_smul]
  rw [Finsupp.sum_eq_single 0]
  · intro m _ hm
    rw [h m hm, smul_zero]
  · simp

end Representation

end MobiusCoefficients

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ConstrainedSquareBound
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v

namespace SharpColumns
open scoped ComplexConjugate

 

theorem sum_injective_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i)
    (N : ℕ) (hzero : ∀ i, N < i → g i = 0) :
    (∑ i ∈ s, g (f i)) ≤ ∑ i ∈ Finset.range (N + 1), g i := by
  classical
  rw [← Finset.sum_image hf]
  have he : ∑ i ∈ (s.image f).filter (fun i => i ≤ N), g i = ∑ i ∈ s.image f, g i := by
    apply Finset.sum_filter_of_ne
    intro i hi hne
    by_contra h
    exact hne (hzero i (by omega))
  rw [← he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hi).2; omega)
  · intro i _ _
    exact hg i

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

 

theorem row_sq_le {ι : Type*} (s : Finset ι) (T T' : ι → Module.End ℂ V)
    (E : Submodule ℂ V) (K : ℝ) (hK : 0 ≤ K)
    (hadj : ∀ i ∈ s, ∀ v w, inner ℂ (T i v) w = inner ℂ v (T' i w))
    (hcol : ∀ w ∈ E, ∑ i ∈ s, ‖T' i w‖^2 ≤ K * ‖w‖^2)
    (v : ι → V) (z : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ C)
    (hv : (∑ i ∈ s, z i • T i (v i)) ∈ E) :
    ‖∑ i ∈ s, z i • T i (v i)‖^2 ≤ C^2 * K * ∑ i ∈ s, ‖v i‖^2 := by
  classical
  let w := ∑ i ∈ s, z i • T i (v i)
  have hi : ‖w‖^2 ≤ C * ∑ i ∈ s, ‖v i‖ * ‖T' i w‖ := by
    calc
      _ = ‖inner ℂ w w‖ := by rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
      _ = ‖∑ i ∈ s, conj (z i) * inner ℂ (v i) (T' i w)‖ := by
        conv_lhs => arg 1; lhs; rw [show w = ∑ i ∈ s, z i • T i (v i) from rfl]
        rw [sum_inner]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [inner_smul_left, hadj i hi]
      _ ≤ ∑ i ∈ s, ‖conj (z i) * inner ℂ (v i) (T' i w)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, C * (‖v i‖ * ‖T' i w‖) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (hz i hi) (norm_inner_le_norm _ _) (norm_nonneg _) hC
      _ = _ := by rw [Finset.mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖v i‖) (fun i => ‖T' i w‖)
  have hcol' := hcol w hv
  have hsum : 0 ≤ ∑ i ∈ s, ‖v i‖^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq := pow_le_pow_left₀ (sq_nonneg ‖w‖) hi 2
  rw [mul_pow] at hsq
  have hc := mul_le_mul_of_nonneg_left hcs (sq_nonneg C)
  have hk := mul_le_mul_of_nonneg_left hcol' (mul_nonneg (sq_nonneg C) hsum)
  by_cases hw : ‖w‖ = 0
  · change ‖w‖^2 ≤ _
    rw [hw, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hp : 0 < ‖w‖^2 := sq_pos_of_ne_zero hw
    change ‖w‖^2 ≤ _
    apply (mul_le_mul_iff_of_pos_right hp).mp
    nlinarith

omit [InnerProductSpace ℂ V] in
 
theorem finite_sum_sq_le_card {ι : Type*} (s : Finset ι) (v : ι → V) :
    ‖∑ i ∈ s, v i‖^2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖v i‖^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2).trans h

 

theorem triangular_column_sq_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (v : ι → V) (T : κ → ι → Module.End ℂ V)
    (P : κ → ι → Prop) [∀ k i, Decidable (P k i)]
    (z : κ → ι → ℂ) (C K : ℝ)
    (hz : ∀ k ∈ t, ∀ i ∈ s, P k i → ‖z k i‖ ≤ C)
    (hcol : ∀ i ∈ s, ∑ k ∈ t with P k i, ‖T k i (v i)‖^2 ≤ K * ‖v i‖^2) :
    (∑ k ∈ t, ‖∑ i ∈ s with P k i, z k i • T k i (v i)‖^2) ≤
      (s.card : ℝ) * C^2 * K * ∑ i ∈ s, ‖v i‖^2 := by
  classical
  calc
    _ ≤ ∑ k ∈ t, (s.card : ℝ) * C^2 * ∑ i ∈ s with P k i, ‖T k i (v i)‖^2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := finite_sum_sq_le_card (s.filter (P k)) (fun i => z k i • T k i (v i))
      apply hh.trans
      have hc : ((s.filter (P k)).card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Finset.card_filter_le s (P k)
      have hb : ∑ i ∈ s with P k i, ‖z k i • T k i (v i)‖^2 ≤
          C^2 * ∑ i ∈ s with P k i, ‖T k i (v i)‖^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_smul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) (hz k hk i (Finset.mem_filter.mp hi).1
            (Finset.mem_filter.mp hi).2) 2) (sq_nonneg _)
      calc
        _ ≤ (s.card : ℝ) * (C^2 * ∑ i ∈ s with P k i, ‖T k i (v i)‖^2) :=
          mul_le_mul hc hb (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
        _ = _ := by ring
    _ = (s.card : ℝ) * C^2 * ∑ i ∈ s, ∑ k ∈ t with P k i, ‖T k i (v i)‖^2 := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ ≤ _ := by
      rw [mul_assoc _ K]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg C))
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      exact hcol

end SharpColumns

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ColumnControl
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v

namespace SharpColumns
variable {V : Type*} [NormedAddCommGroup V]

theorem norm_add_add_sub_sq_le (x y z t : V) :
    ‖x + y + z - t‖^2 ≤ 4 * (‖x‖^2 + ‖y‖^2 + ‖z‖^2 + ‖t‖^2) := by
  have h := finite_sum_sq_le_card (Finset.univ : Finset (Fin 4)) ![x, y, z, -t]
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

theorem sum_columns_sq_le {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → κ → V) (K : ι → ℝ)
    (H : ∀ i ∈ s, ∑ k ∈ t, ‖f i k‖^2 ≤ K i) :
    (∑ k ∈ t, ‖∑ i ∈ s, f i k‖^2) ≤ (s.card : ℝ) * ∑ i ∈ s, K i := by
  calc
    _ ≤ ∑ k ∈ t, (s.card : ℝ) * ∑ i ∈ s, ‖f i k‖^2 :=
      Finset.sum_le_sum fun k _ => finite_sum_sq_le_card s (fun i => f i k)
    _ = (s.card : ℝ) * ∑ i ∈ s, ∑ k ∈ t, ‖f i k‖^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum H) (Nat.cast_nonneg _)

end SharpColumns

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)


def sharpCorrectionMass (d : ℕ) : ℝ :=
  (d - 1 : ℕ) * ∑ i ∈ Finset.range (d - 1), (i + 1 : ℝ) *
    ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ)^2

theorem sharpCorrectionMass_nonneg (d : ℕ) : 0 ≤ sharpCorrectionMass d := by
  unfold sharpCorrectionMass
  positivity

end CFTTypeVOA

namespace SharpColumns
variable {V : Type*} [NormedAddCommGroup V]
theorem norm_add_sq_le_two (x y : V) : ‖x + y‖^2 ≤ 2 * (‖x‖^2 + ‖y‖^2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
end SharpColumns

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_AdjointMass
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
def adjointMass (d : ℕ) : ℝ :=
  (d + 1 : ℝ) * ∑ j ∈ Finset.range (d + 1), ‖(j.factorial : ℂ)⁻¹‖^2

theorem adjointMass_nonneg (d : ℕ) : 0 ≤ adjointMass d := by unfold adjointMass; positivity

end UnitaryStructure



end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_HilbertCore
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter

open scoped ContDiff



section GraphData
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace ClosedGraphData



theorem commutes_projection_of_reduces (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (Q : H →L[ℂ] H) (hQ : ∀ x ∈ S, Q x ∈ S)
    (hQa : ∀ x ∈ S, Q.adjoint x ∈ S) :
    Q.comp S.starProjection = S.starProjection.comp Q := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hQ _ (S.starProjection_apply_mem x)
  · change Q x - Q (S.starProjection x) ∈ Sᗮ
    rw [← map_sub]
    apply (S.mem_orthogonal' _).mpr
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact (S.mem_orthogonal' _).mp (Submodule.sub_starProjection_mem_orthogonal x)
      _ (hQa y hy)
end ClosedGraphData
end GraphData
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphEquiv
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

open scoped Topology
open Filter
namespace StronglyRationalVOA
namespace SymmetricOperator
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 
def shift (T : H →ₗ.[ℂ] H) (z : ℂ) : H →ₗ.[ℂ] H where
  domain := T.domain
  toFun := T.toFun - z • T.domain.subtype

@[simp] theorem shift_apply (T : H →ₗ.[ℂ] H) (z : ℂ) (x : T.domain) :
    shift T z x = T x - z • (x : H) := rfl

theorem shift_graph (T : H →ₗ.[ℂ] H) (z : ℂ) (x y : H) :
    (x,y) ∈ (shift T z).graph ↔ (x,y+z•x) ∈ T.graph := by
  rw [(shift T z).mem_graph_iff,T.mem_graph_iff]
  dsimp only [Prod.fst,Prod.snd]
  constructor
  · rintro ⟨a,ha,hb⟩
    refine ⟨a,ha,?_⟩
    change T a - z • (a : H) = y at hb
    rw [← ha,← hb]; abel
  · rintro ⟨a,ha,hb⟩
    exact ⟨a,ha,by change T a - z • (a : H) = y; rw [hb,ha]; abel⟩

theorem shift_closed {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) (z : ℂ) :
    (shift T z).IsClosed := by
  have heq : ((shift T z).graph : Set (H × H)) =
      (fun p : H × H => (p.1,p.2+z•p.1)) ⁻¹' T.graph := by
    ext x; exact shift_graph T z x.1 x.2
  rw [LinearPMap.IsClosed,heq]
  exact hT.preimage (continuous_fst.prodMk (continuous_snd.add (continuous_fst.const_smul z)))

theorem real_expectation {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T) (x : T.domain) :
    (inner ℂ (T x) (x : H)).im = 0 := by
  have h := congrArg Complex.im (hs x x)
  have hc := inner_conj_symm (𝕜 := ℂ) (T x) (x : H)
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

theorem shift_I_norm_sq {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T) (x : T.domain) :
    ‖shift T Complex.I x‖^2 = ‖T x‖^2 + ‖(x : H)‖^2 := by
  rw [shift_apply,norm_sub_sq (𝕜 := ℂ),inner_smul_right,norm_smul,Complex.norm_I,one_mul]
  have hh := real_expectation hs x
  simp only [RCLike.re_to_complex,Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,hh,mul_zero,sub_zero]

theorem shift_I_lower_bound {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T) (x : T.domain) :
    ‖(x : H)‖ ≤ ‖shift T Complex.I x‖ := by
  have hh := shift_I_norm_sq hs x
  nlinarith [sq_nonneg ‖T x‖,norm_nonneg (shift T Complex.I x),norm_nonneg (x : H)]

variable [CompleteSpace H]

 

theorem range_closed_of_lower_bound {T : H →ₗ.[ℂ] H} (hT : T.IsClosed)
    (hb : ∀ x : T.domain, ‖(x : H)‖ ≤ ‖T x‖) :
    IsClosed (LinearMap.range T.toFun : Set H) := by
  apply IsSeqClosed.isClosed
  intro a y ha hay
  choose x hx using ha
  change ∀ n, T (x n) = a n at hx
  have hc : CauchySeq (fun n => (x n : H)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hay.cauchySeq ε hε
    refine ⟨N,fun m hm n hn => ?_⟩
    calc
      dist (x m : H) (x n : H) = ‖((x m-x n : T.domain) : H)‖ := by simp [dist_eq_norm]
      _ ≤ ‖T (x m-x n)‖ := hb _
      _ = dist (a m) (a n) := by rw [T.map_sub,hx m,hx n,dist_eq_norm]
      _ < ε := hN m hm n hn
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  have hg : (v,y) ∈ T.graph := hT.mem_of_tendsto (hv.prodMk_nhds hay)
    (Eventually.of_forall (fun n => T.mem_graph_iff.mpr ⟨x n,rfl,hx n⟩))
  obtain ⟨w,_,hw⟩ := T.mem_graph_iff.mp hg
  exact ⟨w,hw⟩

 

theorem orthogonal_range_shift {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (z : ℂ) {y : H}
    (hy : y ∈ (LinearMap.range (shift T z).toFun)ᗮ) :
    (y,star z • y) ∈ T.adjoint.graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro a b hab
  obtain ⟨x,hx,hTx⟩ := T.mem_graph_iff.mp hab
  dsimp only [Prod.fst,Prod.snd] at hx hTx
  have hh := ((LinearMap.range (shift T z).toFun).mem_orthogonal y).mp hy
    (shift T z x) ⟨x,rfl⟩
  rw [shift_apply,inner_sub_left,inner_smul_left] at hh
  rw [← hx,← hTx,inner_smul_right]
  simpa only [starRingEnd_apply] using hh

 

theorem selfAdjoint_of_deficiency_zero {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (hT : T.IsClosed) (hs : T.IsFormalAdjoint T)
    (hp : ∀ y : H, (y,Complex.I • y) ∈ T.adjoint.graph → y = 0)
    (hm : ∀ y : H, (y,(-Complex.I) • y) ∈ T.adjoint.graph → y = 0) :
    IsSelfAdjoint T := by
  have hclosed : IsClosed (LinearMap.range (shift T Complex.I).toFun : Set H) :=
    range_closed_of_lower_bound (shift_closed hT _) (shift_I_lower_bound hs)
  let : IsClosed (LinearMap.range (shift T Complex.I).toFun : Set H) := hclosed
  have hr : LinearMap.range (shift T Complex.I).toFun = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    apply hm y
    simpa only [Complex.star_def,Complex.conj_I] using orthogonal_range_shift hd Complex.I hy
  have hle : T ≤ T.adjoint := hs.le_adjoint hd
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm _ hle
  apply LinearPMap.le_of_le_graph
  intro p hpgraph
  obtain ⟨y,hy,hTy⟩ := T.adjoint.mem_graph_iff.mp hpgraph
  have hv : T.adjoint y - Complex.I • (y : H) ∈ LinearMap.range (shift T Complex.I).toFun := by
    rw [hr]; trivial
  obtain ⟨x,hx⟩ := hv
  have hxadj : (x : H) ∈ T.adjoint.domain := hle.1 x.property
  let x' : T.adjoint.domain := ⟨x,hxadj⟩
  have hTx : T.adjoint x' = T x := by
    exact (hle.2 (x := x) (y := x') rfl).symm
  have hzero : (y : H) - x = 0 := by
    apply hp
    refine T.adjoint.mem_graph_iff.mpr ⟨y-x',rfl,?_⟩
    rw [T.adjoint.map_sub,hTx]
    change T x - Complex.I • (x : H) = T.adjoint y - Complex.I • (y : H) at hx
    simp only [smul_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mpr hx.symm
  have hxy : (x : H) = (y : H) := (sub_eq_zero.mp hzero).symm
  refine T.mem_graph_iff.mpr ⟨x,hxy.trans hy,?_⟩
  rw [← hTy,← hTx]
  congr 1
  exact Subtype.ext hxy



theorem regularizer_adjoint {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (R B : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hg : ∀ x : H, (R x,B x) ∈ T.graph)
    {y z : H} (hy : (y,z) ∈ T.adjoint.graph) :
    B.adjoint y = R z := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hh := (Submodule.mem_adjoint_iff _ _).mp
    (by rwa [← LinearPMap.adjoint_graph_eq_graph_adjoint hd] : (y,z) ∈ T.graph.adjoint)
    (R x) (B x) (hg x)
  have hRadj : R.adjoint = R := hR
  rw [← hRadj,ContinuousLinearMap.adjoint_inner_right]
  exact sub_eq_zero.mp hh

 

theorem selfAdjoint_of_regularizers {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (hT : T.IsClosed) (hs : T.IsFormalAdjoint T)
    (R B : ℕ → H →L[ℂ] H)
    (hR : ∀ n, IsSelfAdjoint (R n))
    (hg : ∀ n x, (R n x,B n x) ∈ T.graph)
    (hlim : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 x))
    (hcomm : ∀ x, Tendsto (fun n => (B n - (B n).adjoint) x) atTop (𝓝 0)) :
    IsSelfAdjoint T := by
  have hreal : ∀ y z : H, (y,z) ∈ T.adjoint.graph → (inner ℂ z y).im = 0 := by
    intro y z hy
    have hBadj : ∀ n, (B n).adjoint y = R n z :=
      fun n => regularizer_adjoint hd (R n) (B n) (hR n) (hg n) hy
    have hBl : Tendsto (fun n => B n y) atTop (𝓝 z) := by
      have hh := (hcomm y).add (hlim z)
      simp only [sub_apply,← hBadj,sub_add_cancel,zero_add] at hh
      exact hh
    have hre : ∀ n, (inner ℂ (B n y) (R n y)).im = 0 := by
      intro n
      obtain ⟨x,hx,hBx⟩ := T.mem_graph_iff.mp (hg n y)
      dsimp only [Prod.fst,Prod.snd] at hx hBx
      rw [← hx,← hBx]
      exact real_expectation hs x
    have hilt := Complex.continuous_im.continuousAt.tendsto.comp (hBl.inner (hlim y))
    have heq : (fun n => (inner ℂ (B n y) (R n y)).im) = fun _ => (0 : ℝ) := funext hre
    change Tendsto (fun n => (inner ℂ (B n y) (R n y)).im) atTop (𝓝 _) at hilt
    rw [heq] at hilt
    exact (tendsto_nhds_unique hilt tendsto_const_nhds)
  apply selfAdjoint_of_deficiency_zero hd hT hs
  · intro y hy
    have hh := hreal y (Complex.I • y) hy
    rw [inner_smul_left] at hh
    simp only [Complex.conj_I,neg_mul,Complex.mul_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,Complex.neg_im,
      inner_self_eq_norm_sq_to_K] at hh
    have hy0 : ‖y‖^2 = 0 := by
      simp only [neg_eq_zero] at hh
      change ((‖y‖ : ℂ)^2).re = 0 at hh
      simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hy0)
  · intro y hy
    have hh := hreal y ((-Complex.I) • y) hy
    rw [inner_smul_left] at hh
    simp only [map_neg,Complex.conj_I,neg_neg,Complex.mul_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,
      inner_self_eq_norm_sq_to_K] at hh
    have hy0 : ‖y‖^2 = 0 := by
      change ((‖y‖ : ℂ)^2).re = 0 at hh
      simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hy0)

end SymmetricOperator
end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BoundedMultiplierSingle
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
universe u
open scoped Topology
open Filter
namespace StronglyRationalVOA

namespace StrongOperatorLimit
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

 

theorem zero_of_dense {S : Submodule ℂ H} (hS : Dense (S : Set H))
    (B : ℕ → H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C) (hB : ∀ n, ‖B n‖ ≤ C)
    (hlim : ∀ x ∈ S, Tendsto (fun n => B n x) atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => B n x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := hS.exists_dist_lt x (show 0 < ε/(2*(C+1)) by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hlim y hy) (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hyb : ‖B n y‖ < ε/2 := by simpa using hN n hn
  have hxy' : ‖x-y‖*(2*(C+1)) < ε := by
    rw [dist_eq_norm] at hxy
    exact (lt_div_iff₀ (by positivity)).mp hxy
  rw [dist_zero_right]
  calc
    ‖B n x‖ = ‖B n (x-y) + B n y‖ := by rw [map_sub,sub_add_cancel]
    _ ≤ ‖B n (x-y)‖ + ‖B n y‖ := norm_add_le _ _
    _ ≤ C*‖x-y‖ + ‖B n y‖ := add_le_add ((B n).le_of_opNorm_le (hB n) _) le_rfl
    _ < ε := by nlinarith [norm_nonneg (x-y)]

end StrongOperatorLimit

end StronglyRationalVOA

namespace StronglyRationalVOA

theorem summable_inner_left {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {g : ι → H} (hg : Summable g) (y : H) :
    Summable (fun i => inner ℂ (g i) y) :=
  ((innerSL ℂ).flip y).summable hg

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GeneratorSharpGrowth
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v

namespace CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (A : CFTTypeVOA V)

omit [InnerProductSpace ℂ V] in
 

theorem norm_of_sharp_square {X : ℝ} (hX : 0 ≤ X) {C : ℝ} (hC : 0 ≤ C)
    (N r s : ℕ) (v w : V)
    (H : ‖w‖^2 ≤ C * (N+1 : ℝ)^(2*r) * X^(2*s) * ‖v‖^2) :
    ‖w‖ ≤ (C+1) * (N+1 : ℝ)^r * X^s * ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ C * (N+1 : ℝ)^(2*r) * X^(2*s) * ‖v‖^2 := H
    _ ≤ (C+1)^2 * (N+1 : ℝ)^(2*r) * X^(2*s) * ‖v‖^2 := by
      gcongr
      nlinarith [sq_nonneg C]
    _ = _ := by simp only [mul_pow, pow_mul, mul_comm 2 r, mul_comm 2 s]

theorem reduced_commutator_coefficient_bound {d : ℕ} (hd : 1 ≤ d) (m j : ℕ)
    (hj : j < 2*d-1) :
    ‖((m+d-1).choose (j+1) : ℂ) - ((d-1).choose (j+1) : ℂ)‖ ≤
      (2 : ℝ)*(d+1 : ℝ)^(2*d)*(m+1 : ℝ)^(2*d) := by
  have hchoose (n : ℕ) (hn : n ≤ (d+1)*(m+1)) :
      (n.choose (j+1) : ℝ) ≤ (d+1 : ℝ)^(2*d)*(m+1 : ℝ)^(2*d) := by
    have H : n.choose (j+1) ≤ ((d+1)*(m+1))^(2*d) :=
      (Nat.choose_le_pow n (j+1)).trans
        ((Nat.pow_le_pow_left hn (j+1)).trans (Nat.pow_le_pow_right (by positivity) (by omega)))
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_pow] using
      (show (n.choose (j+1) : ℝ) ≤ (((d+1)*(m+1) : ℕ) : ℝ)^(2*d) from by exact_mod_cast H)
  have H := hchoose (m+d-1) (by nlinarith [Nat.sub_le (m+d) 1])
  have K := hchoose (d-1) (by nlinarith [Nat.sub_le d 1])
  calc
    _ ≤ ‖((m+d-1).choose (j+1) : ℂ)‖ + ‖((d-1).choose (j+1) : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by simp only [Complex.norm_natCast]; linarith



end CFTTypeVOA

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CutoffPowerControl
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
def CutoffPowerControl (Y : ℕ → ℝ) (P : ℕ) (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N, f N^P ≤ C*Y N

theorem cutoffPowerControl_add {Y f g : ℕ → ℝ} {P : ℕ}
    (hf : ∀ N, 0 ≤ f N) (hg : ∀ N, 0 ≤ g N)
    (Hf : CutoffPowerControl Y P f) (Hg : CutoffPowerControl Y P g) :
    CutoffPowerControl Y P (fun N => f N+g N) := by
  obtain ⟨C, hC, HC⟩ := Hf
  obtain ⟨D, hD, HD⟩ := Hg
  refine ⟨2^(P-1)*(C+D), by positivity, ?_⟩
  intro N
  calc
    _ ≤ 2^(P-1)*(f N^P+g N^P) := add_pow_le (hf N) (hg N) P
    _ ≤ 2^(P-1)*(C*Y N+D*Y N) := by gcongr; exacts [HC N, HD N]
    _ = _ := by ring

theorem cutoffPowerControl_sum {Y : ℕ → ℝ} {P : ℕ}
    (hP : 1 ≤ P) {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, ∀ N, 0 ≤ f i N)
    (H : ∀ i ∈ s, CutoffPowerControl Y P (f i)) :
    CutoffPowerControl Y P (fun N => ∑ i ∈ s, f i N) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, by simp [show P ≠ 0 by omega]⟩
  | @insert i s hi ih =>
    have hsum := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => H j (Finset.mem_insert_of_mem hj))
    have h := cutoffPowerControl_add (hf i (Finset.mem_insert_self _ _))
      (fun N => Finset.sum_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj) N))
      (H i (Finset.mem_insert_self _ _)) hsum
    simpa only [Finset.sum_insert hi] using h

theorem cutoffPowerControl_one {Y : ℕ → ℝ} (hY : ∀ N, 1 ≤ Y N) (P : ℕ) :
    CutoffPowerControl Y P (fun _ => 1) :=
  ⟨1, zero_le_one, by simpa using hY⟩

 

theorem root_lift_power_bound {q X C : ℝ} {p P : ℕ} (hq : 0 ≤ q) (hX : 0 ≤ X)
    (hC : 0 ≤ C) (hp : 1 ≤ p) (hpP : p ≤ P)
    (hroot : q^((p : ℝ)⁻¹) ≤ X) (H : q ≤ C*X^(p-1)) :
    (q^((p : ℝ)⁻¹))^P ≤ C*X^(P-1) := by
  have hqroot := Real.rpow_nonneg hq ((p : ℝ)⁻¹)
  calc
    _ = (q^((p : ℝ)⁻¹))^p * (q^((p : ℝ)⁻¹))^(P-p) := by
      rw [← pow_add, Nat.add_sub_of_le hpP]
    _ = q*(q^((p : ℝ)⁻¹))^(P-p) := by
      rw [Real.rpow_inv_natCast_pow hq (by omega)]
    _ ≤ (C*X^(p-1))*X^(P-p) := by gcongr
    _ = _ := by rw [mul_assoc, ← pow_add, show p-1+(P-p) = P-1 by omega]

def PolynomialCutoffControl (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ, ∀ N, f N ≤ C*(N+1 : ℝ)^p

theorem polynomialCutoffControl_add {f g : ℕ → ℝ}
    (Hf : PolynomialCutoffControl f) (Hg : PolynomialCutoffControl g) :
    PolynomialCutoffControl (fun N => f N+g N) := by
  obtain ⟨C, hC, p, HC⟩ := Hf
  obtain ⟨D, hD, q, HD⟩ := Hg
  refine ⟨C+D, add_nonneg hC hD, p+q, ?_⟩
  intro N
  have hN : 1 ≤ (N+1 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have Hp := pow_le_pow_right₀ hN (show p ≤ p+q by omega)
  have Hq := pow_le_pow_right₀ hN (show q ≤ p+q by omega)
  calc
    _ ≤ C*(N+1 : ℝ)^p+D*(N+1 : ℝ)^q := add_le_add (HC N) (HD N)
    _ ≤ C*(N+1 : ℝ)^(p+q)+D*(N+1 : ℝ)^(p+q) := by gcongr
    _ = _ := by ring

theorem polynomialCutoffControl_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (H : ∀ i ∈ s, PolynomialCutoffControl (f i)) :
    PolynomialCutoffControl (fun N => ∑ i ∈ s, f i N) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, 0, by simp⟩
  | @insert i s hi ih =>
    have h := polynomialCutoffControl_add (H i (Finset.mem_insert_self _ _))
      (ih (fun j hj => H j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

theorem polynomialCutoffControl_one : PolynomialCutoffControl (fun _ => 1) :=
  ⟨1, zero_le_one, 0, by simp⟩

theorem rpow_inv_nat_le_one_add {q : ℝ} (hq : 0 ≤ q) {p : ℕ} (hp : 1 ≤ p) :
    q^((p : ℝ)⁻¹) ≤ 1+q := by
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  rcases le_total q 1 with hq1 | hq1
  · exact (Real.rpow_le_one hq hq1 (by positivity)).trans (le_add_of_nonneg_right hq)
  · apply (Real.rpow_le_self_of_one_le hq1 ((inv_le_one₀ hp0).mpr hpR)).trans
    linarith

theorem polynomialCutoffControl_root {f : ℕ → ℝ} (hf : ∀ N, 0 ≤ f N)
    (H : PolynomialCutoffControl f) {p : ℕ} (hp : 1 ≤ p) :
    PolynomialCutoffControl (fun N => f N^((p : ℝ)⁻¹)) := by
  obtain ⟨C, hC, k, HC⟩ := polynomialCutoffControl_add polynomialCutoffControl_one H
  exact ⟨C, hC, k, fun N => (rpow_inv_nat_le_one_add (hf N) hp).trans (HC N)⟩

open Filter
 

theorem multiplicative_cutoff_log_bound (b : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (ρ c C s : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 ≤ c)
    (hstart : ∀ N, 1 ≤ N → b N ≤ C + s * Real.log N)
    (hstep : ∀ N, 1 ≤ N → b N ≤ c + ρ * b (K * N)) :
    ∀ N, 1 ≤ N → b N ≤ c / (1 - ρ) := by
  let B := c / (1 - ρ)
  have hden : 0 < 1 - ρ := sub_pos.mpr hρ1
  have hB0 : 0 ≤ B := div_nonneg hc hden.le
  have hB : c + ρ * B = B := by dsimp [B]; field_simp; ring
  have hit (j : ℕ) : ∀ N, 1 ≤ N → b N - B ≤ ρ ^ j * b (K ^ j * N) := by
    induction j with
    | zero => intro N hN; simpa using sub_le_self (b N) hB0
    | succ j ih =>
      intro N hN
      have hKN : 1 ≤ K * N := by nlinarith
      calc
        _ ≤ ρ * (b (K * N) - B) := by nlinarith [hstep N hN]
        _ ≤ ρ * (ρ^j * b (K^j * (K * N))) :=
          mul_le_mul_of_nonneg_left (ih _ hKN) hρ0
        _ = _ := by
          rw [show K^j * (K * N) = K^(j+1) * N by rw [pow_succ]; ring, pow_succ]
          ring
  intro N hN
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb (j : ℕ) : b N - B ≤
      ρ ^ j * (C + s * Real.log N + s * (j : ℝ) * Real.log K) := by
    apply (hit j N hN).trans
    have hp : 1 ≤ K^j * N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (pow_ne_zero _ (by omega)) (by omega))
    have he : Real.log ((K^j * N : ℕ) : ℝ) = (j : ℝ) * Real.log K + Real.log N := by
      push_cast
      rw [Real.log_mul (pow_ne_zero _ hKpos.ne') hNpos.ne', Real.log_pow]
    have h := mul_le_mul_of_nonneg_left (hstart _ hp) (pow_nonneg hρ0 j)
    rw [he] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have ht : Tendsto (fun j : ℕ =>
      ρ ^ j * (C + s * Real.log N + s * (j : ℝ) * Real.log K)) atTop (nhds 0) := by
    have h₀ := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have h₁ := tendsto_pow_const_mul_const_pow_of_lt_one 1 hρ0 hρ1
    have h := (h₀.const_mul (C + s * Real.log N)).add (h₁.const_mul (s * Real.log K))
    convert h using 1
    · ext j; ring
    · simp
  have hlast : b N - B ≤ 0 := ge_of_tendsto' ht hb
  exact sub_nonpos.mp hlast

 

theorem polynomial_power_contraction_bounded (X : ℕ → ℝ) (hX : ∀ N, 1 ≤ X N)
    (hm : Monotone X) (hp : PolynomialCutoffControl X)
    (K P : ℕ) (hK : 1 ≤ K) (hP : 1 ≤ P) (C : ℝ) (hC : 1 ≤ C)
    (H : ∀ N, X N^P ≤ C*X (K*N)^(P-1)) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ N, X N ≤ B := by
  obtain ⟨D, hD, p, HD⟩ := hp
  let A := (D+1)*2^p
  have hA : 0 < A := by dsimp [A]; positivity
  have hPR : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hPR1 : 1 ≤ (P : ℝ) := by exact_mod_cast hP
  let ρ : ℝ := 1-(P : ℝ)⁻¹
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; linarith [(inv_le_one₀ hPR).mpr hPR1]
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [inv_pos.mpr hPR]
  let c := Real.log C/(P : ℝ)
  have hc : 0 ≤ c := div_nonneg (Real.log_nonneg hC) hPR.le
  have hstart (N : ℕ) (hN : 1 ≤ N) : Real.log (X N) ≤ Real.log A + (p : ℝ)*Real.log N := by
    have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNR : (0 : ℝ) < N := by linarith
    have HX : X N ≤ A*(N : ℝ)^p := by
      apply (HD N).trans
      calc
        _ ≤ (D+1)*(2*(N : ℝ))^p := by gcongr <;> linarith
        _ = _ := by dsimp [A]; rw [mul_pow]; ring
    have HH := Real.log_le_log (by linarith [hX N] : 0 < X N) HX
    rwa [Real.log_mul hA.ne' (pow_pos hNR p).ne', Real.log_pow] at HH
  have hstep (N : ℕ) (_hN : 1 ≤ N) : Real.log (X N) ≤ c+ρ*Real.log (X (K*N)) := by
    have hx : 0 < X N := by linarith [hX N]
    have hy : 0 < X (K*N) := by linarith [hX (K*N)]
    have HL := Real.log_le_log (pow_pos hx P) (H N)
    rw [Real.log_mul (by linarith : C ≠ 0) (pow_ne_zero _ hy.ne'), Real.log_pow,
      Real.log_pow, Nat.cast_sub hP, Nat.cast_one] at HL
    have he : c+ρ*Real.log (X (K*N)) =
        (Real.log C+((P : ℝ)-1)*Real.log (X (K*N)))/(P : ℝ) := by
      dsimp [c, ρ]
      field_simp
    rw [he]
    exact (le_div_iff₀ hPR).mpr (by simpa only [mul_comm] using HL)
  have HB := multiplicative_cutoff_log_bound (fun N => Real.log (X N)) K hK
    ρ c (Real.log A) p hρ0 hρ1 hc hstart hstep
  let B := Real.exp (c/(1-ρ))
  have HB1 : 1 ≤ B := Real.one_le_exp_iff.mpr (div_nonneg hc (by linarith))
  have HBN (N : ℕ) (hN : 1 ≤ N) : X N ≤ B := by
    have hx : 0 < X N := by linarith [hX N]
    simpa [B, Real.exp_log hx] using Real.exp_le_exp.mpr (HB N hN)
  exact ⟨B, HB1, fun N => if hN : 1 ≤ N then HBN N hN else
    (hm (show N ≤ 1 by omega)).trans (HBN 1 le_rfl)⟩

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SummableNormSobolev
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u v

noncomputable section
open scoped Topology
open Filter

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem shift_im_lower_bound {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T)
    (z : ℂ) (x : T.domain) : |z.im| *‖(x : H)‖ ≤ ‖shift T z x‖ := by
  have him : (inner ℂ (shift T z x) (x : H)).im = z.im*‖(x : H)‖^2 := by
    rw [shift_apply,inner_sub_left,inner_smul_left,inner_self_eq_norm_sq_to_K]
    change (inner ℂ (T x) (x : H)).im - (star z * (‖(x : H)‖ : ℂ)^2).im = _
    rw [real_expectation hs x,← Complex.ofReal_pow]
    simp only [Complex.mul_im,Complex.star_def,Complex.conj_im,
      Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add,neg_mul,zero_sub,neg_neg]
  have hi := (Complex.abs_im_le_norm (inner ℂ (shift T z x) (x : H))).trans
    (norm_inner_le_norm (shift T z x) (x : H))
  rw [him,abs_mul,abs_of_nonneg (sq_nonneg ‖(x : H)‖)] at hi
  by_cases hx : ‖(x : H)‖ = 0
  · rw [hx,mul_zero]; positivity
  · have hxpos := lt_of_le_of_ne (norm_nonneg (x : H)) (Ne.symm hx)
    nlinarith

variable [CompleteSpace H]

theorem selfAdjoint_formal {T : H →ₗ.[ℂ] H} (hs : IsSelfAdjoint T) :
    T.IsFormalAdjoint T := by
  have h := LinearPMap.adjoint_isFormalAdjoint hs.dense_domain
  rwa [show T.adjoint = T from hs] at h

 

theorem shift_bijective {T : H →ₗ.[ℂ] H} (hs : IsSelfAdjoint T)
    (z : ℂ) (hz : 1 ≤ |z.im|) : Function.Bijective (shift T z).toFun := by
  have hf := selfAdjoint_formal hs
  have hb : ∀ x : T.domain, ‖(x : H)‖ ≤ ‖shift T z x‖ := by
    intro x
    exact (le_mul_of_one_le_left (norm_nonneg _) hz).trans (shift_im_lower_bound hf z x)
  have hclosed := range_closed_of_lower_bound (shift_closed hs.isClosed z) hb
  let : IsClosed (LinearMap.range (shift T z).toFun : Set H) := hclosed
  have hr : LinearMap.range (shift T z).toFun = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hg := orthogonal_range_shift hs.dense_domain z hy
    rw [show T.adjoint = T from hs] at hg
    obtain ⟨x,hx,he⟩ := T.mem_graph_iff.mp hg
    have hi := real_expectation hf x
    rw [he,hx,inner_smul_left,inner_self_eq_norm_sq_to_K] at hi
    simp only [starRingEnd_apply,star_star] at hi
    change (z*(‖y‖ : ℂ)^2).im = 0 at hi
    rw [← Complex.ofReal_pow,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_add] at hi
    have him : z.im ≠ 0 := by intro h; rw [h,abs_zero] at hz; norm_num at hz
    have hn : ‖y‖^2 = 0 := (mul_eq_zero.mp hi).resolve_left him
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  constructor
  · change Function.Injective (fun x : T.domain => shift T z x)
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have h := hb (x-y)
    change ‖((x-y : T.domain) : H)‖ ≤ ‖(T.toFun-z • T.domain.subtype) (x-y)‖ at h
    change (T.toFun-z • T.domain.subtype) x = (T.toFun-z • T.domain.subtype) y at hxy
    rw [map_sub,hxy,sub_self,norm_zero] at h
    exact le_antisymm h (norm_nonneg _)
  · exact LinearMap.range_eq_top.mp hr

 
def resolvent (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) : H →L[ℂ] H :=
  (T.domain.subtype.comp (LinearEquiv.ofBijective (shift T z).toFun (shift_bijective hs z hz)).symm.toLinearMap).mkContinuous
    |z.im|⁻¹ (by
      intro y
      let x := (LinearEquiv.ofBijective (shift T z).toFun (shift_bijective hs z hz)).symm y
      have hx : shift T z x = y := (LinearEquiv.ofBijective (shift T z).toFun
        (shift_bijective hs z hz)).apply_symm_apply y
      have h := shift_im_lower_bound (selfAdjoint_formal hs) z x
      rw [hx] at h
      change ‖(x : H)‖ ≤ |z.im|⁻¹*‖y‖
      exact (le_inv_mul_iff₀ (lt_of_lt_of_le zero_lt_one hz)).mpr h)

theorem resolvent_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) (y : H) :
    (resolvent T hs z hz y,y+z•resolvent T hs z hz y) ∈ T.graph := by
  apply (shift_graph T z _ _).mp
  exact (shift T z).mem_graph_iff.mpr ⟨_,rfl,
    (LinearEquiv.ofBijective (shift T z).toFun (shift_bijective hs z hz)).apply_symm_apply y⟩

theorem resolvent_shift (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|)
    (x : T.domain) : resolvent T hs z hz (T x-z•(x : H)) = (x : H) := by
  obtain ⟨y,hy,he⟩ := T.mem_graph_iff.mp
    (resolvent_graph T hs z hz (T x-z•(x : H)))
  dsimp only [Prod.fst,Prod.snd] at hy he
  have hshift : shift T z y = shift T z x := by
    rw [shift_apply,shift_apply,he,hy,add_sub_cancel_right]
  have heq : y = x := (shift_bijective hs z hz).injective hshift
  exact hy.symm.trans (congrArg Subtype.val heq)

theorem resolvent_norm_le (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) :
    ‖resolvent T hs z hz‖ ≤ |z.im|⁻¹ := by
  exact LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr (abs_nonneg _)) _

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolvent_adjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) :
    (resolvent T hs z hz).adjoint =
      resolvent T hs (star z) (by simpa only [Complex.star_def,Complex.conj_im,abs_neg] using hz) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨a,ha,hTa⟩ := T.mem_graph_iff.mp (resolvent_graph T hs z hz x)
  obtain ⟨b,hb,hTb⟩ := T.mem_graph_iff.mp (resolvent_graph T hs (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,abs_neg] using hz) y)
  dsimp only [Prod.fst,Prod.snd] at ha hb hTa hTb
  have h := selfAdjoint_formal hs a b
  rw [hTa,hTb,ha,hb,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right] at h
  exact (add_right_cancel (show inner ℂ x (resolvent T hs (star z) _ y) +
      star z * inner ℂ (resolvent T hs z hz x) (resolvent T hs (star z) _ y) =
    inner ℂ (resolvent T hs z hz x) y +
      star z * inner ℂ (resolvent T hs z hz x) (resolvent T hs (star z) _ y) from h)).symm



end StronglyRationalVOA.SymmetricOperator

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_InverseEnergySelf
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



theorem graph_invariant_of_commutes_resolvent (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (z : ℂ) (hz : 1 ≤ |z.im|) (Q : H →L[ℂ] H)
    (hq : Q * resolvent T hs z hz = resolvent T hs z hz * Q) :
    ∀ x y, (x,y) ∈ T.graph → (Q x,Q y) ∈ T.graph := by
  intro x y hxy
  obtain ⟨u,hu,hTu⟩ := T.mem_graph_iff.mp hxy
  dsimp only [Prod.fst,Prod.snd] at hu hTu
  have hr := resolvent_shift T hs z hz u
  rw [hu,hTu] at hr
  have hqr : resolvent T hs z hz (Q (y-z•x)) = Q x := by
    rw [← show Q (resolvent T hs z hz (y-z•x)) = resolvent T hs z hz (Q (y-z•x)) from
      congrArg (fun L : H →L[ℂ] H => L (y-z•x)) hq,hr]
  have hg := resolvent_graph T hs z hz (Q (y-z•x))
  rwa [hqr,map_sub,map_smul,sub_add_cancel] at hg

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.FourierAnalysis
open MeasureTheory AddCircle
variable {T : ℝ} [Fact (0 < T)]

 
def coefficientCLM (n : ℤ) : C(AddCircle T,ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => fourierCoeff f n
      map_add' := by
        intro f g
        exact congrFun (fourierCoeff.add
          (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) n
      map_smul' := by
        intro c f
        exact fourierCoeff.const_smul f c n } 1 (by
      intro f
      change ‖∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle‖ ≤ 1*‖f‖
      have H := norm_integral_le_of_norm_le_const (μ := (haarAddCircle : Measure (AddCircle T)))
        (f := fun t => fourier (-n) t • f t) (C := ‖f‖) (Filter.Eventually.of_forall (by
          intro t
          rw [norm_smul,show ‖fourier (-n) t‖ = 1 from Circle.norm_coe _,one_mul]
          exact f.norm_coe_le_norm t))
      simpa using H)

@[simp] theorem coefficientCLM_apply (n : ℤ) (f : C(AddCircle T,ℂ)) :
    coefficientCLM n f = fourierCoeff f n := rfl

 
theorem coefficient_character_mul (g : C(AddCircle T,ℂ)) (m n : ℤ) :
    fourierCoeff ((fourier m : C(AddCircle T,ℂ))*g) n = fourierCoeff g (n-m) := by
  unfold fourierCoeff
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  change fourier (-n) t * (fourier m t * g t) = fourier (-(n-m)) t * g t
  rw [← mul_assoc,← fourier_add]
  rw [show -n+m = -(n-m) by omega]

 

theorem hasSum_coefficient_product (f g : C(AddCircle T,ℂ))
    (hf : Summable (fourierCoeff f)) (n : ℤ) :
    HasSum (fun m : ℤ => fourierCoeff f m * fourierCoeff g (n-m))
      (fourierCoeff (f*g) n) := by
  have H := (coefficientCLM (T := T) n).hasSum
    ((hasSum_fourier_series_of_summable hf).mul_right g)
  convert H using 1
  · ext m
    change _ = fourierCoeff ((fourierCoeff f m • (fourier m : C(AddCircle T,ℂ)))*g) n
    rw [smul_mul_assoc]
    change _ = fourierCoeff (fourierCoeff f m • (((fourier m : C(AddCircle T,ℂ))*g) : AddCircle T → ℂ)) n
    rw [fourierCoeff.const_smul,smul_eq_mul]
    change _ = fourierCoeff f m * fourierCoeff ((fourier m : C(AddCircle T,ℂ))*g) n
    rw [coefficient_character_mul]
  · rfl

end StronglyRationalVOA.FourierAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_BoundedFlows
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter

open scoped Topology
open Filter
namespace StronglyRationalVOA.StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma equicontinuous_of_norm_bound {ι : Type*} (F : ι → H →L[ℂ] H) {C : ℝ}
    (hF : ∀ n, ‖F n‖ ≤ C) : Equicontinuous (fun n => (F n : H → H)) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun t : ℝ => C*t)
    (by
      convert (continuous_const.mul continuous_id : Continuous (fun t : ℝ => C*t)).tendsto
        (0 : ℝ) using 1
      all_goals try with_reducible_and_instances rfl
      simp)
  intro x y n
  rw [dist_eq_norm,← map_sub,dist_eq_norm]
  exact (F n).le_of_opNorm_le (hF n) (x-y)

lemma exists_of_dense_core (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (F : ℕ → H →L[ℂ] H) {C : ℝ} (hF : ∀ n, ‖F n‖ ≤ C)
    (hcore : ∀ x : D, CauchySeq (fun n => F n x)) :
    ∃ L : H →L[ℂ] H, ∀ x : H, Tendsto (fun n => F n x) atTop (𝓝 (L x)) := by
  choose f hf using fun x : D => cauchySeq_tendsto_of_complete (hcore x)
  let B : D →ₗ[ℂ] H :=
    { toFun := f
      map_add' := by
        intro x y
        apply tendsto_nhds_unique (hf (x+y))
        simpa only [Submodule.coe_add,map_add] using (hf x).add (hf y)
      map_smul' := by
        intro c x
        apply tendsto_nhds_unique (hf (c • x))
        simpa only [Submodule.coe_smul,map_smul,RingHom.id_apply] using (hf x).const_smul c }
  have hb : ∀ x : D, ‖B x‖ ≤ C*‖x‖ := by
    intro x
    apply le_of_tendsto (hf x).norm
    exact Filter.Eventually.of_forall fun n => (F n).le_of_opNorm_le (hF n) x
  let K := B.mkContinuous C hb
  let L := K.extend D.subtypeL
  have hd : DenseRange D.subtypeL := by
    change Dense (Set.range (D.subtypeL : D → H))
    have hr : Set.range (D.subtypeL : D → H) = (D : Set H) := by
      ext x
      exact ⟨by rintro ⟨y,rfl⟩; exact y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
    rw [hr]
    exact hD
  have he : IsUniformInducing D.subtypeL := D.subtypeₗᵢ.isometry.isUniformInducing
  have hc := (equicontinuous_of_norm_bound F hF).isClosed_setOfPred_tendsto (l := atTop) L.continuous
  refine ⟨L,fun x => ?_⟩
  apply (closure_minimal (s := (D : Set H)) (t := {x | Tendsto (fun n => F n x) atTop (𝓝 (L x))}) ?_ hc) (hD x)
  intro x hx
  let v : D := ⟨x,hx⟩
  change Tendsto (fun n => F n (v : H)) atTop (𝓝 (K.extend D.subtypeL (D.subtypeL v)))
  rw [ContinuousLinearMap.extend_eq K hd he]
  exact hf v

omit [CompleteSpace H] in
lemma mul_tendsto (F G : ℕ → H →L[ℂ] H) (A B : H →L[ℂ] H) {C : ℝ}
    (hF : ∀ n, ‖F n‖ ≤ C)
    (hf : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (A x)))
    (hg : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (B x))) (x : H) :
    Tendsto (fun n => F n (G n x)) atTop (𝓝 (A (B x))) := by
  have hz : Tendsto (fun n => F n (G n x-B x)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => C*‖G n x-B x‖)
    · exact fun n => (F n).le_of_opNorm_le (hF n) _
    · simpa only [sub_self,norm_zero,mul_zero] using
        (tendsto_const_nhds.mul ((hg x).sub_const (B x)).norm)
  have h := hz.add (hf (B x))
  simpa only [map_sub,sub_add_cancel,zero_add] using h

end StronglyRationalVOA.StrongLimit

open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma resolvent_on_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (z : ℂ) (hz : 1 ≤ |z.im|) {x y : H} (hxy : (x,y) ∈ T.graph) :
    resolvent T hs z hz y = x+z • resolvent T hs z hz x := by
  obtain ⟨v,hv,hTv⟩ := T.mem_graph_iff.mp hxy
  dsimp only [Prod.fst,Prod.snd] at hv hTv
  have he := resolvent_shift T hs z hz v
  rw [hv,hTv,map_sub,map_smul] at he
  exact (sub_eq_iff_eq_add.mp he)

lemma resolvent_commute (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (z w : ℂ) (hz : 1 ≤ |z.im|) (hw : 1 ≤ |w.im|) :
    Commute (resolvent T hs z hz) (resolvent T hs w hw) := by
  apply ContinuousLinearMap.ext
  intro x
  let R := resolvent T hs z hz
  let S := resolvent T hs w hw
  have hg := resolvent_graph T hs z hz (S x)
  have he := resolvent_on_graph T hs z hz (resolvent_graph T hs w hw x)
  have hg' : (R (S x),R x+w • R (S x)) ∈ T.graph := by
    have hoe : S x+z • R (S x) = R x+w • R (S x) := by
      simpa only [map_add,map_smul] using he.symm
    simpa only [R,hoe] using hg
  have hn := resolvent_on_graph T hs w hw hg'
  simp only [map_add,map_smul] at hn
  change R (S x) = S (R x)
  exact (add_right_cancel hn).symm

lemma imaginary_modulus (r : ℝ) : |((r : ℂ)*Complex.I).im| = |r| := by simp

 
def regularizer (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : H →L[ℂ] H :=
  (-(r : ℂ)*Complex.I/2) •
    (resolvent T hs ((r : ℂ)*Complex.I) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr) -
     resolvent T hs (-((r : ℂ)*Complex.I)) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr))

def boundedGenerator (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : H →L[ℂ] H :=
  ((r : ℂ)^2/2) •
    (resolvent T hs ((r : ℂ)*Complex.I) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr) +
     resolvent T hs (-((r : ℂ)*Complex.I)) (by simpa [abs_of_nonneg (by linarith : 0 ≤ r)] using hr))

lemma boundedGenerator_selfAdjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : IsSelfAdjoint (boundedGenerator T hs r hr) := by
  change star (boundedGenerator T hs r hr) = _
  rw [boundedGenerator,star_smul,star_add]
  change star ((r : ℂ)^2/2) •
    ((resolvent T hs ((r : ℂ)*Complex.I) _).adjoint+
     (resolvent T hs (-((r : ℂ)*Complex.I)) _).adjoint) = _
  rw [resolvent_adjoint,resolvent_adjoint]
  simp only [map_div₀,map_pow,Complex.star_def,Complex.conj_ofReal,map_ofNat,
    map_mul,Complex.conj_I,map_neg,mul_neg,neg_neg]
  exact congrArg (fun X : H →L[ℂ] H => ((r : ℂ)^2/2) • X) (add_comm _ _)

lemma regularizer_norm_le (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) : ‖regularizer T hs r hr‖ ≤ 1 := by
  have hr0 : 0 < r := by linarith
  calc
    _ ≤ ‖-(r : ℂ)*Complex.I/2‖ *
        (‖resolvent T hs ((r : ℂ)*Complex.I) _‖ + ‖resolvent T hs (-((r : ℂ)*Complex.I)) _‖) := by
      dsimp only [regularizer]
      rw [norm_smul]
      gcongr
      exact norm_sub_le _ _
    _ ≤ ‖-(r : ℂ)*Complex.I/2‖ * (r⁻¹+r⁻¹) := by
      gcongr
      · simpa [abs_of_pos hr0] using resolvent_norm_le T hs ((r : ℂ)*Complex.I) (by simpa [abs_of_pos hr0] using hr)
      · simpa [abs_of_pos hr0] using resolvent_norm_le T hs (-((r : ℂ)*Complex.I)) (by simpa [abs_of_pos hr0] using hr)
    _ = 1 := by simp [Complex.norm_real,abs_of_pos hr0]; field_simp; norm_num

lemma boundedGenerator_commute (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r s : ℝ) (hr : 1 ≤ r) (hs' : 1 ≤ s) :
    Commute (boundedGenerator T hs r hr) (boundedGenerator T hs s hs') := by
  unfold boundedGenerator
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.add_left
  · apply Commute.add_right <;> exact resolvent_commute T hs _ _ _ _
  · apply Commute.add_right <;> exact resolvent_commute T hs _ _ _ _

lemma regularizer_on_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) {x y : H} (hxy : (x,y) ∈ T.graph) :
    boundedGenerator T hs r hr x = regularizer T hs r hr y := by
  let z : ℂ := (r : ℂ)*Complex.I
  have hz : 1 ≤ |z.im| := by simpa [z,abs_of_nonneg (by linarith : 0 ≤ r)] using hr
  have hz' : 1 ≤ |(-z).im| := by simpa using hz
  change ((r : ℂ)^2/2) • (resolvent T hs z hz x+resolvent T hs (-z) hz' x) =
      (-(r : ℂ)*Complex.I/2) • (resolvent T hs z hz y-resolvent T hs (-z) hz' y)
  rw [resolvent_on_graph T hs z hz hxy,resolvent_on_graph T hs (-z) hz' hxy]
  simp only [add_sub_add_left_eq_sub,smul_sub,smul_add,smul_smul,neg_smul,z]
  have h1 : (-(r : ℂ)*Complex.I/2)*((r : ℂ)*Complex.I) = (r : ℂ)^2/2 := by
    calc _ = -(r : ℂ)^2*Complex.I^2/2 := by ring
         _ = _ := by rw [Complex.I_sq]; ring
  rw [h1]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [Complex.I_sq]; ring)

lemma regularizer_error (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (hr : 1 ≤ r) {x y : H} (hxy : (x,y) ∈ T.graph) :
    ‖regularizer T hs r hr x-x‖ ≤ r⁻¹*‖y‖ := by
  let z : ℂ := (r : ℂ)*Complex.I
  have hr0 : 0 < r := by linarith
  have hz : 1 ≤ |z.im| := by simpa [z,abs_of_pos hr0] using hr
  have hz' : 1 ≤ |(-z).im| := by simpa using hz
  have he : regularizer T hs r hr x-x =
      (-1/2 : ℂ) • (resolvent T hs z hz y+resolvent T hs (-z) hz' y) := by
    rw [resolvent_on_graph T hs z hz hxy,resolvent_on_graph T hs (-z) hz' hxy]
    simp only [regularizer,smul_apply,sub_apply,z]
    module
  rw [he,norm_smul]
  calc
    _ ≤ ‖(-1/2 : ℂ)‖ * (‖resolvent T hs z hz y‖+‖resolvent T hs (-z) hz' y‖) := by
      gcongr; exact norm_add_le _ _
    _ ≤ ‖(-1/2 : ℂ)‖ * ((‖resolvent T hs z hz‖+‖resolvent T hs (-z) hz'‖)*‖y‖) := by
      rw [add_mul]; gcongr <;> exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖(-1/2 : ℂ)‖ * ((r⁻¹+r⁻¹)*‖y‖) := by
      gcongr
      · simpa [z,abs_of_pos hr0] using resolvent_norm_le T hs z hz
      · simpa [z,abs_of_pos hr0] using resolvent_norm_le T hs (-z) hz'
    _ = _ := by norm_num; ring

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
open Filter
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev sampleRadius (n : ℕ) : ℝ := (n : ℝ)+1
lemma sampleRadius_ge (n : ℕ) : 1 ≤ sampleRadius n := by
  dsimp [sampleRadius]
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma regularizer_strong (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (x : H) :
    Tendsto (fun n : ℕ => regularizer T hs (sampleRadius n) (sampleRadius_ge n) x) atTop (𝓝 x) := by
  have he : Equicontinuous (fun n : ℕ => (regularizer T hs (sampleRadius n) (sampleRadius_ge n) : H → H)) :=
    StrongLimit.equicontinuous_of_norm_bound _ (fun n => regularizer_norm_le T hs _ _)
  have hc := he.isClosed_setOfPred_tendsto (l := atTop) (f := id) continuous_id
  apply (closure_minimal (s := (T.domain : Set H)) (t := {x | Tendsto
    (fun n : ℕ => regularizer T hs (sampleRadius n) (sampleRadius_ge n) x) atTop (𝓝 x)}) ?_ hc) (hs.dense_domain x)
  intro x hx
  let v : T.domain := ⟨x,hx⟩
  change Tendsto _ _ _
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (a := fun n : ℕ => (sampleRadius n)⁻¹*‖T v‖)
  · intro n
    exact regularizer_error T hs _ _ (T.mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
  · have ht : Tendsto (fun n : ℕ => sampleRadius n) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa only [zero_mul, Pi.inv_apply] using ht.inv_tendsto_atTop.mul_const ‖T v‖

lemma boundedGenerator_strong (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {x y : H}
    (hxy : (x,y) ∈ T.graph) :
    Tendsto (fun n : ℕ => boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x) atTop (𝓝 y) := by
  simp_rw [regularizer_on_graph T hs _ _ hxy]
  exact regularizer_strong T hs y

end StronglyRationalVOA.SymmetricOperator

open scoped Topology

open scoped Topology
open Filter MeasureTheory
namespace StronglyRationalVOA.StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma intervalIntegral_tendsto {F : ℕ → ℝ → H} {f : ℝ → H} {C : ℝ}
    (hc : ∀ n, Continuous (F n)) (hb : ∀ n t, ‖F n t‖ ≤ C)
    (ht : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (f t))) (a b : ℝ) :
    Tendsto (fun n => ∫ t in a..b, F n t) atTop (𝓝 (∫ t in a..b, f t)) := by
  have h (a b : ℝ) := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioc a b)) (fun _ : ℝ => C)
    (fun n => (hc n).aestronglyMeasurable) (integrable_const C)
    (fun n => Eventually.of_forall (hb n)) (Eventually.of_forall ht)
  exact (h a b).sub (h b a)

end StronglyRationalVOA.StrongLimit

open scoped Topology
open Filter MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_ApproximatingFlowDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory

open scoped Topology
open Filter
namespace StronglyRationalVOA.StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

lemma apply_tendsto {ι : Type*} {l : Filter ι} (F : ι → H →L[ℂ] H) (A : H →L[ℂ] H)
    {C : ℝ} (hF : ∀ n, ‖F n‖ ≤ C)
    (hf : ∀ x, Tendsto (fun n => F n x) l (𝓝 (A x)))
    {v : ι → H} {x : H} (hv : Tendsto v l (𝓝 x)) :
    Tendsto (fun n => F n (v n)) l (𝓝 (A x)) := by
  have hz : Tendsto (fun n => F n (v n-x)) l (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => C*‖v n-x‖)
    · exact fun n => (F n).le_of_opNorm_le (hF n) _
    · simpa only [sub_self,norm_zero,mul_zero] using
        (tendsto_const_nhds.mul (hv.sub_const x).norm)
  have h := hz.add (hf x)
  simpa only [map_sub,sub_add_cancel,zero_add] using h

 

lemma hasDerivAt_apply {F : ℝ → H →L[ℂ] H} {g : ℝ → H} {g' z' : H} {t C : ℝ}
    (hF : ∀ s, ‖F s‖ ≤ C) (hc : ∀ x, ContinuousAt (fun s => F s x) t)
    (hg : HasDerivAt g g' t) (hz : HasDerivAt (fun s => F s (g t)) z' t) :
    HasDerivAt (fun s => F s (g s)) (F t g'+z') t := by
  rw [hasDerivAt_iff_tendsto_slope] at hg hz ⊢
  have ha := apply_tendsto F (F t) hF (fun x => (hc x).tendsto.mono_left nhdsWithin_le_nhds) hg
  have h := ha.add hz
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  simp only [slope, vsub_eq_sub]
  rw [show F s ((s-t)⁻¹ • (g s-g t)) = (s-t)⁻¹ • F s (g s-g t) from
    (F s |>.restrictScalars ℝ).map_smul _ _]
  rw [map_sub]
  module

end StronglyRationalVOA.StrongLimit

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma norm_le_exp_of_derivative_bound {f f' : ℝ → H} {C : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ C*‖f t‖) (t : ℝ) :
    ‖f t‖ ≤ ‖f 0‖*Real.exp (C*|t|) := by
  have hp {f f' : ℝ → H} (hf : ∀ t, HasDerivAt f (f' t) t)
      (hb : ∀ t, ‖f' t‖ ≤ C*‖f t‖) {t : ℝ} (ht : 0 ≤ t) :
      ‖f t‖ ≤ ‖f 0‖*Real.exp (C*t) := by
    have hc : Continuous f := continuous_iff_continuousAt.mpr (fun s => (hf s).continuousAt)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (K := C) (ε := 0) hc.continuousOn
      (fun s _ => (hf s).hasDerivWithinAt) (le_refl ‖f 0‖)
      (fun s _ => by simpa only [add_zero] using hb s) t (show t ∈ Set.Icc 0 t from ⟨ht,le_rfl⟩)
    simpa only [gronwallBound_ε0,sub_zero] using h
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using hp hf hb ht
  · have hn : 0 ≤ -t := by linarith
    have hd (s : ℝ) : HasDerivAt (fun r => f (-r)) (-f' (-s)) s := by
      simpa only [neg_one_smul, Function.comp_def] using (hf (-s)).scomp s (hasDerivAt_neg s)
    have hb' (s : ℝ) : ‖-f' (-s)‖ ≤ C*‖f (-s)‖ := by simpa only [norm_neg] using hb (-s)
    simpa only [neg_neg,neg_zero,abs_of_neg (lt_of_not_ge ht)] using hp hd hb' hn

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
open Filter

open UniformSpace

open scoped Topology
open Filter MeasureTheory

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma selfAdjoint_injective_of_denseRange (S : H →L[ℂ] H)
    (hS : IsSelfAdjoint S) (hSd : DenseRange S) : Function.Injective S := by
  apply S.toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change S x = 0 at hx
  apply ext_inner_left ℂ
  intro y
  have he : ∀ y : H, inner ℂ y x = 0 := by
    intro y
    apply hSd.induction_on (p := fun y => inner ℂ y x = 0)
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro z
      rw [← ContinuousLinearMap.adjoint_inner_right]
      change inner ℂ z (S.adjoint x) = 0
      rw [show S.adjoint = S from hS,hx,inner_zero_right]
  simpa only [inner_zero_right] using he y



end StronglyRationalVOA.SymmetricOperator

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CoefficientDifferentiated
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter

namespace StronglyRationalVOA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem summable_inner_diagonal {u v : ℤ → H}
    (hu : Summable (fun n => ‖u n‖)) (hv : Summable (fun n => ‖v n‖)) (r : ℤ) :
    Summable (fun n => inner ℂ (u n) (v (n+r))) := by
  have hp : Summable (fun p : ℤ × ℤ => ‖u p.1‖*‖v p.2‖) :=
    hu.mul_of_nonneg hv (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hd := hp.comp_injective (show Function.Injective (fun n : ℤ => (n,n+r)) from
    fun _ _ h => congrArg Prod.fst h)
  apply hd.of_norm_bounded
  intro n
  exact norm_inner_le_norm _ _

 

theorem inner_tsum_diagonal {u v : ℤ → H} (hu : Summable u) (hv : Summable v)
    (r : ℤ) (hz : ∀ m n, n ≠ m+r → inner ℂ (u m) (v n) = 0) :
    inner ℂ (∑' m, u m) (∑' n, v n) = ∑' m, inner ℂ (u m) (v (m+r)) := by
  calc
    _ = ∑' m, inner ℂ (u m) (∑' n, v n) :=
      ((innerSL ℂ).flip (∑' n, v n)).map_tsum hu
    _ = _ := by
      apply tsum_congr
      intro m
      calc
        _ = ∑' n, inner ℂ (u m) (v n) := (innerSL ℂ (u m)).map_tsum hv
        _ = _ := tsum_eq_single (m+r) (fun n hn => hz m n hn)

end StronglyRationalVOA

open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RegularizerFactorAdd
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace

open scoped Topology
open UniformSpace

open UniformSpace

open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



omit [CompleteSpace H] in
 

lemma graph_invariant_of_core (M : H →ₗ.[ℂ] H) (hc : M.IsClosable) (Q : H →L[ℂ] H)
    (hcore : ∀ x y, (x,y) ∈ M.graph → (Q x,Q y) ∈ M.closure.graph)
    {x y : H} (hxy : (x,y) ∈ M.closure.graph) : (Q x,Q y) ∈ M.closure.graph := by
  rw [← hc.graph_closure_eq_closure_graph] at hxy
  have hclosed : IsClosed {p : H × H | (Q p.1,Q p.2) ∈ M.closure.graph} :=
    hc.closure_isClosed.preimage ((Q.continuous.comp continuous_fst).prodMk
      (Q.continuous.comp continuous_snd))
  exact (closure_minimal (fun p hp => hcore p.1 p.2 hp) hclosed) hxy
end StronglyRationalVOA.SymmetricOperator

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_PrimaryStressWeak
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff

open UniformSpace

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
 

lemma graph_invariant_of_regularizers (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (R B : ℕ → H →L[ℂ] H)
    (hg : ∀ n x, (R n x,B n x) ∈ T.graph)
    (hlim : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 x))
    (hreg : ∀ n x y, (x,y) ∈ T.graph → B n x = R n y)
    (Q : H →L[ℂ] H)
    (hQR : ∀ n, Q * R n = R n * Q) (hQB : ∀ n, Q * B n = B n * Q)
    {x y : H} (hxy : (x,y) ∈ T.graph) : (Q x,Q y) ∈ T.graph := by
  have hgr (n : ℕ) : (Q (R n x),Q (R n y)) ∈ T.graph := by
    have hr := congrArg (fun S : H →L[ℂ] H => S x) (hQR n)
    have hb := congrArg (fun S : H →L[ℂ] H => S x) (hQB n)
    change Q (R n x) = R n (Q x) at hr
    change Q (B n x) = B n (Q x) at hb
    rw [hreg n x y hxy] at hb
    rw [hr,hb]
    exact hg n (Q x)
  exact hT.mem_of_tendsto
    ((Q.continuous.tendsto x |>.comp (hlim x)).prodMk_nhds
      (Q.continuous.tendsto y |>.comp (hlim y)))
    (Eventually.of_forall hgr)

 

lemma selfAdjoint_of_selfAdjoint_regularizers {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (hT : T.IsClosed) (hs : T.IsFormalAdjoint T)
    (R B : ℕ → H →L[ℂ] H)
    (hR : ∀ n, IsSelfAdjoint (R n)) (hB : ∀ n, IsSelfAdjoint (B n))
    (hg : ∀ n x, (R n x,B n x) ∈ T.graph)
    (hlim : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 x)) : IsSelfAdjoint T := by
  apply selfAdjoint_of_regularizers hd hT hs R B hR hg hlim
  intro x
  have he (n : ℕ) : (B n - (B n).adjoint) x = 0 := by
    rw [show (B n).adjoint = B n from hB n, sub_self,zero_apply]
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))



end StronglyRationalVOA.SymmetricOperator

open Filter MeasureTheory
open scoped Topology

open MeasureTheory
open scoped Topology
namespace StronglyRationalVOA

lemma intervalIntegral_mem_closedSubmodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hm : ∀ t, f t ∈ S) : (∫ t in a..b,f t) ∈ S := by
  let : IsClosed (S : Set E) := hS
  have h := S.mkQL.intervalIntegral_comp_comm hf
  have hz (t : ℝ) : S.mkQL (f t) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr (hm t)
  simp only [hz,intervalIntegral.integral_zero] at h
  exact (Submodule.Quotient.mk_eq_zero S).mp h.symm

end StronglyRationalVOA

open Filter MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_TimeAverageGraph
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma contraction_pow_initial_bound (R : H →L[ℂ] H) (hR : ‖R‖ ≤ 1) (k : ℕ) (x : H) :
    ‖(R^k) x-x‖ ≤ k*‖R x-x‖ := by
  induction k with
  | zero => simp only [pow_zero,one_apply_eq_self,sub_self,norm_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ k ih =>
    have he : (R^(k+1)) x-x = R ((R^k) x-x)+(R x-x) := by
      rw [pow_succ',mul_apply_eq_comp,map_sub]; abel
    rw [he]
    calc
      ‖R ((R^k) x-x)+(R x-x)‖ ≤ ‖R ((R^k) x-x)‖+‖R x-x‖ := norm_add_le _ _
      _ ≤ ‖(R^k) x-x‖+‖R x-x‖ := by
        exact add_le_add (by simpa only [one_mul] using R.le_of_opNorm_le hR ((R^k) x-x)) le_rfl
      _ ≤ (k:ℝ)*‖R x-x‖+‖R x-x‖ := add_le_add ih le_rfl
      _ = (k+1:ℕ)*‖R x-x‖ := by push_cast; ring

end StronglyRationalVOA.SymmetricOperator

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma bounded_regularization (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (P r : Module.End ℂ D) (R : H →L[ℂ] H)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ T.graph)
    (hr : ∀ x : D, (r x:H) = R x)
    {C : ℝ} (hb : ∀ x : D, ‖(P (r x):H)‖ ≤ C*‖(x:H)‖) :
    ∃ B : H →L[ℂ] H, (∀ x : D, B x = (P (r x):H)) ∧
      ∀ x : H, (R x,B x) ∈ T.graph := by
  let M : D →ₗ[ℂ] H := D.subtype.comp (P.comp r)
  let K := M.mkContinuous C hb
  let B := K.extend D.subtypeL
  have hd : DenseRange D.subtypeL := by
    change Dense (Set.range (D.subtypeL : D → H))
    have he : Set.range (D.subtypeL : D → H) = (D : Set H) := by
      ext x; exact ⟨by rintro ⟨y,rfl⟩; exact y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
    rwa [he]
  have he : IsUniformInducing D.subtypeL := D.subtypeₗᵢ.isometry.isUniformInducing
  have hc (x : D) : B x = (P (r x):H) := ContinuousLinearMap.extend_eq K hd he x
  refine ⟨B,hc,?_⟩
  have hclosed : IsClosed {x : H | (R x,B x) ∈ T.graph} := hT.preimage (R.continuous.prodMk B.continuous)
  intro x
  apply (closure_minimal (s := (D : Set H)) (t := {x:H | (R x,B x) ∈ T.graph}) ?_ hclosed) (hD x)
  intro y hy
  have h := hP (r ⟨y,hy⟩)
  rw [hr,← hc] at h
  exact h

lemma bounded_symmetric_of_core (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (B : H →L[ℂ] H)
    (hB : ∀ x y : D, inner ℂ (B x) (y:H) = inner ℂ (x:H) (B y)) :
    IsSelfAdjoint B := by
  have he (x : D) (y : H) : inner ℂ (B x) y = inner ℂ (x:H) (B y) := by
    have hc : IsClosed {y : H | inner ℂ (B x) y = inner ℂ (x:H) (B y)} :=
      isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner B.continuous)
    exact (closure_minimal (fun y hy => hB x ⟨y,hy⟩) hc) (hD y)
  have he' (x y : H) : inner ℂ (B x) y = inner ℂ x (B y) := by
    have hc : IsClosed {x : H | inner ℂ (B x) y = inner ℂ x (B y)} :=
      isClosed_eq (B.continuous.inner continuous_const) (continuous_id.inner continuous_const)
    exact (closure_minimal (fun x hx => he ⟨x,hx⟩ y) hc) (hD x)
  exact ((ContinuousLinearMap.eq_adjoint_iff B B).mpr he').symm

lemma regularization_selfAdjoint (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (P r : Module.End ℂ D) (R B : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hr : ∀ x : D, (r x:H) = R x)
    (hB : ∀ x : D, B x = (P (r x):H))
    (hP : ∀ x y : D, inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H))
    (hPr : P*r = r*P) : IsSelfAdjoint B := by
  apply bounded_symmetric_of_core D hD B
  intro x y
  rw [hB,hB,hP,hr,← ContinuousLinearMap.adjoint_inner_right,show R.adjoint = R from hR]
  have hp := congrArg (fun F : Module.End ℂ D => (F y:H)) hPr
  change (P (r y):H) = (r (P y):H) at hp
  rw [hp,hr]

omit [CompleteSpace H] in
 

lemma regularization_preserves_closure (D : Submodule ℂ H)
    (P Q r : Module.End ℂ D) (B : H →L[ℂ] H)
    (hB : ∀ x : D, B x = (P (r x):H))
    (hPQ : P*Q = Q*P) (hrQ : r*Q = Q*r)
    (M : H →ₗ.[ℂ] H) (hc : M.IsClosable)
    (hM : M.graph = (D.subtype.prod (D.subtype.comp Q)).range)
    {x y : H} (hxy : (x,y) ∈ M.closure.graph) : (B x,B y) ∈ M.closure.graph := by
  apply graph_invariant_of_core M hc B ?_ hxy
  intro u v huv
  rw [hM] at huv
  obtain ⟨z,hz⟩ := huv
  change ((z:H),(Q z:H)) = (u,v) at hz
  cases hz
  rw [hB,hB]
  have he : P (r (Q z)) = Q (P (r z)) := by
    have hrq := congrArg (fun F : Module.End ℂ D => F z) hrQ
    have hpq := congrArg (fun F : Module.End ℂ D => F (r z)) hPQ
    change r (Q z) = Q (r z) at hrq
    change P (Q (r z)) = Q (P (r z)) at hpq
    rw [hrq,hpq]
  rw [he]
  apply LinearPMap.le_graph_of_le (LinearPMap.le_closure M)
  rw [hM]
  exact ⟨P (r z),rfl⟩
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

def onSubmodule (D : Submodule ℂ H) (P : Module.End ℂ D) : H →ₗ.[ℂ] H where
  domain := D
  toFun := D.subtype.comp P

lemma onSubmodule_graph (D : Submodule ℂ H) (P : Module.End ℂ D) :
    (onSubmodule D P).graph = (D.subtype.prod (D.subtype.comp P)).range := by
  ext p
  rw [LinearPMap.mem_graph_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨x,hx,hy⟩
    exact ⟨x,Prod.ext hx hy⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,congrArg Prod.fst hx,congrArg Prod.snd hx⟩

lemma onSubmodule_mem_graph (D : Submodule ℂ H) (P : Module.End ℂ D) (x : D) :
    ((x:H),(P x:H)) ∈ (onSubmodule D P).graph :=
  (LinearPMap.mem_graph_iff _).mpr ⟨x,rfl,rfl⟩

lemma closure_eq_of_intermediate (M N : H →ₗ.[ℂ] H) (hM : M.IsClosable)
    (hMN : M ≤ N) (hNM : N ≤ M.closure) : N.closure = M.closure := by
  have hN := hM.closure_isClosed.isClosable.leIsClosable hNM
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro p hp
    rw [← hN.graph_closure_eq_closure_graph] at hp
    exact (closure_minimal (LinearPMap.le_graph_of_le hNM) hM.closure_isClosed) hp
  · exact hN.closure_mono hMN
end StronglyRationalVOA.SymmetricOperator

open Filter MeasureTheory
open scoped Topology

namespace StronglyRationalVOA.SymmetricOperator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma end_pow_bound (P : Module.End ℂ E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖P x‖ ≤ C*‖x‖) (k : ℕ) (x : E) :
    ‖(P^k) x‖ ≤ C^k*‖x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖(P^(k+1)) x‖ = ‖P ((P^k) x)‖ := by rw [pow_succ']; rfl
      _ ≤ C*‖(P^k) x‖ := hb _
      _ ≤ C*(C^k*‖x‖) := mul_le_mul_of_nonneg_left ih hC
      _ = C^(k+1)*‖x‖ := by rw [pow_succ']; ring

 

lemma commuting_core_power_bound (T r : Module.End ℂ E) (hc : T*r = r*T)
    {b : ℝ} (hb : 0 ≤ b) (hr : ∀ x, ‖r x‖ ≤ ‖x‖)
    (hTr : ∀ x, ‖T (r x)‖ ≤ b*‖x‖) {j k : ℕ} (hjk : j ≤ k) (x : E) :
    ‖(T^j) ((r^k) x)‖ ≤ b^j*‖x‖ := by
  have he : T^j*r^k = (T*r)^j*r^(k-j) := by
    rw [Commute.mul_pow hc, mul_assoc,← pow_add,Nat.add_sub_of_le hjk]
  have hex := congrArg (fun P : Module.End ℂ E => P x) he
  change (T^j) ((r^k) x) = ((T*r)^j) ((r^(k-j)) x) at hex
  rw [hex]
  calc
    ‖((T*r)^j) ((r^(k-j)) x)‖ ≤ b^j*‖(r^(k-j)) x‖ :=
      end_pow_bound (T*r) hb hTr j _
    _ ≤ b^j*‖x‖ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb j)
      simpa only [one_pow,one_mul] using
        end_pow_bound r (by norm_num : (0:ℝ) ≤ 1) (by simpa only [one_mul] using hr) (k-j) x
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 
def restricted (D : Submodule ℂ H) (R : H →L[ℂ] H)
    (hR : ∀ x : D, R x ∈ D) : Module.End ℂ D :=
  (R.toLinearMap.comp D.subtype).codRestrict D hR

@[simp] lemma restricted_coe (D : Submodule ℂ H) (R : H →L[ℂ] H)
    (hR : ∀ x : D, R x ∈ D) (x : D) : (restricted D R hR x:H) = R x := rfl

lemma restricted_pow_coe (D : Submodule ℂ H) (R : H →L[ℂ] H)
    (hR : ∀ x : D, R x ∈ D) (k : ℕ) (x : D) :
    (((restricted D R hR)^k) x:H) = (R^k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',pow_succ']
    change R (((restricted D R hR)^k) x:H) = R ((R^k) x)
    rw [ih]

lemma restricted_commutes_of_graph (D : Submodule ℂ H) (P : Module.End ℂ D)
    (R : H →L[ℂ] H) (hR : ∀ x : D, R x ∈ D) (M : H →ₗ.[ℂ] H)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ M.graph)
    (hRM : ∀ x y, (x,y) ∈ M.graph → (R x,R y) ∈ M.graph) :
    P*restricted D R hR = restricted D R hR*P := by
  ext x
  change (P (restricted D R hR x):H) = R (P x)
  exact M.mem_graph_snd_inj (hP (restricted D R hR x)) (hRM _ _ (hP x)) rfl

end StronglyRationalVOA.SymmetricOperator

open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SymmetricWeakCommute
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
lemma symmetric_weak_commute (D : Submodule ℂ H) (P Q : Module.End ℂ D)
    (hP : ∀ x y : D, inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H))
    (hQ : ∀ x y : D, inner ℂ (Q x:H) (y:H) = inner ℂ (x:H) (Q y:H))
    (hw : ∀ x y : D, inner ℂ (P x:H) (Q y:H) = inner ℂ (Q x:H) (P y:H)) :
    P*Q = Q*P := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (P (Q x):H) (y:H) = inner ℂ (Q (P x):H) (y:H)
  calc
    inner ℂ (P (Q x):H) (y:H) = inner ℂ (Q x:H) (P y:H) := hP (Q x) y
    _ = inner ℂ (P x:H) (Q y:H) := (hw x y).symm
    _ = inner ℂ (Q (P x):H) (y:H) := (hQ (P x) y).symm



end StronglyRationalVOA.SymmetricOperator

open UniformSpace

namespace StronglyRationalVOA.LocalCovariance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 

lemma shifted_power_graph_bound (T : Module.End ℂ E) (c : ℂ) {M : ℝ}
    (hc : ‖c‖ ≤ M) (k : ℕ) (x : E) :
    ‖((T+c • (1 : Module.End ℂ E))^k) x‖ ≤
      (1+M)^k*∑ j ∈ Finset.range (k+1), ‖(T^j) x‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hc
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hshift : (∑ j ∈ Finset.range (k+1), ‖(T^j) (T x)‖) ≤
        ∑ j ∈ Finset.range (k+2), ‖(T^j) x‖ := by
      have he (j : ℕ) : (T^j) (T x) = (T^(j+1)) x := by rw [pow_succ]; rfl
      simp_rw [he]
      rw [Finset.sum_range_succ' (fun j => ‖(T^j) x‖) (k+1)]
      exact le_add_of_nonneg_right (norm_nonneg _)
    have hold : (∑ j ∈ Finset.range (k+1), ‖(T^j) x‖) ≤
        ∑ j ∈ Finset.range (k+2), ‖(T^j) x‖ := by
      rw [Finset.sum_range_succ (fun j => ‖(T^j) x‖) (k+1)]
      exact le_add_of_nonneg_right (norm_nonneg _)
    let S := ∑ j ∈ Finset.range (k+2), ‖(T^j) x‖
    have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have he : ((T+c • (1 : Module.End ℂ E))^(k+1)) x =
        ((T+c • (1 : Module.End ℂ E))^k) (T x) +
          c • ((T+c • (1 : Module.End ℂ E))^k) x := by
      rw [pow_succ]
      change ((T+c • (1 : Module.End ℂ E))^k) (T x+c • x) = _
      rw [map_add,map_smul]
    rw [he]
    calc
      _ ≤ ‖((T+c • (1 : Module.End ℂ E))^k) (T x)‖ +
          ‖c • ((T+c • (1 : Module.End ℂ E))^k) x‖ := norm_add_le _ _
      _ ≤ (1+M)^k*S + M*((1+M)^k*S) := by
        rw [norm_smul]
        apply add_le_add
        · exact (ih (T x)).trans (mul_le_mul_of_nonneg_left hshift (by positivity))
        · exact mul_le_mul hc ((ih x).trans (mul_le_mul_of_nonneg_left hold (by positivity)))
            (norm_nonneg _) hM
      _ = (1+M)^(k+1)*S := by rw [pow_succ]; ring

 

lemma bound_of_unitary_covariance (e : E ≃ₗᵢ[ℂ] E)
    (P P₀ T L : Module.End ℂ E) (k : ℕ) {α β C M : ℝ}
    (hC : 0 ≤ C) (hs : |α-β| ≤ M)
    (hglobal : ∀ x, ‖P₀ x‖ ≤ C*‖(((1 : Module.End ℂ E)+L)^k) x‖)
    (hP : ∀ x, e (P x) = ((α:ℂ)^k) • P₀ (e x))
    (hT : ∀ x, e (T x) = (α:ℂ) • L (e x) + (β:ℂ) • e x) (x : E) :
    ‖P x‖ ≤ C*(1+M)^k*∑ j ∈ Finset.range (k+1), ‖(T^j) x‖ := by
  let K : Module.End ℂ E := T+((α-β:ℝ):ℂ) • 1
  have hK (z : E) : e (K z) = (α:ℂ) • (((1 : Module.End ℂ E)+L) (e z)) := by
    change e (T z+((α-β:ℝ):ℂ) • z) = _
    rw [map_add,map_smul,hT]
    simp only [LinearMap.add_apply,Module.End.one_apply,Complex.ofReal_sub,smul_add,sub_smul]
    module
  have hpow (j : ℕ) (z : E) : e ((K^j) z) = (α:ℂ)^j • ((((1 : Module.End ℂ E)+L)^j) (e z)) := by
    induction j generalizing z with
    | zero => simp
    | succ j ih =>
      rw [pow_succ',Module.End.mul_apply,hK,ih,map_smul]
      simp only [pow_succ',Module.End.mul_apply,mul_smul]
  have hn : ‖P x‖ ≤ C*‖(K^k) x‖ := by
    rw [← e.norm_map (P x),hP,norm_smul,← e.norm_map ((K^k) x),hpow,norm_smul]
    calc
      _ ≤ ‖(α:ℂ)^k‖*(C*‖(((1 : Module.End ℂ E)+L)^k) (e x)‖) :=
        mul_le_mul_of_nonneg_left (hglobal (e x)) (norm_nonneg _)
      _ = _ := by ring
  have hc : ‖((α-β:ℝ):ℂ)‖ ≤ M := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hs
  exact hn.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (shifted_power_graph_bound T ((α-β:ℝ):ℂ) hc k x) hC)
end StronglyRationalVOA.LocalCovariance

open MeasureTheory Set
open scoped ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry

 

structure Field (T : ℝ) where
  toFun : ℝ → ℝ
  periodic : Function.Periodic toFun T
  smooth : ContDiff ℝ ∞ toFun
  positive : ∀ x, 0 < toFun x
instance instCoeFunFieldForallReal {T : ℝ} : CoeFun (Field T) (fun _ => ℝ → ℝ) := ⟨Field.toFun⟩
namespace Field
variable {T : ℝ} (f : Field T)

def totalTime : ℝ := ∫ t in 0..T, (f t)⁻¹

def normalizedCoordinate (x : ℝ) : ℝ := (totalTime f)⁻¹ * ∫ t in 0..T*x, (f t)⁻¹

lemma inverse_continuous : Continuous (fun t => (f t)⁻¹) :=
  f.smooth.continuous.inv₀ (fun t => ne_of_gt (f.positive t))

lemma totalTime_pos (hT : 0 < T) : 0 < totalTime f := by
  apply intervalIntegral.integral_pos hT f.inverse_continuous.continuousOn
    (fun t _ => (inv_pos.mpr (f.positive t)).le)
  exact ⟨0,⟨le_rfl,hT.le⟩,inv_pos.mpr (f.positive 0)⟩

lemma coordinate_hasDerivAt (x : ℝ) :
    HasDerivAt (normalizedCoordinate f)
      ((totalTime f)⁻¹ * ((f (T*x))⁻¹ * T)) x := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    (f.inverse_continuous.intervalIntegrable 0 (T*x))
    f.inverse_continuous.stronglyMeasurable.stronglyMeasurableAtFilter f.inverse_continuous.continuousAt
  convert (hi.comp x ((hasDerivAt_id x).const_mul T)).const_mul (totalTime f)⁻¹ using 1 <;> first | rfl | simp only [mul_one]

lemma coordinate_derivative_pos (hT : 0 < T) (x : ℝ) :
    0 < (totalTime f)⁻¹ * ((f (T*x))⁻¹ * T) := by
  exact mul_pos (inv_pos.mpr (f.totalTime_pos hT)) (mul_pos (inv_pos.mpr (f.positive _)) hT)

lemma coordinate_add_one (hT : 0 < T) (x : ℝ) :
    normalizedCoordinate f (x+1) = normalizedCoordinate f x+1 := by
  have hp : Function.Periodic (fun t => (f t)⁻¹) T := fun _ => congrArg Inv.inv (f.periodic _)
  have he := hp.intervalIntegral_add_eq_add 0 (T*x)
    (fun a b => f.inverse_continuous.intervalIntegrable a b)
  simp only [zero_add] at he
  dsimp only [normalizedCoordinate]
  rw [mul_add,mul_one,he,mul_add,← totalTime,inv_mul_cancel₀ (ne_of_gt (f.totalTime_pos hT))]

lemma coordinate_smooth : ContDiff ℝ ∞ (normalizedCoordinate f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (f.coordinate_hasDerivAt x).differentiableAt,?_⟩
  have he : deriv (normalizedCoordinate f) =
      fun x => (totalTime f)⁻¹*((f (T*x))⁻¹*T) := funext fun x => (f.coordinate_hasDerivAt x).deriv
  rw [he]
  exact contDiff_const.mul (((f.smooth.comp (contDiff_const.mul contDiff_id)).inv (fun x => ne_of_gt (f.positive (T*x)))).mul contDiff_const)

end Field
end StronglyRationalVOA.PositiveCircleGeometry

namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable {T : ℝ} (f : Field T)

def frequency : ℝ := T / f.totalTime
lemma frequency_pos (hT : 0 < T) : 0 < f.frequency := div_pos hT (f.totalTime_pos hT)

lemma frequency_le (hT : 0 < T) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x ∈ Icc 0 T, f x ≤ M) : f.frequency ≤ M := by
  have hI : T/M ≤ f.totalTime := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hT.le
      (continuous_const.intervalIntegrable 0 T) (f.inverse_continuous.intervalIntegrable 0 T)
      (fun x hx => (inv_anti₀ (f.positive x) (hb x hx)))
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,div_eq_mul_inv,one_div,totalTime] using h
  apply (div_le_iff₀ (f.totalTime_pos hT)).mpr
  have h := (div_le_iff₀ hM).mp hI
  simpa only [mul_comm] using h

 

lemma flatten_identity (hT : 0 < T) (x : ℝ) :
    deriv f.normalizedCoordinate x * f (T*x) = f.frequency := by
  rw [(f.coordinate_hasDerivAt x).deriv]
  dsimp only [frequency]
  field_simp [ne_of_gt (f.positive (T*x)),ne_of_gt (f.totalTime_pos hT)]

 

def stressScalar (c : ℝ) : ℝ :=
  c/24*((T⁻¹*∫ x in 0..T,f x)-f.frequency-
    T⁻¹*∫ x in 0..T,(deriv f x)^2/f x)

end StronglyRationalVOA.PositiveCircleGeometry.Field

namespace StronglyRationalVOA.PositiveCircleGeometry
variable {T : ℝ} {g : ℝ → ℝ}

 
def quadraticField (hp : Function.Periodic g T) (hs : ContDiff ℝ ∞ g) {ε : ℝ} (hε : 0 < ε) : Field T where
  toFun := fun x => g x^2+ε
  periodic := fun _ => by dsimp only; rw [hp]
  smooth := (hs.pow 2).add contDiff_const
  positive := fun x => by nlinarith [sq_nonneg (g x)]

lemma quadratic_derivative (hp : Function.Periodic g T) (hs : ContDiff ℝ ∞ g)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (quadraticField hp hs hε) x = 2*g x*deriv g x := by
  have h := (((hs.differentiable (by norm_num)).differentiableAt (x := x)).hasDerivAt.pow 2).add_const ε
  simpa only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,Pi.pow_apply,quadraticField] using h.deriv

lemma quadratic_logDerivative_bound (hp : Function.Periodic g T) (hs : ContDiff ℝ ∞ g)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (deriv (quadraticField hp hs hε) x)^2 / quadraticField hp hs hε x ≤
      4*(deriv g x)^2 := by
  rw [quadratic_derivative]
  apply (div_le_iff₀ ((quadraticField hp hs hε).positive x)).mpr
  change (2*g x*deriv g x)^2 ≤ 4*(deriv g x)^2*(g x^2+ε)
  nlinarith [mul_nonneg hε.le (sq_nonneg (deriv g x))]

end StronglyRationalVOA.PositiveCircleGeometry

open MeasureTheory Set Filter
open scoped Topology Interval

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressEvolution
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval

namespace StronglyRationalVOA.TimeOrdered
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma norm_growth {f f' : ℝ → E} {C : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ C*‖f t‖) (t : ℝ) :
    ‖f t‖ ≤ ‖f 0‖*Real.exp (C*|t|) := by
  have hp {g g' : ℝ → E} (hg : ∀ t, HasDerivAt g (g' t) t)
      (hgb : ∀ t, ‖g' t‖ ≤ C*‖g t‖) {s : ℝ} (hs : 0 ≤ s) :
      ‖g s‖ ≤ ‖g 0‖*Real.exp (C*s) := by
    have hc : Continuous g := continuous_iff_continuousAt.mpr (fun r => (hg r).continuousAt)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (K := C) (ε := 0) hc.continuousOn
      (fun r _ => (hg r).hasDerivWithinAt) (le_refl ‖g 0‖)
      (fun r _ => by simpa only [add_zero] using hgb r) s (show s ∈ Set.Icc 0 s from ⟨hs,le_rfl⟩)
    simpa only [gronwallBound_ε0,sub_zero] using h
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using hp hf hb ht
  · have hn : 0 ≤ -t := by linarith
    have hd (s : ℝ) : HasDerivAt (fun r => f (-r)) (-f' (-s)) s := by
      simpa only [neg_one_smul,Function.comp_def] using (hf (-s)).scomp s (hasDerivAt_neg s)
    have hb' (s : ℝ) : ‖-f' (-s)‖ ≤ C*‖f (-s)‖ := by simpa only [norm_neg] using hb (-s)
    simpa only [neg_neg,neg_zero,abs_of_neg (lt_of_not_ge ht)] using hp hd hb' hn

lemma zero_of_derivative_bound {f f' : ℝ → E} {C : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ C*‖f t‖)
    (h0 : f 0 = 0) (t : ℝ) : f t = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [h0,norm_zero,zero_mul] using norm_growth hf hb t
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

lemma linear_ode_unique {K f g : ℝ → A} {M : ℝ} (hb : ∀ t, ‖K t‖ ≤ M)
    (hf : ∀ t, HasDerivAt f (K t*f t) t) (hg : ∀ t, HasDerivAt g (K t*g t) t)
    (h0 : f 0 = g 0) (t : ℝ) : f t = g t := by
  have hd (s : ℝ) : HasDerivAt (fun r => f r-g r) (K s*(f s-g s)) s := by
    rw [mul_sub]
    exact (hf s).sub (hg s)
  have hm (s : ℝ) : ‖K s*(f s-g s)‖ ≤ M*‖f s-g s‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb s) (norm_nonneg _))
  exact sub_eq_zero.mp (zero_of_derivative_bound hd hm (sub_eq_zero.mpr h0) t)

end StronglyRationalVOA.TimeOrdered

open MeasureTheory Set Filter
open scoped Topology Interval
namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

omit [Nontrivial H] in
lemma unitary_of_strong_and_star_limit (F : ℕ → H →L[ℂ] H)
    (hF : ∀ n, F n ∈ unitary (H →L[ℂ] H)) (L R : H →L[ℂ] H)
    (hl : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (L x)))
    (hr : ∀ x, Tendsto (fun n => star (F n) x) atTop (𝓝 (R x))) :
    L ∈ unitary (H →L[ℂ] H) ∧ star L=R := by
  have hs : star L=R := by
    ext x
    apply ext_inner_right ℂ
    intro y
    have h1 := (hr x).inner (𝕜 := ℂ) (tendsto_const_nhds (x := y))
    have h2 := (tendsto_const_nhds (x := x)).inner (𝕜 := ℂ) (hl y)
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
    apply tendsto_nhds_unique h2
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] using h1
  have hn (n : ℕ) : ‖F n‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [ContinuousLinearMap.norm_map_of_mem_unitary (hF n),one_mul]
  have hsn (n : ℕ) : ‖star (F n)‖ ≤ 1 := by simpa only [norm_star] using hn n
  refine ⟨⟨?_,?_⟩,hs⟩
  · ext x
    have h := StrongLimit.mul_tendsto (fun n => star (F n)) F R L hsn hr hl x
    have he (n : ℕ) : star (F n) (F n x)=x := congrArg (fun A : H →L[ℂ] H => A x) (hF n).1
    simp only [he] at h
    change star L (L x)=x
    rw [hs]
    exact tendsto_nhds_unique h tendsto_const_nhds
  · ext x
    have h := StrongLimit.mul_tendsto F (fun n => star (F n)) L R hn hl hr x
    have he (n : ℕ) : F n (star (F n) x)=x := congrArg (fun A : H →L[ℂ] H => A x) (hF n).2
    simp only [he] at h
    change L (star L x)=x
    rw [hs]
    exact tendsto_nhds_unique h tendsto_const_nhds
end StronglyRationalVOA.TimeOrdered

namespace StronglyRationalVOA.TimeOrdered
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]



omit [Nontrivial H] in
 

lemma regularizer_factor_of_limits (F : ℕ → H →L[ℂ] H) (L : H →L[ℂ] H)
    (hl : ∀ x, Tendsto (fun n => star (F n) x) atTop (𝓝 (star L x)))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n x, ‖S (star (F n) x)‖ ≤ C*‖S x‖) :
    ∃ B : H →L[ℂ] H, L.comp S=S.comp B ∧ ‖B‖ ≤ C := by
  let Q := (S.comp (star L)).toLinearMap
  have hq (x : H) : ‖Q x‖ ≤ C*‖S.toLinearMap x‖ := by
    apply le_of_tendsto ((S.continuous.tendsto _).comp (hl x)).norm
    exact Filter.Eventually.of_forall (fun n => hb n x)
  let B := Q.extendOfNorm S.toLinearMap
  have he : B.comp S = S.comp (star L) := by
    ext x
    exact Q.extendOfNorm_eq hSd ⟨C,hq⟩ x
  have he' := congrArg ContinuousLinearMap.adjoint he
  have heq : S.comp B.adjoint=L.comp S := by
    simpa only [ContinuousLinearMap.adjoint_comp,show S.adjoint=S from hS,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using he'
  refine ⟨B.adjoint,heq.symm,?_⟩
  rw [LinearIsometryEquiv.norm_map]
  exact Q.opNorm_extendOfNorm_le hSd hC hq
end StronglyRationalVOA.TimeOrdered

open Set Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_EnergyCutoffNorm
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cutoff_commutator_bound (P F : H →L[ℂ] H) (hP : ‖P‖ ≤ 1) :
    ‖Complex.I • (P*F.adjoint*P)‖ ≤ ‖F‖ := by
  rw [norm_smul,Complex.norm_I,one_mul]
  calc
    _ ≤ (‖P‖*‖F.adjoint‖)*‖P‖ := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖F.adjoint‖)*1 := by gcongr
    _ = ‖F‖ := by rw [one_mul,mul_one,LinearIsometryEquiv.norm_map]

 

lemma cutoff_error (P S E A B : H →L[ℂ] H) (hP : ‖P‖ ≤ 1)
    (hleft : E=S*A) (hright : E=B*S) (hPS : Commute P S) {δ : ℝ}
    (htail : ‖(1-P)*S‖ ≤ δ) :
    ‖P*E*P-E‖ ≤ δ*(‖A‖+‖B‖) := by
  have hd : 0 ≤ δ := (norm_nonneg _).trans htail
  have hid : P*E*P-E = -(1-P)*E*P-E*(1-P) := by noncomm_ring
  have hrighttail : ‖S*(1-P)‖ ≤ δ := by
    have he : S*(1-P)=(1-P)*S := by rw [mul_sub,sub_mul,mul_one,one_mul,hPS.eq]
    rwa [he]
  rw [hid]
  calc
    _ ≤ ‖-(1-P)*E*P‖+‖E*(1-P)‖ := norm_sub_le _ _
    _ = ‖((1-P)*S)*A*P‖+‖B*(S*(1-P))‖ := by
      rw [neg_mul,neg_mul,norm_neg]
      congr 1
      · rw [hleft]; simp only [mul_assoc]
      · rw [hright]; simp only [mul_assoc]
    _ ≤ (‖(1-P)*S‖*‖A‖)*‖P‖+‖B‖*‖S*(1-P)‖ := add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
      (norm_mul_le _ _)
    _ ≤ (δ*‖A‖)*1+‖B‖*δ := by gcongr
    _ = _ := by ring
end StronglyRationalVOA.SymmetricOperator

open UniformSpace Set

open UniformSpace

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressCutoffNormalized2
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

lemma form_pairing_derivative (D : Submodule ℂ H) (P : ℝ → D →ₗ[ℂ] H)
    (x y : ℝ → D) (t : ℝ) (dx dy z : H)
    (hs : ∀ a b : D, inner ℂ (P t a) (b : H)=inner ℂ (a : H) (P t b))
    (hx : HasDerivAt (fun s => (x s : H)) dx t)
    (hy : HasDerivAt (fun s => (y s : H)) dy t)
    (hPy : ContinuousAt (fun s => P s (y s)) t)
    (hP : Tendsto (fun s => (s-t)⁻¹ • (P s (y s)-P t (y s))) (𝓝[≠] t) (𝓝 z)) :
    HasDerivAt (fun s => inner ℂ (x s : H) (P s (y s)))
      (inner ℂ dx (P t (y t))+inner ℂ (P t (x t)) dy+inner ℂ (x t : H) z) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h := ((hx.tendsto_slope.inner (𝕜 := ℂ) (hPy.mono_left nhdsWithin_le_nhds)).add
    ((tendsto_const_nhds (x := P t (x t))).inner (𝕜 := ℂ) hy.tendsto_slope)).add ((tendsto_const_nhds (x := (x t : H))).inner (𝕜 := ℂ) hP)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext s
  simp only [slope,vsub_eq_sub,inner_sub_left,inner_sub_right,inner_smul_left_eq_star_smul,
    inner_smul_right_eq_smul,starRingEnd_apply,star_trivial,hs,smul_sub]
  abel
end StronglyRationalVOA.SymmetricOperator

open UniformSpace Filter
open scoped Topology

open UniformSpace Filter
open scoped Topology

open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressPropagatorDerivative
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology

open Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry
 

lemma parameter_inverse_smooth (F : ℝ → ℝ ≃o ℝ)
    (hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2))
    (hn : ∀ t y, deriv (F t) y ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => (F p.1).symm p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let y : ℝ := (F p.1).symm p.2
  let K : (ℝ × ℝ) × ℝ → ℝ := fun q => F q.1.1 q.2-q.1.2
  have hK : ContDiff ℝ ∞ K :=
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd
  let L := fderiv ℝ K (p,y)
  have hpart : HasDerivAt (fun z => F p.1 z-p.2)
      ((L.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)) 1) y := by
    have hd := (hK.differentiable (by simp) (p,y)).hasFDerivAt
    have hcomp := hd.comp y ((hasFDerivAt_const (p : ℝ × ℝ) y).prodMk (hasFDerivAt_id y))
    simpa only [K,L,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,map_one,
      zero_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.inr_apply,Function.comp_def] using hcomp.hasDerivAt
  have hsingle : DifferentiableAt ℝ (fun z => F p.1 z) y :=
    ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)).differentiableAt
  have he : (L.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)) 1=deriv (F p.1) y := by
    have hd := hsingle.hasDerivAt.sub_const p.2
    exact hpart.unique hd
  have hinv : (L.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)).IsInvertible := by
    refine ⟨(ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (deriv (F p.1) y) (hn p.1 y))),?_⟩
    apply ContinuousLinearMap.ext
    intro z
    change z*deriv (F p.1) y = _
    rw [show z=z • (1:ℝ) by simp, map_smul,smul_eq_mul,he]
    simp only [smul_eq_mul,mul_one]
  have hloc := hK.contDiffAt.contDiffAt_implicitFunction (by simp) hinv
  apply hloc.congr_of_eventuallyEq
  filter_upwards [hK.contDiffAt.eventually_apply_implicitFunction (by simp) hinv] with q hq
  apply (F q.1).injective
  rw [(F q.1).apply_symm_apply]
  dsimp only [K] at hq
  have hp : F p.1 y=p.2 := (F p.1).apply_symm_apply p.2
  rw [hp,sub_self] at hq
  exact (sub_eq_zero.mp hq).symm
end StronglyRationalVOA.PositiveCircleGeometry

open Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry
 
structure SmoothLift where
  toFun : ℝ → ℝ
  add_one : ∀ x, toFun (x+1)=toFun x+1
  smooth : ContDiff ℝ ∞ toFun
  derivative_pos : ∀ x, 0 < deriv toFun x
instance instCoeFunSmoothLiftForallReal : CoeFun SmoothLift (fun _ => ℝ → ℝ) := ⟨SmoothLift.toFun⟩
namespace SmoothLift
variable (φ : SmoothLift)
lemma strictMono : StrictMono φ := strictMono_of_deriv_pos φ.derivative_pos

def degreeOne : CircleDeg1Lift where
  toFun := φ
  monotone' := φ.strictMono.monotone
  map_add_one' := φ.add_one
lemma surjective : Function.Surjective φ := φ.degreeOne.continuous_iff_surjective.mp φ.smooth.continuous

def orderIso : ℝ ≃o ℝ := StrictMono.orderIsoOfRightInverse φ φ.strictMono
  (Function.surjInv φ.surjective) (Function.rightInverse_surjInv φ.surjective)
@[simp] lemma orderIso_apply (x : ℝ) : φ.orderIso x=φ x := rfl

 

def interpolate (t x : ℝ) : ℝ := (1-Real.smoothTransition t)*x+Real.smoothTransition t*φ x
lemma interpolate_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.interpolate p.1 p.2) := by
  exact ((contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).mul contDiff_snd).add
    ((Real.smoothTransition.contDiff.comp contDiff_fst).mul (φ.smooth.comp contDiff_snd))
lemma interpolate_zero (x : ℝ) : φ.interpolate 0 x=x := by simp [interpolate]
lemma interpolate_one (x : ℝ) : φ.interpolate 1 x=φ x := by simp [interpolate]
lemma interpolate_add_one (t x : ℝ) : φ.interpolate t (x+1)=φ.interpolate t x+1 := by
  simp only [interpolate,φ.add_one]; ring
lemma interpolate_derivative (t x : ℝ) :
    HasDerivAt (φ.interpolate t) (1-Real.smoothTransition t+Real.smoothTransition t*deriv φ x) x := by
  unfold interpolate
  convert ((hasDerivAt_id x).const_mul (1-Real.smoothTransition t)).add
    (((φ.smooth.differentiable (by simp) x).hasDerivAt).const_mul (Real.smoothTransition t)) using 1 <;> first | rfl | simp only [mul_one]
lemma interpolate_derivative_pos (t x : ℝ) :
    0 < 1-Real.smoothTransition t+Real.smoothTransition t*deriv φ x := by
  have h0 := Real.smoothTransition.nonneg t
  have h1 := Real.smoothTransition.le_one t
  by_cases h : Real.smoothTransition t=0
  · simp [h]
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr h1)
      (mul_pos (lt_of_le_of_ne h0 (Ne.symm h)) (φ.derivative_pos x))
def isotopy (t : ℝ) : SmoothLift where
  toFun := φ.interpolate t
  add_one := φ.interpolate_add_one t
  smooth := φ.interpolate_smooth.comp (contDiff_const.prodMk contDiff_id)
  derivative_pos := fun x => by rw [(φ.interpolate_derivative t x).deriv]; exact φ.interpolate_derivative_pos t x
@[simp] lemma isotopy_apply (t x : ℝ) : φ.isotopy t x=φ.interpolate t x := rfl
end SmoothLift
end StronglyRationalVOA.PositiveCircleGeometry

open Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
def inverse (t x : ℝ) : ℝ := (φ.isotopy t).orderIso.symm x
lemma inverse_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.inverse p.1 p.2) := by
  apply parameter_inverse_smooth (fun t => (φ.isotopy t).orderIso)
  · exact φ.interpolate_smooth
  · intro t x
    exact ne_of_gt ((φ.isotopy t).derivative_pos x)
@[simp] lemma interpolate_inverse (t x : ℝ) : φ.interpolate t (φ.inverse t x)=x :=
  (φ.isotopy t).orderIso.apply_symm_apply x
@[simp] lemma inverse_interpolate (t x : ℝ) : φ.inverse t (φ.interpolate t x)=x :=
  (φ.isotopy t).orderIso.symm_apply_apply x
lemma inverse_add_one (t x : ℝ) : φ.inverse t (x+1)=φ.inverse t x+1 := by
  apply (φ.isotopy t).strictMono.injective
  change φ.interpolate t (φ.inverse t (x+1))=φ.interpolate t (φ.inverse t x+1)
  rw [φ.interpolate_inverse,φ.interpolate_add_one,φ.interpolate_inverse]
def jacobian (t y : ℝ) : ℝ := 1-Real.smoothTransition t+Real.smoothTransition t*deriv φ y
lemma jacobian_pos (t y : ℝ) : 0 < φ.jacobian t y := φ.interpolate_derivative_pos t y
lemma jacobian_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.jacobian p.1 p.2) := by
  exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp contDiff_fst)).add
    ((Real.smoothTransition.contDiff.comp contDiff_fst).mul ((contDiff_infty_iff_deriv.mp φ.smooth).2.comp contDiff_snd))
def velocity (t x : ℝ) : ℝ := deriv Real.smoothTransition t*(φ (φ.inverse t x)-φ.inverse t x)
lemma velocity_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.velocity p.1 p.2) := by
  exact ((contDiff_infty_iff_deriv.mp (Real.smoothTransition.contDiff (n := ⊤))).2.comp contDiff_fst).mul
    ((φ.smooth.comp φ.inverse_smooth).sub φ.inverse_smooth)
lemma inverse_space_derivative (t x : ℝ) :
    HasDerivAt (φ.inverse t) (φ.jacobian t (φ.inverse t x))⁻¹ x := by
  apply HasDerivAt.of_local_left_inverse
    (((φ.inverse_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous).continuousAt)
    (φ.interpolate_derivative t (φ.inverse t x))
    (ne_of_gt (φ.jacobian_pos t (φ.inverse t x)))
  exact Filter.Eventually.of_forall (φ.interpolate_inverse t)
lemma inverse_time_derivative (t x : ℝ) :
    HasDerivAt (fun s => φ.inverse s x) (-φ.velocity t x/(φ.jacobian t (φ.inverse t x))) t := by
  have hd := ((φ.inverse_smooth.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt
  have hr := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt
  have hp := (φ.smooth.differentiable (by simp) (φ.inverse t x)).hasDerivAt.comp t hd
  have he := ((hasDerivAt_const t (1:ℝ)).sub hr).mul hd |>.add (hr.mul hp)
  have he0 := he.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => (φ.interpolate_inverse s x).symm))
  have hz := he0.unique (hasDerivAt_const t x)
  have hval : deriv (fun s => φ.inverse s x) t= -φ.velocity t x/φ.jacobian t (φ.inverse t x) := by
    apply (eq_div_iff (ne_of_gt (φ.jacobian_pos t (φ.inverse t x)))).mpr
    dsimp only [velocity,jacobian]
    simp only [Function.comp_def,id_eq,Pi.sub_apply] at hz
    linear_combination hz
  exact hval ▸ hd
lemma velocity_space_derivative (t x : ℝ) :
    HasDerivAt (φ.velocity t)
      (deriv Real.smoothTransition t*(deriv φ (φ.inverse t x)-1)/(φ.jacobian t (φ.inverse t x))) x := by
  have he := (((φ.smooth.differentiable (by simp) (φ.inverse t x)).hasDerivAt.comp x
    (φ.inverse_space_derivative t x)).sub (φ.inverse_space_derivative t x)).const_mul (deriv Real.smoothTransition t)
  unfold velocity
  convert he using 1 <;> first | rfl | ring
lemma jacobian_space_derivative (t y : ℝ) : HasDerivAt (φ.jacobian t)
    (Real.smoothTransition t*deriv (deriv φ) y) y := by
  have he := ((contDiff_infty_iff_deriv.mp φ.smooth).2.differentiable (by simp) y).hasDerivAt.const_mul (Real.smoothTransition t)
  convert he.const_add (1-Real.smoothTransition t) using 1
  all_goals try with_reducible_and_instances rfl
  rfl


def density (g : ℝ → ℝ) (k : ℕ) (t x : ℝ) : ℝ :=
  φ.jacobian t (φ.inverse t x)^k*g (φ.inverse t x)
lemma density_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ.density g k p.1 p.2) := by
  exact ((φ.jacobian_smooth.comp (contDiff_fst.prodMk φ.inverse_smooth)).pow k).mul
    (hg.comp φ.inverse_smooth)
lemma density_space_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) (t x : ℝ) :
    HasDerivAt (φ.density g k t)
    ((k:ℝ)*φ.jacobian t (φ.inverse t x)^(k-1)*
      (Real.smoothTransition t*deriv (deriv φ) (φ.inverse t x)/(φ.jacobian t (φ.inverse t x)))*g (φ.inverse t x)+
      φ.jacobian t (φ.inverse t x)^k*(deriv g (φ.inverse t x)/(φ.jacobian t (φ.inverse t x)))) x := by
  have hi := φ.inverse_space_derivative t x
  have hj := (φ.jacobian_space_derivative t (φ.inverse t x)).comp x hi
  have hd := (hj.pow k).mul ((hg.differentiable (by simp) (φ.inverse t x)).hasDerivAt.comp x hi)
  unfold density
  convert hd using 1 <;> rfl
lemma density_time_derivative {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) (t x : ℝ) :
    HasDerivAt (fun s => φ.density g k s x)
      ((k:ℝ)*deriv (φ.velocity t) x*φ.density g k t x-φ.velocity t x*deriv (φ.density g k t) x) t := by
  have hi := φ.inverse_time_derivative t x
  have hr := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) t).hasDerivAt
  have hp := (((contDiff_infty_iff_deriv.mp φ.smooth).2.differentiable (by simp)
    (φ.inverse t x)).hasDerivAt).comp t hi
  have hj := ((hasDerivAt_const t (1:ℝ)).sub hr).add (hr.mul hp)
  have hd := (hj.pow k).mul ((hg.differentiable (by simp) (φ.inverse t x)).hasDerivAt.comp t hi)
  rw [(φ.velocity_space_derivative t x).deriv,(φ.density_space_derivative hg k t x).deriv]
  unfold density jacobian
  convert hd using 1 <;> first | rfl | skip
  have hn := ne_of_gt (φ.jacobian_pos t (φ.inverse t x))
  dsimp only [jacobian] at hn
  simp only [jacobian,Function.comp_def,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
  generalize hJ : 1-Real.smoothTransition t+Real.smoothTransition t*deriv φ (φ.inverse t x)=J at *
  cases k with
  | zero => simp; ring
  | succ k =>
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,pow_succ]
    field_simp [hn]
    ring
lemma derivative_periodic : Function.Periodic (deriv φ) 1 := by
  intro x
  have h : (fun y => φ (y+1))=(fun y => φ y+1) := funext φ.add_one
  have he := congrFun (congrArg deriv h) x
  simpa only [deriv_comp_add_const,deriv_add_const] using he
lemma velocity_periodic (t : ℝ) : Function.Periodic (φ.velocity t) 1 := by
  intro x
  simp only [velocity,φ.inverse_add_one,φ.add_one]
  ring
lemma density_periodic {g : ℝ → ℝ} (hg : Function.Periodic g 1) (k : ℕ) (t : ℝ) :
    Function.Periodic (φ.density g k t) 1 := by
  intro x
  simp only [density,φ.inverse_add_one,jacobian,φ.derivative_periodic (φ.inverse t x),hg (φ.inverse t x)]
lemma inverse_zero (x : ℝ) : φ.inverse 0 x=x := by
  have h := φ.interpolate_inverse 0 x
  rwa [φ.interpolate_zero] at h
lemma density_zero (g : ℝ → ℝ) (k : ℕ) (x : ℝ) : φ.density g k 0 x=g x := by
  simp [density,jacobian,φ.inverse_zero]
lemma velocity_stationary {t : ℝ} (ht : t ∉ Set.Icc 0 1) : φ.velocity t=0 := by
  have he : deriv Real.smoothTransition t=0 := by
    rcases lt_or_ge t 0 with h | h
    · have hh : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
        filter_upwards [Iio_mem_nhds h] with s hs
        exact Real.smoothTransition.zero_of_nonpos hs.le
      rw [hh.deriv_eq,deriv_const]
    · have h1 : 1 < t := lt_of_not_ge (fun h1 => ht ⟨h,h1⟩)
      have hh : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
        filter_upwards [Ioi_mem_nhds h1] with s hs
        exact Real.smoothTransition.one_of_one_le hs.le
      rw [hh.deriv_eq,deriv_const]
  funext x
  simp only [velocity,he,zero_mul,Pi.zero_apply]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA
lemma joint_space_deriv_smooth {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun x => f (p.1,x)) p.2) := by
  have he (p : ℝ × ℝ) : deriv (fun x => f (p.1,x)) p.2 = fderiv ℝ f p (0,1) := by
    have hg : HasFDerivAt (fun x : ℝ => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 := by
      convert (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2) using 1 <;> rfl
    have h := (hf.differentiable (by simp) p).hasFDerivAt.comp p.2 hg
    convert h.hasDerivAt.deriv using 1 <;> rfl
  simp_rw [he]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
lemma joint_iterated_space_deriv_smooth {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => iteratedDeriv k (fun x => f (p.1,x)) p.2) := by
  induction k with
  | zero => exact hf
  | succ k ih => simpa only [iteratedDeriv_succ] using joint_space_deriv_smooth ih

lemma summable_circle_decay : Summable (fun n : ℤ => ((1+|(n:ℝ)|)^2)⁻¹) := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  have h : Summable (fun n : ℕ => ((1+(n:ℝ))^2)⁻¹) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_comm] using
      (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2))
  constructor
  · simpa only [Int.cast_natCast,Nat.abs_cast] using h
  · simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,Nat.abs_cast] using h

end StronglyRationalVOA

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_CoefficientSummableBound
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set

open Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
lemma angular_shift (x : ℝ) : (x+2*Real.pi)/(2*Real.pi)=x/(2*Real.pi)+1 := by
  field_simp [Real.pi_ne_zero]

end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open UniformSpace Filter
open scoped Topology ContDiff

open Filter MeasureTheory Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_StressSmoothness
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
namespace StronglyRationalVOA.RealCircleCalculus

lemma space_deriv_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : Differentiable ℝ f) (p : ℝ × ℝ) :
    deriv (fun x => f (p.1,x)) p.2=fderiv ℝ f p (0,1) := by
  have hg : HasFDerivAt (fun x : ℝ => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ ℝ) p.2 := by
    convert (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2) using 1 <;> rfl
  exact ((hf p).hasFDerivAt.comp p.2 hg).hasDerivAt.deriv
lemma time_deriv_eq_fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : Differentiable ℝ f) (p : ℝ × ℝ) :
    deriv (fun t => f (t,p.2)) p.1=fderiv ℝ f p (1,0) := by
  have hg : HasFDerivAt (fun t : ℝ => (t,p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 := by
    convert (hasFDerivAt_id (𝕜 := ℝ) p.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) p.2 p.1) using 1 <;> rfl
  exact ((hf p).hasFDerivAt.comp p.1 hg).hasDerivAt.deriv
lemma space_deriv_smooth {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun x => f (p.1,x)) p.2) := by
  simp_rw [space_deriv_eq_fderiv (hf.differentiable (by simp))]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
lemma time_deriv_smooth {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (fun t => f (t,p.2)) p.1) := by
  simp_rw [time_deriv_eq_fderiv (hf.differentiable (by simp))]
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
lemma mixed_deriv {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (t x : ℝ) :
    deriv (fun s => deriv (fun y => f (s,y)) x) t =
      deriv (fun y => deriv (fun s => f (s,y)) t) x := by
  have hd := hf.differentiable (by simp)
  have hh : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hdd := hh.differentiable (by simp)
  have hx (s : ℝ) := space_deriv_eq_fderiv hd (s,x)
  have ht (y : ℝ) := time_deriv_eq_fderiv hd (t,y)
  simp only at hx ht
  simp_rw [hx,ht]
  rw [time_deriv_eq_fderiv (hdd.clm_apply (differentiable_const (0,1))) (t,x),
    space_deriv_eq_fderiv (hdd.clm_apply (differentiable_const (1,0))) (t,x)]
  have he (v w : ℝ × ℝ) :
      fderiv ℝ (fun p => fderiv ℝ f p v) (t,x) w=fderiv ℝ (fderiv ℝ f) (t,x) w v := by
    have h := (hdd (t,x)).hasFDerivAt.clm_apply (hasFDerivAt_const v (t,x))
    rw [h.fderiv]
    simp
  rw [he,he]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast) _ _

 

lemma integral_derivative {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (a b t : ℝ) :
    HasDerivAt (fun s => ∫ x in a..b, f (s,x))
      (∫ x in a..b, deriv (fun s => f (s,x)) t) t := by
  let G (s x : ℝ) := deriv (fun q => f (q,x)) s
  have hF (s : ℝ) : Continuous (fun x => f (s,x)) := hf.continuous.comp (continuous_const.prodMk continuous_id)
  have hG : Continuous (Function.uncurry G) := (time_deriv_smooth hf).continuous
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    hG.continuousOn (s := Icc (t-1) (t+1) ×ˢ uIcc a b)
  have hd := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => f (s,x)) (F' := G) (μ := volume) (a := a) (b := b)
    (s := Icc (t-1) (t+1)) (bound := fun _ => M)
    (Icc_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s => (hF s).aestronglyMeasurable))
    ((hF t).intervalIntegrable _ _)
    ((hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x hx s hs => hM (s,x) ⟨hs,uIoc_subset_uIcc hx⟩))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun x _ s _ => by
      exact ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) s).hasDerivAt))
  exact hd.2
lemma periodic_deriv {g : ℝ → ℝ} {T : ℝ} (hp : Function.Periodic g T) :
    Function.Periodic (deriv g) T := by
  intro x
  have he : (fun y => g (y+T))=g := funext hp
  have h := congrFun (congrArg deriv he) x
  simpa only [deriv_comp_add_const] using h

def anomalyDensity (g : ℝ → ℝ) (x : ℝ) : ℝ := g x-(deriv g x)^2/g x

def anomalyFlux (g v : ℝ → ℝ) (x : ℝ) : ℝ :=
  v x*(deriv g x)^2/g x-v x*g x-2*g x*deriv (deriv v) x

def anomalyEnergy (T : ℝ) (g : ℝ → ℝ) : ℝ := ∫ x in 0..T, anomalyDensity g x

lemma anomaly_density_smooth {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : ∀ t x, g (t,x) ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => anomalyDensity (fun x => g (p.1,x)) p.2) :=
  hg.sub (((space_deriv_smooth hg).pow 2).div hg (fun p => hp p.1 p.2))

 

lemma anomaly_density_derivative {g v : ℝ × ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hv : ContDiff ℝ ∞ v) (hpos : ∀ t x, g (t,x) ≠ 0)
    (hpde : ∀ t x, deriv (fun s => g (s,x)) t =
      deriv (fun y => v (t,y)) x*g (t,x)-v (t,x)*deriv (fun y => g (t,y)) x)
    (t x : ℝ) :
    HasDerivAt (fun s => anomalyDensity (fun y => g (s,y)) x)
      (2*(deriv (deriv (deriv (fun y => v (t,y)))) x+deriv (fun y => v (t,y)) x)*g (t,x)+
        deriv (anomalyFlux (fun y => g (t,y)) (fun y => v (t,y))) x) t := by
  let G : ℝ → ℝ := fun y => g (t,y)
  let W : ℝ → ℝ := fun y => v (t,y)
  have hG : ContDiff ℝ ∞ G := hg.comp (contDiff_const.prodMk contDiff_id)
  have hW : ContDiff ℝ ∞ W := hv.comp (contDiff_const.prodMk contDiff_id)
  have hG' := (contDiff_infty_iff_deriv.mp hG).2
  have hW' := (contDiff_infty_iff_deriv.mp hW).2
  have hW'' := (contDiff_infty_iff_deriv.mp hW').2
  have hdx := (hG.differentiable (by simp) x).hasDerivAt
  have hdx' := (hG'.differentiable (by simp) x).hasDerivAt
  have hdv := (hW.differentiable (by simp) x).hasDerivAt
  have hdv' := (hW'.differentiable (by simp) x).hasDerivAt
  have hdv'' := (hW''.differentiable (by simp) x).hasDerivAt
  have hd := ((hg.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt
  change HasDerivAt (fun s => g (s,x)) (deriv (fun s => g (s,x)) t) t at hd
  rw [hpde] at hd
  have hsd := (((space_deriv_smooth hg).comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt
  have he : (fun y => deriv (fun s => g (s,y)) t)=(fun y => deriv W y*G y-W y*deriv G y) :=
    funext (hpde t)
  have hm := mixed_deriv hg t x
  rw [he] at hm
  change _=deriv (deriv W*G-W*deriv G) x at hm
  rw [((hdv'.mul hdx).sub (hdv.mul hdx')).deriv] at hm
  change deriv (fun s => deriv (fun y => g (s,y)) x) t=_ at hm
  change HasDerivAt (fun s => deriv (fun y => g (s,y)) x)
    (deriv (fun s => deriv (fun y => g (s,y)) x) t) t at hsd
  rw [hm] at hsd
  have hdE := hd.sub ((hsd.pow 2).div hd (hpos t x))
  have hB := (((hdv.mul (hdx'.pow 2)).div hdx (hpos t x)).sub (hdv.mul hdx)).sub
    ((hdx.mul hdv'').const_mul 2)
  have heB : (fun y => W y*(deriv G y)^2/G y-W y*G y-2*(G y*deriv (deriv W) y))=
      anomalyFlux G W := by ext y; dsimp [anomalyFlux]; ring
  change HasDerivAt (fun y => W y*(deriv G y)^2/G y-W y*G y-2*(G y*deriv (deriv W) y)) _ x at hB
  rw [heB] at hB
  change HasDerivAt (fun s => anomalyDensity (fun y => g (s,y)) x)
    (2*(deriv (deriv (deriv W)) x+deriv W x)*G x+deriv (anomalyFlux G W) x) t
  rw [hB.deriv]
  convert hdE using 1 <;> try rfl
  simp only [G,W,Pi.pow_apply,Pi.mul_apply,Nat.cast_ofNat,show 2-1=1 from rfl,pow_one]
  field_simp [hpos t x]
  ring
lemma anomaly_flux_smooth {g v : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hv : ContDiff ℝ ∞ v)
    (hp : ∀ x, g x ≠ 0) : ContDiff ℝ ∞ (anomalyFlux g v) := by
  have hg' := (contDiff_infty_iff_deriv.mp hg).2
  have hv'' := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hv).2).2
  exact (((hv.mul (hg'.pow 2)).div hg hp).sub (hv.mul hg)).sub
    ((contDiff_const.mul hg).mul hv'')
lemma anomaly_flux_periodic {g v : ℝ → ℝ} {T : ℝ}
    (hg : Function.Periodic g T) (hv : Function.Periodic v T) :
    Function.Periodic (anomalyFlux g v) T := by
  intro x
  dsimp only [anomalyFlux]
  rw [hg,hv,periodic_deriv hg x,periodic_deriv (periodic_deriv hv) x]

lemma anomaly_energy_derivative {g v : ℝ × ℝ → ℝ} {T : ℝ}
    (hg : ContDiff ℝ ∞ g) (hv : ContDiff ℝ ∞ v) (hpos : ∀ t x, g (t,x) ≠ 0)
    (hgp : ∀ t, Function.Periodic (fun x => g (t,x)) T)
    (hvp : ∀ t, Function.Periodic (fun x => v (t,x)) T)
    (hpde : ∀ t x, deriv (fun s => g (s,x)) t =
      deriv (fun y => v (t,y)) x*g (t,x)-v (t,x)*deriv (fun y => g (t,y)) x)
    (t : ℝ) :
    HasDerivAt (fun s => anomalyEnergy T (fun y => g (s,y)))
      (2*∫ x in 0..T, (deriv (deriv (deriv (fun y => v (t,y)))) x+deriv (fun y => v (t,y)) x)*g (t,x)) t := by
  let G : ℝ → ℝ := fun y => g (t,y)
  let W : ℝ → ℝ := fun y => v (t,y)
  have hG : ContDiff ℝ ∞ G := hg.comp (contDiff_const.prodMk contDiff_id)
  have hW : ContDiff ℝ ∞ W := hv.comp (contDiff_const.prodMk contDiff_id)
  have hB := anomaly_flux_smooth hG hW (hpos t)
  have hBp := anomaly_flux_periodic (hgp t) (hvp t)
  have hB' := (contDiff_infty_iff_deriv.mp hB).2
  have hBI : (∫ x in 0..T, deriv (anomalyFlux G W) x)=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => (hB.differentiable (by simp) x).hasDerivAt)
      (hB'.continuous.intervalIntegrable 0 T)]
    have he := hBp 0
    simpa only [zero_add,sub_eq_zero] using he
  have hW' := (contDiff_infty_iff_deriv.mp hW).2
  have hW''' := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hW').2).2
  have hC : Continuous (fun x => (deriv (deriv (deriv W)) x+deriv W x)*G x) :=
    (hW'''.continuous.add hW'.continuous).mul hG.continuous
  have hd := integral_derivative (anomaly_density_smooth hg hpos) 0 T t
  have he : (∫ x in 0..T, deriv (fun s => anomalyDensity (fun y => g (s,y)) x) t)=
      2*∫ x in 0..T, (deriv (deriv (deriv W)) x+deriv W x)*G x := by
    rw [intervalIntegral.integral_congr (fun x _ => (anomaly_density_derivative hg hv hpos hpde t x).deriv)]
    simp_rw [mul_assoc]
    change (∫ x in 0..T, 2*((deriv (deriv (deriv W)) x+deriv W x)*G x)+
      deriv (anomalyFlux G W) x)=_
    rw [intervalIntegral.integral_add ((hC.const_mul 2).intervalIntegrable 0 T)
      (hB'.continuous.intervalIntegrable 0 T),hBI,add_zero,intervalIntegral.integral_const_mul]
  exact he ▸ hd
end StronglyRationalVOA.RealCircleCalculus

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.RealCircleCalculus
lemma deriv_ofReal {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    deriv (fun x => (g x:ℂ))=fun x => ((deriv g x:ℝ):ℂ) :=
  funext fun x => (hg x).hasDerivAt.ofReal_comp.deriv
lemma iteratedDeriv_ofReal {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    iteratedDeriv k (fun x => (g x:ℂ))=fun x => ((iteratedDeriv k g x:ℝ):ℂ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ,ih,iteratedDeriv_succ]
    apply deriv_ofReal
    rw [iteratedDeriv_eq_iterate]
    exact (hg.iterate_deriv k).differentiable (by simp)
end StronglyRationalVOA.RealCircleCalculus
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
def realAngularVelocity (p : ℝ × ℝ) : ℝ := 2*Real.pi*φ.velocity p.1 (p.2/(2*Real.pi))
def realAngularDensity (g : ℝ → ℝ) (k : ℕ) (p : ℝ × ℝ) : ℝ := φ.density g k p.1 (p.2/(2*Real.pi))
lemma realAngularVelocity_smooth : ContDiff ℝ ∞ φ.realAngularVelocity :=
  contDiff_const.mul (φ.velocity_smooth.comp (contDiff_fst.prodMk (contDiff_snd.div_const _)))
lemma realAngularDensity_smooth {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (φ.realAngularDensity g k) :=
  (φ.density_smooth hg k).comp (contDiff_fst.prodMk (contDiff_snd.div_const _))
lemma realAngularDensity_pos {g : ℝ → ℝ} (hg : ∀ x, 0 < g x) (k : ℕ) (t x : ℝ) :
    0 < φ.realAngularDensity g k (t,x) :=
  mul_pos (pow_pos (φ.jacobian_pos _ _) _) (hg _)


def normalizedAnomaly (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (2*Real.pi)⁻¹*RealCircleCalculus.anomalyEnergy (2*Real.pi)
    (fun x => φ.realAngularDensity g 1 (t,x))
def anomalyShift (g : ℝ → ℝ) (c : ℂ) (t : ℝ) : ℂ :=
  c/24*((φ.normalizedAnomaly g t-φ.normalizedAnomaly g 0):ℝ)
@[simp] lemma anomalyShift_zero (g : ℝ → ℝ) (c : ℂ) : φ.anomalyShift g c 0=0 := by
  simp [anomalyShift]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open Filter MeasureTheory Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable (f : Field (2*Real.pi))
def unitParameter (x : ℝ) : ℝ := f (2*Real.pi*x)
lemma unitParameter_smooth : ContDiff ℝ ∞ f.unitParameter :=
  f.smooth.comp (contDiff_const.mul contDiff_id)
lemma unitParameter_periodic : Function.Periodic f.unitParameter 1 := by
  intro x
  dsimp only [unitParameter]
  rw [mul_add,mul_one,f.periodic]
lemma unitParameter_pos (x : ℝ) : 0 < f.unitParameter x := f.positive _
end StronglyRationalVOA.PositiveCircleGeometry.Field
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)
lemma density_power (g : ℝ → ℝ) (k : ℕ) (t x : ℝ) :
    φ.density (fun x => g x^k) k t x=(φ.density g 1 t x)^k := by
  simp only [density,pow_one,mul_pow]
end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

open UniformSpace Filter
open scoped Topology ContDiff

open Filter UniformSpace
open scoped Topology ContDiff

open UniformSpace Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothEnergyPower
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace

open UniformSpace Filter
open scoped Topology ContDiff

open Set MeasureTheory
open scoped ContDiff
namespace StronglyRationalVOA.RealCircleCalculus
lemma average_bounds {T K : ℝ} (hT : 0 < T) {h : ℝ → ℝ} (hh : Continuous h)
    (hb : ∀ x ∈ Icc 0 T, 0 ≤ h x ∧ h x ≤ K) :
    0 ≤ T⁻¹*(∫ x in 0..T,h x) ∧ T⁻¹*(∫ x in 0..T,h x) ≤ K := by
  have hnon : 0 ≤ ∫ x in 0..T,h x := intervalIntegral.integral_nonneg hT.le (fun x hx => (hb x hx).1)
  have hupper := intervalIntegral.integral_mono_on (μ := volume) hT.le (hh.intervalIntegrable 0 T)
    (continuous_const.intervalIntegrable 0 T) (fun x hx => (hb x hx).2)
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hupper
  refine ⟨mul_nonneg (inv_nonneg.mpr hT.le) hnon,?_⟩
  calc
    _ ≤ T⁻¹*(T*K) := mul_le_mul_of_nonneg_left hupper (inv_nonneg.mpr hT.le)
    _ = K := by field_simp
end StronglyRationalVOA.RealCircleCalculus

open UniformSpace Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.LocalCovariance
lemma continuous_power_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T L : Module.End ℂ E) (n : ℕ) (x : E) :
    Continuous (fun t : ℝ => ((T+(t:ℂ) • L)^n) x) := by
  induction n generalizing x with
  | zero => simpa only [pow_zero,Module.End.one_apply] using (continuous_const (y := x) : Continuous (fun _ : ℝ => x))
  | succ n ih =>
    have he (t : ℝ) : ((T+(t:ℂ) • L)^(n+1)) x=
        ((T+(t:ℂ) • L)^n) (T x)+(t:ℂ) • ((T+(t:ℂ) • L)^n) (L x) := by
      rw [pow_succ]
      change ((T+(t:ℂ) • L)^n) (T x+(t:ℂ) • L x)=_
      rw [map_add,map_smul]
    simp_rw [he]
    exact (ih (T x)).add (Complex.continuous_ofReal.smul (ih (L x)))
end StronglyRationalVOA.LocalCovariance

open UniformSpace Filter Set
open scoped Topology ContDiff

open UniformSpace Set
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GraphInvariantOf
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set

open UniformSpace Filter
open scoped Topology

open UniformSpace

open Filter MeasureTheory
open scoped Topology

open UniformSpace

open MeasureTheory Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothRotationKernel
def bump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : ℝ) :=
  ⟨ε/2,ε,by linarith,by linarith⟩
def kernel (ε : ℝ) (hε : 0 < ε) : ℝ → ℝ := (bump ε hε).normed volume
lemma integral (ε : ℝ) (hε : 0 < ε) : (∫ t, kernel ε hε t)=1 :=
  (bump ε hε).integral_normed
lemma support (ε : ℝ) (hε : 0 < ε) : Function.support (kernel ε hε)=Metric.ball 0 ε :=
  (bump ε hε).support_normed_eq
lemma tsupport (ε : ℝ) (hε : 0 < ε) : tsupport (kernel ε hε)=Metric.closedBall 0 ε :=
  (bump ε hε).tsupport_normed_eq
lemma normed_smooth (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (fun t => (kernel ε hε t : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (bump ε hε).contDiff_normed
def jet (ε : ℝ) (hε : 0 < ε) (j : ℕ) : ℝ → ℂ :=
  iteratedDeriv j (fun t => (kernel ε hε t : ℂ))
lemma jet_zero (ε : ℝ) (hε : 0 < ε) (t : ℝ) : jet ε hε 0 t=(kernel ε hε t : ℂ) := rfl
lemma jet_continuous (ε : ℝ) (hε : 0 < ε) (j : ℕ) : Continuous (jet ε hε j) :=
  (normed_smooth ε hε).continuous_iteratedDeriv j (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
lemma jet_derivative (ε : ℝ) (hε : 0 < ε) (j : ℕ) (t : ℝ) :
    HasDerivAt (jet ε hε j) (jet ε hε (j+1) t) t := by
  change HasDerivAt (iteratedDeriv j _) (iteratedDeriv (j+1) _ t) t
  rw [iteratedDeriv_succ]
  exact ((normed_smooth ε hε).differentiable_iteratedDeriv j (by exact_mod_cast ENat.natCast_lt_top j) t).hasDerivAt
lemma jet_support (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    _root_.tsupport (jet ε hε j) ⊆ Metric.closedBall 0 ε := by
  induction j with
  | zero =>
      change _root_.tsupport (fun t => (kernel ε hε t : ℂ)) ⊆ _
      rw [← tsupport ε hε]
      apply closure_mono
      intro t ht
      exact fun h => ht (by simp only [h,Complex.ofReal_zero])
  | succ j ih =>
      change _root_.tsupport (iteratedDeriv (j+1) _) ⊆ _
      rw [iteratedDeriv_succ]
      change _root_.tsupport (deriv (jet ε hε j)) ⊆ _
      exact tsupport_deriv_subset.trans ih
lemma jet_compactSupport (ε : ℝ) (hε : 0 < ε) (j : ℕ) : HasCompactSupport (jet ε hε j) :=
  (isCompact_closedBall (0 : ℝ) ε).of_isClosed_subset isClosed_closure (jet_support ε hε j)
lemma jet_bounded (ε : ℝ) (hε : 0 < ε) (j : ℕ) : ∃ C : ℝ, ∀ t, ‖jet ε hε j t‖ ≤ C := by
  obtain ⟨C,hC⟩ := ((jet_compactSupport ε hε j).isCompact_range
    (jet_continuous ε hε j)).isBounded.exists_norm_le
  exact ⟨C,fun t => hC _ ⟨t,rfl⟩⟩
def bound (ε : ℝ) (hε : 0 < ε) (j : ℕ) : ℝ := (jet_bounded ε hε j).choose
lemma norm_le_bound (ε : ℝ) (hε : 0 < ε) (j : ℕ) (t : ℝ) :
    ‖jet ε hε j t‖ ≤ bound ε hε j := (jet_bounded ε hε j).choose_spec t
lemma jet_vanish (ε : ℝ) (hε : 0 < ε) (j : ℕ) {t : ℝ} (ht : ε < |t|) : jet ε hε j t=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := jet_support ε hε j h
  simp only [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
  exact ht.not_ge hh
end StronglyRationalVOA.SmoothRotationKernel

open MeasureTheory Filter
open scoped Topology

open MeasureTheory Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothConjugateInner
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter

open Set MeasureTheory Filter UniformSpace
open scoped Topology

open Set UniformSpace
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
lemma onSubmodule_closure_graph_invariant (D : Submodule ℂ H) (P : Module.End ℂ D)
    (hP : (onSubmodule D P).IsClosable) (Q : H →L[ℂ] H) (hQ : ∀ x : D, Q x ∈ D)
    (hc : P*restricted D Q hQ = restricted D Q hQ*P)
    {x y : H} (hxy : (x,y) ∈ (onSubmodule D P).closure.graph) :
    (Q x,Q y) ∈ (onSubmodule D P).closure.graph := by
  apply graph_invariant_of_core _ hP Q _ hxy
  intro u v huv
  obtain ⟨z,rfl,rfl⟩ := (onSubmodule D P).mem_graph_iff.mp huv
  have h := onSubmodule_mem_graph D P (restricted D Q hQ z)
  have he := congrArg (fun R : Module.End ℂ D => (R z : H)) hc
  change (P (restricted D Q hQ z) : H) = Q (P z) at he
  rw [he] at h
  exact LinearPMap.le_graph_of_le (onSubmodule D P).le_closure h
end StronglyRationalVOA.SymmetricOperator

open Set UniformSpace Filter
open scoped Topology

open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
lemma compact_translation_radius {K O : Set (AddCircle (2*Real.pi))}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ x ∈ K, x+(t : AddCircle (2*Real.pi)) ∈ O := by
  let N : Set (ℝ × AddCircle (2*Real.pi)) :=
    (fun z => z.2+(z.1 : AddCircle (2*Real.pi))) ⁻¹' O
  have hc : Continuous (fun t : ℝ => (t : AddCircle (2*Real.pi))) := continuous_quotient_mk'
  have hN : IsOpen N := hO.preimage (continuous_snd.add (hc.comp continuous_fst))
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ N := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    have ht0 : t=0 := ht
    subst t
    change x+(0 : AddCircle (2*Real.pi)) ∈ O
    simpa only [add_zero] using hKO hx
  obtain ⟨u,v,hu,_,h0,hK',huv⟩ := generalized_tube_lemma isCompact_singleton hK hN hsub
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds (h0 (by rfl)))
  refine ⟨ε,hε,fun t ht x hx => ?_⟩
  change (t,x) ∈ N
  apply huv
  refine ⟨?_,hK' hx⟩
  exact he (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)


end StronglyRationalVOA.SmoothCircleFunction

open Set UniformSpace
open scoped Topology

open Set UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothConjugatePrimary
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter

open Set UniformSpace Filter
open scoped Topology

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA
lemma frequency_weight_shift (n j : ℤ) :
    1+|(n:ℝ)| ≤ (1+|((n-j:ℤ):ℝ)|)*(1+|(j:ℝ)|) := by
  have h := abs_add_le ((n:ℝ)-(j:ℝ)) (j:ℝ)
  have hp := mul_nonneg (abs_nonneg ((n:ℝ)-(j:ℝ))) (abs_nonneg (j:ℝ))
  push_cast
  rw [sub_add_cancel] at h
  nlinarith
end StronglyRationalVOA

open UniformSpace Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_RotationConjugateCommutant
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.SmoothCircleLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter

open UniformSpace Set

open UniformSpace Set

open scoped ContDiff
namespace StronglyRationalVOA


namespace SmoothCircleLift
@[ext] lemma ext {F G : SmoothCircleLift} (h : ∀ t, F t=G t) : F=G := by
  cases F with
  | mk f hf hfi hp =>
    cases G with
    | mk g hg hgi hgp =>
      have he : f=g := DFunLike.ext _ _ h
      subst g
      rfl
def identity : SmoothCircleLift where
  toOrderIso := OrderIso.refl ℝ
  smooth := contDiff_id
  inverse_smooth := contDiff_id
  period := fun _ => rfl
def compose (F G : SmoothCircleLift) : SmoothCircleLift where
  toOrderIso := G.toOrderIso.trans F.toOrderIso
  smooth := F.smooth.comp G.smooth
  inverse_smooth := G.inverse_smooth.comp F.inverse_smooth
  period := by intro t; change F (G (t+2*Real.pi))=F (G t)+2*Real.pi; rw [G.period,F.period]
def inverse (F : SmoothCircleLift) : SmoothCircleLift where
  toOrderIso := F.toOrderIso.symm
  smooth := F.inverse_smooth
  inverse_smooth := F.smooth
  period := by
    intro t
    apply F.toOrderIso.injective
    rw [F.toOrderIso.apply_symm_apply,F.period,F.toOrderIso.apply_symm_apply]
instance instGroup : Group SmoothCircleLift where
  mul := compose
  one := identity
  inv := inverse
  mul_assoc F G H := by ext; rfl
  one_mul F := by ext; rfl
  mul_one F := by ext; rfl
  inv_mul_cancel F := by ext t; exact F.toOrderIso.symm_apply_apply t
@[simp] lemma one_apply (t : ℝ) : (1 : SmoothCircleLift) t=t := rfl
@[simp] lemma mul_apply (F G : SmoothCircleLift) (t : ℝ) : (F*G) t=F (G t) := rfl
@[simp] lemma inv_apply_apply (F : SmoothCircleLift) (t : ℝ) : F⁻¹ (F t)=t := F.toOrderIso.symm_apply_apply t
@[simp] lemma apply_inv_apply (F : SmoothCircleLift) (t : ℝ) : F (F⁻¹ t)=t := F.toOrderIso.apply_symm_apply t
 
def rotation (s : ℝ) : SmoothCircleLift where
  toOrderIso := OrderIso.addRight s
  smooth := contDiff_id.add contDiff_const
  inverse_smooth := by
    change ContDiff ℝ ∞ (fun x : ℝ => x + -s)
    exact contDiff_id.add contDiff_const
  period := by intro t; change t+2*Real.pi+s=t+s+2*Real.pi; ring
@[simp] lemma rotation_apply (s t : ℝ) : rotation s t=t+s := rfl
lemma rotation_zero : rotation 0=1 := by ext; simp
lemma rotation_add (s t : ℝ) : rotation (s+t)=rotation s*rotation t := by ext; simp; ring
lemma circle_periodic (F : SmoothCircleLift) : Function.Periodic (fun t : ℝ => (F t : AddCircle (2*Real.pi))) (2*Real.pi) := by
  intro t
  change ((F.toOrderIso (t+2*Real.pi) : ℝ) : AddCircle (2*Real.pi)) =
    (F.toOrderIso t : AddCircle (2*Real.pi))
  rw [F.period,AddCircle.coe_add]
  simp
 
def onCircle (F : SmoothCircleLift) : AddCircle (2*Real.pi) → AddCircle (2*Real.pi) := F.circle_periodic.lift
@[simp] lemma onCircle_coe (F : SmoothCircleLift) (t : ℝ) : F.onCircle (t : AddCircle (2*Real.pi))=(F t : AddCircle (2*Real.pi)) := rfl
lemma onCircle_mul (F G : SmoothCircleLift) (t : AddCircle (2*Real.pi)) :
    (F*G).onCircle t=F.onCircle (G.onCircle t) := by
  induction t using QuotientAddGroup.induction_on with
  | H t => rfl
lemma onCircle_one (t : AddCircle (2*Real.pi)) : (1 : SmoothCircleLift).onCircle t=t := by
  induction t using QuotientAddGroup.induction_on with
  | H t => rfl
lemma onCircle_inverse (F : SmoothCircleLift) (t : AddCircle (2*Real.pi)) : F⁻¹.onCircle (F.onCircle t)=t := by
  rw [← onCircle_mul,inv_mul_cancel,onCircle_one]
lemma differentiable (F : SmoothCircleLift) : Differentiable ℝ F :=
  F.smooth.differentiable (by simp)
lemma derivative_positive (F : SmoothCircleLift) (t : ℝ) : 0 < deriv F t := by
  have hn : 0 ≤ deriv F t := F.toOrderIso.monotone.deriv_nonneg
  have hF := (F.differentiable t).hasDerivAt
  have hI := ((F⁻¹).differentiable (F t)).hasDerivAt
  have hh : HasDerivAt (fun x : ℝ => x) (deriv (fun x => (F⁻¹ : SmoothCircleLift) x) (F t)*deriv F t) t := by
    simpa only [Function.comp_def,inv_apply_apply] using hI.comp t hF
  have he : deriv (fun x => (F⁻¹ : SmoothCircleLift) x) (F t)*deriv F t=1 := hh.unique (hasDerivAt_id t)
  exact lt_of_le_of_ne hn (by intro hz; rw [← hz,mul_zero] at he; norm_num at he)
lemma continuous_onCircle (F : SmoothCircleLift) : Continuous F.onCircle := by
  exact ((AddCircle.continuous_mk' (2*Real.pi)).comp F.smooth.continuous).quotient_liftOn' _
 
def circleHomeomorph (F : SmoothCircleLift) :
    AddCircle (2*Real.pi) ≃ₜ AddCircle (2*Real.pi) where
  toFun := F.onCircle
  invFun := F⁻¹.onCircle
  left_inv := F.onCircle_inverse
  right_inv := by intro t; simpa using F⁻¹.onCircle_inverse t
  continuous_toFun := F.continuous_onCircle
  continuous_invFun := F⁻¹.continuous_onCircle
lemma deck_onCircle (n : ℤ) (t : AddCircle (2*Real.pi)) :
    (rotation (n*(2*Real.pi))).onCircle t=t := by
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    rw [onCircle_coe,rotation_apply,AddCircle.coe_add]
    have h : ((n*(2*Real.pi) : ℝ) : AddCircle (2*Real.pi))=0 := by
      exact (AddCircle.coe_eq_zero_iff (2*Real.pi)).mpr ⟨n,by simp [zsmul_eq_mul]⟩
    rw [h,add_zero]
 

lemma onCircle_eq_iff (F G : SmoothCircleLift) : F.onCircle=G.onCircle ↔
    ∃ n : ℤ, F=rotation (n*(2*Real.pi))*G := by
  constructor
  · intro h
    have hz (x : ℝ) : F x-G x ∈ AddSubgroup.zmultiples (2*Real.pi) := by
      have hq : ((F x-G x:ℝ) : AddCircle (2*Real.pi))=0 := by
        rw [AddCircle.coe_sub]
        exact sub_eq_zero.mpr (congrFun h (x:AddCircle (2*Real.pi)))
      exact (QuotientAddGroup.eq_zero_iff (F x-G x)).mp hq
    let D : ℝ → AddSubgroup.zmultiples (2*Real.pi) := fun x => ⟨F x-G x,hz x⟩
    have hD : Continuous D := (F.smooth.continuous.sub G.smooth.continuous).subtype_mk hz
    have hl : IsLocallyConstant D := (IsLocallyConstant.iff_continuous D).mpr hD
    have he (x : ℝ) : F x-G x=F 0-G 0 := congrArg Subtype.val
      (hl.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ x) (Set.mem_univ 0))
    obtain ⟨n,hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hz 0)
    refine ⟨n,?_⟩
    ext x
    simp only [mul_apply,rotation_apply]
    simp only [zsmul_eq_mul] at hn
    linarith [he x]
  · rintro ⟨n,rfl⟩
    funext x
    rw [onCircle_mul,deck_onCircle]
 
def circleAction : SmoothCircleLift →* Equiv.Perm (AddCircle (2*Real.pi)) where
  toFun F := F.circleHomeomorph.toEquiv
  map_one' := by ext x; exact onCircle_one x
  map_mul' F G := by ext x; exact onCircle_mul F G x
lemma circleAction_kernel (F : SmoothCircleLift) : F ∈ circleAction.ker ↔
    ∃ n : ℤ, F=rotation (n*(2*Real.pi)) := by
  change circleAction F=1 ↔ _
  have he : circleAction F=1 ↔ F.onCircle=(1 : SmoothCircleLift).onCircle := by
    constructor
    · intro h
      funext x
      rw [onCircle_one]
      exact congrArg (fun e : Equiv.Perm (AddCircle (2*Real.pi)) => e x) h
    · intro h
      ext x
      change F.onCircle x=x
      simpa only [onCircle_one] using congrFun h x
  rw [he,onCircle_eq_iff]
  simp only [mul_one]
end SmoothCircleLift
 

def SmoothCircleDiffeomorphism := SmoothCircleLift ⧸ SmoothCircleLift.circleAction.ker
instance instGroupSmoothCircleDiffeomorphism : Group SmoothCircleDiffeomorphism := inferInstanceAs
  (Group (SmoothCircleLift ⧸ SmoothCircleLift.circleAction.ker))
end StronglyRationalVOA

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
variable (F : SmoothCircleLift)
def unitParameter (x : ℝ) : ℝ := F (2*Real.pi*x)/(2*Real.pi)
lemma unitParameter_smooth : ContDiff ℝ ∞ F.unitParameter :=
  (F.smooth.comp (contDiff_const.mul contDiff_id)).div_const _
lemma unitParameter_derivative (x : ℝ) :
    HasDerivAt F.unitParameter (deriv F (2*Real.pi*x)) x := by
  have h := (((F.differentiable (2*Real.pi*x)).hasDerivAt).comp x
    ((hasDerivAt_id x).const_mul (2*Real.pi))).div_const (2*Real.pi)
  convert h using 1 <;> first | rfl | field_simp [Real.pi_ne_zero]
def unitLift : PositiveCircleGeometry.SmoothLift where
  toFun := F.unitParameter
  add_one := by
    intro x
    dsimp only [unitParameter]
    rw [mul_add,mul_one,F.period,add_div,div_self (by positivity : (2*Real.pi:ℝ) ≠ 0)]
  smooth := F.unitParameter_smooth
  derivative_pos := fun x => by rw [(F.unitParameter_derivative x).deriv]; exact F.derivative_positive _
@[simp] lemma unitLift_apply (x : ℝ) : F.unitLift x=F (2*Real.pi*x)/(2*Real.pi) := rfl
lemma unitLift_inverse_one (x : ℝ) :
    F.unitLift.inverse 1 (x/(2*Real.pi))=F⁻¹ x/(2*Real.pi) := by
  apply F.unitLift.strictMono.injective
  have h := F.unitLift.interpolate_inverse 1 (x/(2*Real.pi))
  rw [PositiveCircleGeometry.SmoothLift.interpolate_one] at h
  rw [h,F.unitLift_apply,mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ) ≠ 0),F.apply_inv_apply]
lemma unitLift_density_one (g : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    F.unitLift.density (fun t => g (2*Real.pi*t)) k 1 (x/(2*Real.pi))=
      (deriv F (F⁻¹ x))^k*g (F⁻¹ x) := by
  rw [PositiveCircleGeometry.SmoothLift.density,F.unitLift_inverse_one]
  simp only [PositiveCircleGeometry.SmoothLift.jacobian,Real.smoothTransition.one,
    sub_self,zero_add,one_mul]
  change deriv F.unitParameter (F⁻¹ x/(2*Real.pi))^k*g (2*Real.pi*(F⁻¹ x/(2*Real.pi)))=_
  rw [(F.unitParameter_derivative _).deriv,mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ) ≠ 0)]
end StronglyRationalVOA.SmoothCircleLift

open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
lemma derivative_periodic (F : SmoothCircleLift) : Function.Periodic (deriv F) (2*Real.pi) := by
  intro x
  have h : (fun y => F (y+2*Real.pi))=(fun y => F y+2*Real.pi) := funext F.period
  have he := congrFun (congrArg deriv h) x
  simpa only [deriv_comp_add_const,deriv_add_const] using he
lemma derivative_mul (F G : SmoothCircleLift) (x : ℝ) :
    deriv (fun y => (F*G) y) x=deriv F (G x)*deriv G x :=
  (((F.differentiable (G x)).hasDerivAt).comp x (G.differentiable x).hasDerivAt).deriv
 
def pushDensity (F : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv F (F⁻¹ x)^k*g (F⁻¹ x)
lemma pushDensity_smooth (F : SmoothCircleLift) (k : ℕ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (F.pushDensity k g) :=
  (((contDiff_infty_iff_deriv.mp F.smooth).2.comp (F⁻¹).smooth).pow k).mul
    (hg.comp (F⁻¹).smooth)
lemma pushDensity_periodic (F : SmoothCircleLift) (k : ℕ) {g : ℝ → ℝ}
    (hp : Function.Periodic g (2*Real.pi)) : Function.Periodic (F.pushDensity k g) (2*Real.pi) := by
  intro x
  dsimp only [pushDensity]
  rw [(F⁻¹).period,F.derivative_periodic,hp]
lemma pushDensity_pos (F : SmoothCircleLift) (k : ℕ) {g : ℝ → ℝ}
    (hg : ∀ x, 0 < g x) (x : ℝ) : 0 < F.pushDensity k g x :=
  mul_pos (pow_pos (F.derivative_positive _) k) (hg _)
lemma pushDensity_mul (F G : SmoothCircleLift) (k : ℕ) (g : ℝ → ℝ) :
    (F*G).pushDensity k g=F.pushDensity k (G.pushDensity k g) := by
  funext x
  dsimp only [pushDensity]
  rw [mul_inv_rev,mul_apply,derivative_mul,apply_inv_apply,mul_pow]
  ring
end StronglyRationalVOA.SmoothCircleLift

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
variable (F : SmoothCircleLift) (g : ℝ → ℝ)
def unitTest (x : ℝ) : ℝ := g (2*Real.pi*x)
lemma unitTest_smooth (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (unitTest g) :=
  hg.comp (contDiff_const.mul contDiff_id)
lemma unitTest_periodic (hp : Function.Periodic g (2*Real.pi)) : Function.Periodic (unitTest g) 1 := by
  intro x
  dsimp only [unitTest]
  rw [mul_add,mul_one,hp]
def anomaly (c : ℂ) : ℂ := c/24 * (((2*Real.pi)⁻¹ *
  (RealCircleCalculus.anomalyEnergy (2*Real.pi) (F.pushDensity 1 g)-
    RealCircleCalculus.anomalyEnergy (2*Real.pi) g) : ℝ) : ℂ)
lemma anomaly_endpoint (c : ℂ) :
    F.unitLift.anomalyShift (unitTest g) c 1=F.anomaly g c := by
  have h0 : (fun x => F.unitLift.realAngularDensity (unitTest g) 1 (0,x))=g := by
    funext x
    change F.unitLift.density (unitTest g) 1 0 (x/(2*Real.pi))=g x
    rw [PositiveCircleGeometry.SmoothLift.density_zero]
    dsimp only [unitTest]
    rw [mul_div_cancel₀ _ (by positivity : (2*Real.pi:ℝ) ≠ 0)]
  have h1 : (fun x => F.unitLift.realAngularDensity (unitTest g) 1 (1,x))=F.pushDensity 1 g := by
    funext x
    exact F.unitLift_density_one g 1 x
  simp only [PositiveCircleGeometry.SmoothLift.anomalyShift,
    PositiveCircleGeometry.SmoothLift.normalizedAnomaly,h0,h1,anomaly,mul_sub]
lemma anomaly_mul (G : SmoothCircleLift) (c : ℂ) :
    (F*G).anomaly g c=F.anomaly (G.pushDensity 1 g) c+G.anomaly g c := by
  simp only [anomaly,pushDensity_mul]
  push_cast
  ring
end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_DiffeomorphismStressSmooth
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.SmoothCircleLift.instTopologicalSpace _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
open UniformSpace Set Filter

open UniformSpace
open scoped ContDiff

open UniformSpace
open scoped ContDiff

open UniformSpace Set

open UniformSpace

open UniformSpace

open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleLift
lemma rotation_inv (s : ℝ) : (rotation s)⁻¹=rotation (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← rotation_add,add_neg_cancel,rotation_zero]
lemma derivative_rotation (s x : ℝ) : deriv (rotation s) x=1 := by
  exact ((hasDerivAt_id x).add_const s).deriv
lemma pushDensity_deck (n : ℤ) (k : ℕ) {g : ℝ → ℝ}
    (hp : Function.Periodic g (2*Real.pi)) :
    (rotation (n*(2*Real.pi))).pushDensity k g=g := by
  funext x
  simp only [pushDensity,rotation_inv,rotation_apply,derivative_rotation,one_pow,one_mul]
  have h := hp.zsmul (-n) x
  simpa only [zsmul_eq_mul,Int.cast_neg,neg_mul] using h
lemma anomaly_deck (n : ℤ) (g : ℝ → ℝ) (hp : Function.Periodic g (2*Real.pi)) (c : ℂ) :
    (rotation (n*(2*Real.pi))).anomaly g c=0 := by
  simp only [anomaly,pushDensity_deck n 1 hp,sub_self,mul_zero,Complex.ofReal_zero]
end StronglyRationalVOA.SmoothCircleLift

open UniformSpace Set

open UniformSpace Filter Set
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_GeometryContinuation
attribute [-instance] _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff

namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift
variable (φ : SmoothLift)

lemma jet_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv k φ) (iteratedDeriv (k+1) φ x) x := by
  rw [iteratedDeriv_succ]
  exact (φ.smooth.differentiable_iteratedDeriv k (by exact_mod_cast ENat.natCast_lt_top k) x).hasDerivAt

lemma jacobian_lower_near_identity {ε : ℝ} (hε : ε ≤ 1/2)
    (h1 : ∀ x, |deriv φ x-1| ≤ ε) (t y : ℝ) : 1/2 ≤ φ.jacobian t y := by
  have hd := (abs_le.mp (h1 y)).1
  have hb0 := Real.smoothTransition.nonneg t
  have hb1 := Real.smoothTransition.le_one t
  have he : -(Real.smoothTransition t)*ε ≤
      Real.smoothTransition t*(deriv φ y-1) := by nlinarith
  dsimp only [jacobian]
  nlinarith

lemma smoothTransition_deriv_bounded : ∃ B : ℝ, 0 < B ∧ ∀ t, |deriv Real.smoothTransition t| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
    (s := Icc (0:ℝ) 1)
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun t => ?_⟩
  by_cases ht : t ∈ Icc (0:ℝ) 1
  · exact (hB t ht).trans (le_max_right _ _)
  · have he : deriv Real.smoothTransition t = 0 := by
      rcases lt_or_ge t 0 with h | h
      · have hh : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
          filter_upwards [Iio_mem_nhds h] with s hs
          exact Real.smoothTransition.zero_of_nonpos hs.le
        rw [hh.deriv_eq, deriv_const]
      · have h1 : 1 < t := lt_of_not_ge (fun h1 => ht ⟨h,h1⟩)
        have hh : Real.smoothTransition =ᶠ[𝓝 t] fun _ => (1:ℝ) := by
          filter_upwards [Ioi_mem_nhds h1] with s hs
          exact Real.smoothTransition.one_of_one_le hs.le
        rw [hh.deriv_eq, deriv_const]
    rw [he, abs_zero]
    exact zero_le_one.trans (le_max_left _ _)



end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

end

end OAI
end

section
-- module Solutions.OAIQ3_Vtx.VertexAlgebra_SmoothTopology
attribute [-instance] _root_.OAI.MinimalVertex.Code.StronglyRationalVOA.SmoothCircleLift.instGroup _root_.OAI.StronglyRationalVOA.unitaryStrongTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

def identity : SmoothLift where
  toFun := id
  add_one := fun _ => rfl
  smooth := contDiff_id
  derivative_pos := by intro x; simp
@[simp] lemma identity_apply (x : ℝ) : identity x=x := rfl

def jet (φ : SmoothLift) (k : ℕ) : C(ℝ,ℝ) :=
  ⟨iteratedDeriv k φ, φ.smooth.continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))⟩

instance instTopologicalSpace : TopologicalSpace SmoothLift :=
  TopologicalSpace.induced (fun φ => jet φ) inferInstance

lemma continuous_jet (k : ℕ) : Continuous (fun φ : SmoothLift => jet φ k) :=
  (continuous_apply k).comp (show Continuous (fun φ : SmoothLift => jet φ) from continuous_induced_dom)

 
def identityError (φ : SmoothLift) : ℝ :=
  ∑ k ∈ Finset.range 5, ‖(jet φ k-jet identity k).restrict (Icc (0:ℝ) 1)‖

lemma identityError_nonneg (φ : SmoothLift) : 0 ≤ identityError φ :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

@[simp] lemma identityError_identity : identityError identity = 0 := by
  have h : (ContinuousMap.restrict (Icc (0:ℝ) 1) (0 : C(ℝ,ℝ))) = 0 := by ext; rfl
  simp [identityError,h]

end StronglyRationalVOA.PositiveCircleGeometry.SmoothLift

namespace StronglyRationalVOA.SmoothCircleLift

@[simp] lemma unitLift_one : (1 : SmoothCircleLift).unitLift = PositiveCircleGeometry.SmoothLift.identity := by
  cases h : (1 : SmoothCircleLift).unitLift with
  | mk f hp hs hd =>
    have hf : f=id := by
      funext x
      have hh := congrArg (fun φ : PositiveCircleGeometry.SmoothLift => φ x) h
      simpa using hh.symm
    subst f
    rfl

end StronglyRationalVOA.SmoothCircleLift

end

end OAI
end


