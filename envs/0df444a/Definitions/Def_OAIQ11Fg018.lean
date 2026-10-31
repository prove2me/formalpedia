-- Prove2me | Definitions.Def_OAIQ11Fg018
-- name    : OAIQ11Fg018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T10:38:23.478062+00:00
-- url     : https://prove2.me/theorems/d7e18673-95e1-4644-8912-c063a3a28622
-- title:
--   Definitions bundle OAIQ11Fg018 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 41 declarations of OpenAI's Lean: 11 definitions and 30 theorems. The definitions and types are `OAI.Generator.Tracial.traceFreeHilbertAction`, `OAI.Generator.Tracial.traceFreeHilbertActionCLM`, `OAI.Generator.Tracial.traceFreeHilbertBallMap`, `OAI.Generator.Tracial.traceFreeHilbertClosure`, `OAI.Generator.Tracial.traceFreeHilbertCoefficient`, `OAI.Generator.Tracial.traceFreeHilbertIntoClosure`, `OAI.Generator.Tracial.traceFreeHilbertVector`, `OAI.Generator.Tracial.traceFreeRightAction`, `OAI.Generator.Tracial.traceFreeRightOnPreHilbert`, `OAI.Generator.Tracial.traceHilbertClosureOperatorCStar`, `OAI.Generator.Tracial.traceHilbertWOTOperatorCStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean).
--
--   **Imports.** It imports the bundle `OAIQ11Fg017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ11Fg019`; the statements `OAI_Generator_Tracial_predualFunctionals_eq_cyclicPredual_of_membership`, `OAI.Generator.Tracial.traceFreeHilbert_singlyGenerated_pullback` and `OAI_Generator_Tracial_traceOrbit_isSeparable_of_cyclicPredual`; the proofs of `OAI_Generator_FiniteMatrixStage_exists_countable_tensor_refinement`, `OAI_Generator_FiniteMatrixStage_exists_irreducible_matrix_generated_algebra`, `OAI_Generator_FiniteMatrixStage_exists_refinement_descent`, `OAI_Generator_FiniteMatrixStage_exists_tensor_refinement_descent`, `OAI_Generator_Tracial_predualFunctional_unitBall_continuous` and `OAI_Generator_Tracial_relative_generation_at_continuity`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ11Fg017

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.dominationCStar
attribute [local instance] OAI.Generator.Tracial.dominationLE
theorem traceFreeTrace_matrix_diagonal {ι : Type*} [Fintype ι]
    (Q : EquivalentPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) ι)
    (x : M.toStarSubalgebra) :
    (∑ i, traceFreeTrace hfactor hdiff hfinite hunit (Q.stateCoefficient x i i))=
      traceFreeTrace hfactor hdiff hfinite hunit x := by
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have ht := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2
  have hi (i : ι) : τ (Q.stateCoefficient x i i)=τ ((Q.leg i).target.val*x) := by
    change τ ((star (Q.leg i).val*x)*(Q.leg i).val)=_
    rw [ht]
    congr 1
  change (∑ i, τ (Q.stateCoefficient x i i))=τ x
  simp_rw [hi]
  rw [← map_sum,← Finset.sum_mul,Q.total,one_mul]

attribute [local instance] OAI.Generator.Tracial.dominationOrder
local instance dominationPreorder_rf26c3b_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.dominationStarOrder
theorem traceFreeTrace_exists_finite_vector_domination :
    ∃ (n : ℕ) (ξ : Fin n → H) (C : ℝ), 0<C ∧
      ∀ x : M.toStarSubalgebra, 0 ≤ x →
        (traceFreeTrace hfactor hdiff hfinite hunit x).re ≤
          C * ∑ i, (inner ℂ (ξ i) (x.val (ξ i))).re := by
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,a,hE,ha,hloc⟩ := exists_localized_vector_functional hfactor hdiff hfinite hunit ξ hξ 1 (by norm_num)
  obtain ⟨n,_,Q,hQE,_⟩ := exists_equivalent_partition_base_le hfactor hdiff hfinite hunit E hE
  refine ⟨n,fun i => (Q.leg i).val.val ξ,a⁻¹,inv_pos.mpr ha,?_⟩
  intro x hx
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have hi (i : Fin n) : a*(τ (Q.stateCoefficient x i i)).re ≤
      (vectorFunctional ξ (Q.stateCoefficient x i i)).re := by
    have hpos : 0 ≤ Q.stateCoefficient x i i := star_left_conjugate_nonneg hx (Q.leg i).val
    have hEx : E.val*Q.stateCoefficient x i i=Q.stateCoefficient x i i := by
      calc E.val*Q.stateCoefficient x i i =
          E.val*(Q.base.val*Q.stateCoefficient x i i) := by rw [Q.stateCoefficient_left]
        _ = Q.stateCoefficient x i i := by rw [← mul_assoc,hQE,Q.stateCoefficient_left]
    have h := (hloc (Q.stateCoefficient x i i) hpos hEx).1
    rwa [← traceFreeTrace_selfAdjoint hfactor hdiff hfinite hunit _ hpos.isSelfAdjoint] at h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
  rw [← Finset.mul_sum,← Complex.re_sum,
    traceFreeTrace_matrix_diagonal hfactor hdiff hfinite hunit] at hsum
  have hv : (∑ i, (vectorFunctional ξ (Q.stateCoefficient x i i)).re)=
      ∑ i, (inner ℂ ((Q.leg i).val.val ξ) (x.val ((Q.leg i).val.val ξ))).re := by
    rw [← Complex.re_sum,← Q.matrixVectorFunctional_apply]
    simp only [EquivalentPartition.matrixVectorFunctional,sum_apply,Complex.re_sum,
      vectorFunctional_apply]
  rw [hv] at hsum
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr ha.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] using h

/-- The scalar Cauchy--Schwarz bound follows from positivity of a centered square. -/
theorem traceFreeTrace_norm_sq_le (x : M.toStarSubalgebra) :
    ‖traceFreeTrace hfactor hdiff hfinite hunit x‖^2 ≤
      (traceFreeTrace hfactor hdiff hfinite hunit (star x*x)).re := by
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  obtain ⟨_,h1,hpos,hstar,_⟩ := traceFreeTrace_spec hfactor hdiff hfinite hunit
  change τ 1=1 at h1
  change ∀ x : M.toStarSubalgebra, τ (star x)=star (τ x) at hstar
  have h := hpos (star (x-(τ x) • 1)*(x-(τ x) • 1)) (star_mul_self_nonneg _)
  change 0 ≤ (τ (star (x-(τ x) • 1)*(x-(τ x) • 1))).re at h
  have he : τ (star (x-(τ x) • 1)*(x-(τ x) • 1))=
      τ (star x*x)-star (τ x)*(τ x) := by
    simp only [star_sub,star_smul,star_one,sub_mul,mul_sub,smul_mul_assoc,
      mul_smul_comm,mul_one,one_mul,map_sub,map_smul,smul_eq_mul,h1,hstar]
    ring
  rw [he,Complex.sub_re] at h
  change ‖τ x‖^2 ≤ (τ (star x*x)).re
  have hn : (star (τ x)*(τ x)).re=‖τ x‖^2 := by
    rw [RCLike.star_def,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]
  rw [hn] at h
  linarith

end

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.traceNormalCStar
attribute [local instance] OAI.Generator.Tracial.traceNormalOrder
local instance traceNormalPreorder_rf26c3b_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceNormalLE_rf26c3b_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
attribute [local instance] OAI.Generator.Tracial.traceNormalStarOrder
theorem traceFreeTrace_finite_vector_representation :
    ∃ (n : ℕ) (ξ η : Fin n → H), ∀ x : M.toStarSubalgebra,
      traceFreeTrace hfactor hdiff hfinite hunit x=∑ i, inner ℂ (η i) (x.val (ξ i)) := by
  obtain ⟨n,ξ,C,hC,hbound⟩ := traceFreeTrace_exists_finite_vector_domination hfactor hdiff hfinite hunit
  let V := PiLp 2 (fun _ : Fin n => H)
  let F : M.toStarSubalgebra →ₗ[ℂ] V :=
    { toFun := fun x => WithLp.toLp 2 (fun i => x.val (ξ i))
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have hb (x : M.toStarSubalgebra) : ‖τ x‖ ≤ Real.sqrt C*‖F x‖ := by
    have hs := (traceFreeTrace_norm_sq_le hfactor hdiff hfinite hunit x).trans
      (hbound (star x*x) (star_mul_self_nonneg _))
    have hi (i : Fin n) : (inner ℂ (ξ i) ((star x*x).val (ξ i))).re=‖x.val (ξ i)‖^2 := by
      change (vectorFunctional (ξ i) (star x*x)).re=_
      rw [vectorFunctional_star_mul_self,← Complex.ofReal_pow,Complex.ofReal_re]
    simp only [hi] at hs
    have hFn : ‖F x‖^2=∑ i, ‖x.val (ξ i)‖^2 := PiLp.norm_sq_eq_of_L2 _ (F x)
    rw [← hFn] at hs
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hC.le]
    exact hs
  obtain ⟨η,hη⟩ := exists_inner_factor_of_bound F τ.toLinearMap (Real.sqrt C) hb
  refine ⟨n,ξ,fun i => η i,?_⟩
  intro x
  exact (hη x).trans (PiLp.inner_apply η (F x))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner OAI.vonNeumannToStarSubalgebraIsClosed 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit

local notation "L" => traceFreeLeftAction hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertOperatorCStar
@[simp] theorem traceFreeLeftAction_zero : L 0 = 0 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [traceFreeLeftAction_coe,map_zero,zero_mul,zero_apply,UniformSpace.Completion.coe_zero]

attribute [local instance] OAI.Generator.Tracial.traceHilbertActionCStar
@[simp] theorem traceFreeLeftAction_star (a : M.toStarSubalgebra) : L (star a) = star (L a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b c
  obtain ⟨b,rfl⟩ := (copy).surjective b
  obtain ⟨c,rfl⟩ := (copy).surjective c
  rw [traceFreeLeftAction_coe,traceFreeLeftAction_coe]
  rw [UniformSpace.Completion.inner_coe,UniformSpace.Completion.inner_coe]
  change τ₀ (star (star a*b)*c) = τ₀ (star b*(a*c))
  simp only [star_mul,star_star,mul_assoc]

def traceFreeHilbertAction : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun := L
  map_one' := traceFreeLeftAction_one hfactor hdiff hfinite hunit
  map_mul' := traceFreeLeftAction_mul hfactor hdiff hfinite hunit
  map_zero' := traceFreeLeftAction_zero hfactor hdiff hfinite hunit
  map_add' := traceFreeLeftAction_add hfactor hdiff hfinite hunit
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,traceFreeLeftAction_smul,traceFreeLeftAction_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := traceFreeLeftAction_star hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeHilbertAction_inclusion (a x : M.toStarSubalgebra) :
    π a (ι (copy x)) = ι (copy (a*x)) := by
  exact (traceFreeLeftAction_inclusion hfactor hdiff hfinite hunit a (copy x)).trans
    (congrArg ι ((copy).map_mul a x).symm)

def traceFreeHilbertVector : K := ι (copy 1)

local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

@[simp] theorem traceFreeHilbertAction_vector (a : M.toStarSubalgebra) :
    π a Ω = ι (copy a) := by
  change π a (ι (copy 1)) = _
  rw [traceFreeHilbertAction_inclusion,mul_one]

theorem traceFreeHilbertAction_injective : Function.Injective π := by
  intro a b hab
  have hv := congrArg (fun T : K →L[ℂ] K => T Ω) hab
  simp only [traceFreeHilbertAction_vector] at hv
  exact (copy).injective ((ι).injective hv)

local instance traceHilbertActionOrder_rf26c3b_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertActionStarOrder_rf26c3b_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem traceFreeHilbertAction_norm (a : M.toStarSubalgebra) : ‖π a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map π (traceFreeHilbertAction_injective hfactor hdiff hfinite hunit) a

theorem traceFreeHilbertAction_trace (a : M.toStarSubalgebra) : inner ℂ Ω (π a Ω) = τ₀ a := by
  rw [traceFreeHilbertAction_vector]
  change inner ℂ (ι (copy 1)) (ι (copy a)) = _
  rw [traceFreeInclusion_inner,star_one,one_mul]

theorem traceFreeHilbertAction_cyclic : DenseRange (fun a : M.toStarSubalgebra => π a Ω) := by
  have hc : Function.Surjective (fun a : M.toStarSubalgebra => copy a) :=
    fun b => ⟨(copy).symm b,(copy).apply_symm_apply b⟩
  have h := (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit).comp
    hc.denseRange (ι).continuous
  simpa only [traceFreeHilbertAction_vector,Function.comp_def] using h

end

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertRightCStar
local instance traceHilbertRightOperatorCStar_rf26c3b_1 : CStarAlgebra (K →L[ℂ] K) := {}
theorem traceFreeCopy_star_norm (x : M.toStarSubalgebra) : ‖copy (star x)‖ = ‖copy x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [traceFreeCopy_norm_sq,traceFreeCopy_norm_sq,star_star,
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2]

local instance traceHilbertRightOrder_rf26c3b_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertRightStarOrder_rf26c3b_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
theorem traceFreeCopy_mul_norm_le_right (a x : M.toStarSubalgebra) :
    ‖copy (x*a)‖ ≤ ‖a‖ * ‖copy x‖ := by
  rw [← traceFreeCopy_star_norm hfactor hdiff hfinite hunit (x*a),star_mul]
  simpa only [norm_star,traceFreeCopy_star_norm] using
    traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit (star a) (star x)

def traceFreeRightOnPreHilbert (a : M.toStarSubalgebra) : E →L[ℂ] E :=
  LinearMap.mkContinuous (LinearMap.mulRight ℂ (copy a)) ‖a‖ (by
    intro x
    obtain ⟨x,rfl⟩ := (copy).surjective x
    exact traceFreeCopy_mul_norm_le_right hfactor hdiff hfinite hunit a x)

def traceFreeRightAction (a : M.toStarSubalgebra) : K →L[ℂ] K :=
  ((ι).toContinuousLinearMap.comp (traceFreeRightOnPreHilbert hfactor hdiff hfinite hunit a)).extend
    (ι).toContinuousLinearMap

local notation "R" => traceFreeRightAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeRightAction_inclusion (a : M.toStarSubalgebra) (x : E) :
    R a (ι x) = ι (x*copy a) := by
  exact ContinuousLinearMap.extend_eq
    ((ι).toContinuousLinearMap.comp (traceFreeRightOnPreHilbert hfactor hdiff hfinite hunit a))
    (e := (ι).toContinuousLinearMap) (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    ((ι).isometry.isUniformInducing) x

@[simp] theorem traceFreeRightAction_coe (a : M.toStarSubalgebra) (x : E) :
    R a (x : K) = ((x*copy a : E) : K) :=
  traceFreeRightAction_inclusion hfactor hdiff hfinite hunit a x

theorem traceFreeLeftRight_commute (a b : M.toStarSubalgebra) : π a*R b = R b*π a := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  change traceFreeLeftAction hfactor hdiff hfinite hunit a (R b (c : K)) =
    R b (traceFreeLeftAction hfactor hdiff hfinite hunit a (c : K))
  simp only [traceFreeLeftAction_coe,traceFreeRightAction_coe,mul_assoc]

@[simp] theorem traceFreeRightAction_vector (a : M.toStarSubalgebra) : R a Ω = ι (copy a) := by
  change R a (ι (copy 1)) = _
  rw [traceFreeRightAction_inclusion,map_one,one_mul]

end

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/
section
open Filter
open scoped ComplexConjugate CStarAlgebra Pointwise Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local instance traceHilbertClosureOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

/-- The bicommutant is a von Neumann algebra; no image-closedness is assumed. -/
def traceFreeHilbertClosure : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))) =
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    simp only [Set.centralizer_centralizer_centralizer]

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

theorem traceFreeHilbertClosure_mem_iff (T : K →L[ℂ] K) :
    T ∈ N ↔ T ∈ Set.centralizer (Set.centralizer ((π).range : Set (K →L[ℂ] K))) := by
  change T ∈ (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) ↔ _
  simp only [← SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq,Set.union_self]

theorem traceFreeHilbertAction_mem_closure (a : M.toStarSubalgebra) : π a ∈ N := by
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit _).mpr
  intro T hT
  exact (hT (π a) ⟨a,rfl⟩).symm

def traceFreeHilbertIntoClosure : M.toStarSubalgebra →⋆ₐ[ℂ] (N).toStarSubalgebra :=
  (π).codRestrict (N).toStarSubalgebra (traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit)

theorem traceFreeHilbertClosure_strong_net (T : (N).toStarSubalgebra) :
    ∃ a : Finset K × ℕ → M.toStarSubalgebra, ∀ x : K,
      Tendsto (fun d => π (a d) x) atTop (𝓝 (T.val x)) := by
  obtain ⟨b,hb⟩ := bicommutant_exists_strong_net (π).range T.val
    ((traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit T.val).mp T.property)
  have hex (d : Finset K × ℕ) : ∃ a : M.toStarSubalgebra, π a = (b d).val := (b d).property
  choose a ha using hex
  exact ⟨a,fun x => by simpa only [ha] using hb x⟩

theorem traceFreeHilbertClosure_right_commute (T : (N).toStarSubalgebra) (a : M.toStarSubalgebra) :
    traceFreeRightAction hfactor hdiff hfinite hunit a*T.val =
      T.val*traceFreeRightAction hfactor hdiff hfinite hunit a := by
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit T.val).mp T.property
  rintro B ⟨b,rfl⟩
  exact traceFreeLeftRight_commute hfactor hdiff hfinite hunit b a

theorem traceFreeHilbertClosure_separating (T : (N).toStarSubalgebra) (hT : T.val Ω = 0) : T = 0 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  change ∀ x : K, T.val x = (0 : K)
  apply isClosed_property (traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit)
    (isClosed_eq T.val.continuous continuous_const)
  intro a
  rw [traceFreeHilbertAction_vector,← traceFreeRightAction_vector hfactor hdiff hfinite hunit a]
  have he := congrArg (fun B : K →L[ℂ] K => B Ω)
    (traceFreeHilbertClosure_right_commute hfactor hdiff hfinite hunit T a)
  simpa only [mul_apply_eq_comp,hT,map_zero] using he.symm

local instance traceHilbertClosureCStar_rf26c3b_1 : CStarAlgebra M.toStarSubalgebra := {}
theorem traceFreeHilbertClosure_trace_commute_copy (T : (N).toStarSubalgebra) (b : M.toStarSubalgebra) :
    inner ℂ Ω (T.val (π b Ω)) = inner ℂ Ω (π b (T.val Ω)) := by
  classical
  obtain ⟨a,ha⟩ := traceFreeHilbertClosure_strong_net hfactor hdiff hfinite hunit T
  have he (d : Finset K × ℕ) : inner ℂ Ω (π (a d) (π b Ω)) =
      inner ℂ Ω (π b (π (a d) Ω)) := by
    change inner ℂ Ω ((π (a d)*π b) Ω) = inner ℂ Ω ((π b*π (a d)) Ω)
    rw [← map_mul,← map_mul,traceFreeHilbertAction_trace,traceFreeHilbertAction_trace]
    exact (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2 _ _
  have hl := (innerSL ℂ Ω).continuous.continuousAt.tendsto.comp (ha (π b Ω))
  have hr := ((innerSL ℂ Ω).comp (π b)).continuous.continuousAt.tendsto.comp (ha Ω)
  exact tendsto_nhds_unique hl (hr.congr (fun d => (he d).symm))

theorem traceFreeHilbertClosure_trace_commute (S T : (N).toStarSubalgebra) :
    inner ℂ Ω (S.val (T.val Ω)) = inner ℂ Ω (T.val (S.val Ω)) := by
  classical
  obtain ⟨a,ha⟩ := traceFreeHilbertClosure_strong_net hfactor hdiff hfinite hunit S
  have hl := (innerSL ℂ Ω).continuous.continuousAt.tendsto.comp (ha (T.val Ω))
  have hr := ((innerSL ℂ Ω).comp T.val).continuous.continuousAt.tendsto.comp (ha Ω)
  exact tendsto_nhds_unique hl (hr.congr (fun d =>
    traceFreeHilbertClosure_trace_commute_copy hfactor hdiff hfinite hunit T (a d)))

end

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertWOTOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertWOTCStar
local instance traceHilbertWOTOrder_rf26c3b_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertWOTStarOrder_rf26c3b_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
def traceFreeHilbertActionCLM : M.toStarSubalgebra →L[ℂ] (K →L[ℂ] K) :=
  (π).toLinearMap.mkContinuous 1 (by
    intro a
    rw [one_mul]
    exact (traceFreeHilbertAction_norm hfactor hdiff hfinite hunit a).le)

def traceFreeHilbertCoefficient (x y : K) : StrongDual ℂ M.toStarSubalgebra :=
  (innerSL ℂ y).comp ((ContinuousLinearMap.apply ℂ K x).comp
    (traceFreeHilbertActionCLM hfactor hdiff hfinite hunit))

@[simp] theorem traceFreeHilbertCoefficient_apply (x y : K) (a : M.toStarSubalgebra) :
    traceFreeHilbertCoefficient hfactor hdiff hfinite hunit x y a = inner ℂ y (π a x) := rfl

theorem traceFreeHilbertCoefficient_continuous : Continuous
    (fun p : K × K => traceFreeHilbertCoefficient hfactor hdiff hfinite hunit p.1 p.2) :=
  ((innerSL ℂ).continuous.comp continuous_snd).clm_comp
    (((ContinuousLinearMap.apply ℂ K).continuous.comp continuous_fst).clm_comp continuous_const)

theorem traceFreeHilbertCoefficient_copy_ball_continuous (C : ℝ) (a b : M.toStarSubalgebra) :
    Continuous (fun T : weakOperatorBall M C =>
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit (ι (copy a)) (ι (copy b))
        ⟨T.val.toCLM,T.property.1⟩) := by
  obtain ⟨n,ξ,η,ht⟩ := traceFreeTrace_finite_vector_representation hfactor hdiff hfinite hunit
  have he (T : weakOperatorBall M C) :
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit (ι (copy a)) (ι (copy b))
        ⟨T.val.toCLM,T.property.1⟩ = ∑ i, inner ℂ (b.val (η i)) (T.val (a.val (ξ i))) := by
    rw [traceFreeHilbertCoefficient_apply,traceFreeHilbertAction_inclusion,traceFreeInclusion_inner,ht]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (η i) ((star b.val) (T.val (a.val (ξ i)))) = _
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp_rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (a.val (ξ i)) (b.val (η i)))

theorem traceFreeHilbertCoefficient_ball_continuous (C : ℝ) (x y : K) :
    Continuous (fun T : weakOperatorBall M C =>
      inner ℂ y (π ⟨T.val.toCLM,T.property.1⟩ x)) := by
  have hd : DenseRange (fun a : M.toStarSubalgebra => ι (copy a)) := by
    simpa only [traceFreeHilbertAction_vector] using
      traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit
  have hc := (ballContinuousFunctionals_isClosed M C).preimage
    (traceFreeHilbertCoefficient_continuous hfactor hdiff hfinite hunit)
  have hm : ∀ p : K × K,
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit p.1 p.2 ∈ ballContinuousFunctionals M C := by
    apply isClosed_property (hd.prodMap hd) hc
    intro p
    exact traceFreeHilbertCoefficient_copy_ball_continuous hfactor hdiff hfinite hunit C p.1 p.2
  exact hm (x,y)

def traceFreeHilbertBallMap (C : ℝ) (T : weakOperatorBall M C) : K →WOT[ℂ] K :=
  ContinuousLinearMapWOT.ofCLM (π ⟨T.val.toCLM,T.property.1⟩)

theorem traceFreeHilbertBallMap_continuous (C : ℝ) :
    Continuous (traceFreeHilbertBallMap hfactor hdiff hfinite hunit C) :=
  ContinuousLinearMapWOT.continuous_iff.mpr
    (traceFreeHilbertCoefficient_ball_continuous hfactor hdiff hfinite hunit C)

end Generator.Tracial

end

end OAI
end


