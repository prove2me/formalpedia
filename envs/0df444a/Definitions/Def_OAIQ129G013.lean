-- Prove2me | Definitions.Def_OAIQ129G013
-- name    : OAIQ129G013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T20:52:42.751243+00:00
-- url     : https://prove2.me/theorems/22958985-dbf2-47c1-9ad9-5789f816e5ba
-- title:
--   Definitions bundle OAIQ129G013 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.RelativeGeneration.main_theorem` and `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 13 definitions, 2 instances and 34 theorems. The definitions and types are `OAI.Generator.Tracial.TraceFreeHilbert`, `OAI.Generator.Tracial.productFamilyValue`, `OAI.Generator.Tracial.traceFreeHilbertAction`, `OAI.Generator.Tracial.traceFreeHilbertClosure`, `OAI.Generator.Tracial.traceFreeHilbertVector`, `OAI.Generator.Tracial.traceFreeInclusion`, `OAI.Generator.Tracial.traceFreeInnerCore`, `OAI.Generator.Tracial.traceFreeLeftAction`, `OAI.Generator.Tracial.traceFreeLeftOnPreHilbert`, `OAI.Generator.Tracial.traceFreeRightAction`, `OAI.Generator.Tracial.traceFreeRightOnPreHilbert`, `OAI.Generator.Tracial.traceHilbertClosureOperatorCStar`, `OAI.Generator.Tracial.traceHilbertOperatorCStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_ProductWords`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/ProductWords.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean).
--
--   **Imports.** It imports the bundles `OAIQ129G010` and `OAIQ129G011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ129G015`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ129G010
import Definitions.Def_OAIQ129G011

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cornerSpace_complete _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

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
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.traceCStar
attribute [local instance] OAI.Generator.Tracial.traceOrder
local instance tracePreorder_rd8c884_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.traceLE
attribute [local instance] OAI.Generator.Tracial.traceStarOrder
theorem traceFreeTrace_projection (p : AlgebraProjection M) :
    traceFreeTrace hfactor hdiff hfinite hunit p.val=(traceFreeDimension hfactor hdiff p : ℂ) := by
  obtain ⟨_,h1,hpos,hstar,htrace⟩ := traceFreeTrace_spec hfactor hdiff hfinite hunit
  exact tracialFunctional_projection_dimension hfactor hdiff hfinite hunit _ h1 hpos hstar htrace p

theorem traceFreeTrace_selfAdjoint (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    traceFreeTrace hfactor hdiff hfinite hunit x=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx :=
  functional_eq_dimensionSpectralValue hfactor hdiff hfinite hunit _
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).1
    (traceFreeTrace_projection hfactor hdiff hfinite hunit) x hx

theorem traceFreeTrace_faithful (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    traceFreeTrace hfactor hdiff hfinite hunit x=0 ↔ x=0 := by
  rw [traceFreeTrace_selfAdjoint hfactor hdiff hfinite hunit x hx.isSelfAdjoint]
  exact dimensionSpectralValue_eq_zero_iff_of_nonneg hfactor hdiff hfinite hunit x hx

end

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_ProductWords
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Exact signed-word expansion for a product of two unitaries. A unit gap
is allowed only between equal signs; opposite signs retain a centered gap. -/

/-! The actual countable centered coefficients needed to expand words in UV. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

def productFamilyValue (u : Q τ ω) (x : ℕ → Q τ ω) : ProductFamilyIndex → Q τ ω
  | .inl i => x i
  | .inr (.inl (s,i)) => if s then star u*optionalCoefficient x i else optionalCoefficient x i*u
  | .inr (.inr i) => star u*x i*u

end

/-! Expand positive-length signed powers into individual letters. Repeated
letters have unit gaps; boundaries between powers retain centered coefficients. -/

open UltrapowerBridge Filter

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ129_RG2.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.Generator.CoefficientOrder.coefficientPartialOrder _root_.OAI.Generator.Tracial.quotientInnerProductSpace _root_.OAI.Generator.Tracial.quotientNormedAddCommGroup _root_.OAI.Generator.Tracial.sequencesIsTopologicalRing _root_.OAI.Generator.predualAlgebraDualNormed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] OAI.closedSubmoduleNormedAddCommGroup OAI.closedSubmoduleNormedSpace OAI.closedSubmoduleInner 

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
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
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertCStar
attribute [local instance] OAI.Generator.Tracial.traceHilbertOrder
attribute [local instance] OAI.Generator.Tracial.traceHilbertStarOrder
@[instance_reducible] def traceFreeInnerCore : InnerProductSpace.Core ℂ E where
  inner x y := τ₀ (star ((copy).symm x) * (copy).symm y)
  conj_inner_symm x y := by
    change star (τ₀ (star ((copy).symm y) * (copy).symm x)) = _
    rw [← (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.1]
    simp only [star_mul, star_star]
  re_inner_nonneg x :=
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1 _ (star_mul_self_nonneg _)
  add_left x y z := by simp only [map_add, star_add, add_mul]
  smul_left x y c := by
    simp only [map_smul, star_smul, smul_mul_assoc]
    rfl
  definite x hx := by
    have hz := (traceFreeTrace_faithful hfactor hdiff hfinite hunit _
      (star_mul_self_nonneg ((copy).symm x))).mp hx
    have hx' : (copy).symm x = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
    exact (copy).symm.injective (hx'.trans (map_zero (copy).symm).symm)

instance traceFreePreHilbertNormedAddCommGroup : NormedAddCommGroup E :=
  (traceFreeInnerCore hfactor hdiff hfinite hunit).toNormedAddCommGroup
instance traceFreePreHilbertInnerProductSpace : InnerProductSpace ℂ E :=
  .ofCore { traceFreeInnerCore hfactor hdiff hfinite hunit with }

@[simp] theorem traceFreeCopy_inner (x y : M.toStarSubalgebra) :
    inner ℂ (copy x) (copy y) = τ₀ (star x*y) := rfl

theorem traceFreeCopy_norm_sq (x : M.toStarSubalgebra) :
    ‖copy x‖^2 = (τ₀ (star x*x)).re := by
  rw [← traceFreeCopy_inner hfactor hdiff hfinite hunit]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (copy x)).symm

/-- The actual Hilbert completion; no representation is supplied. -/
abbrev TraceFreeHilbert := UniformSpace.Completion E

def traceFreeInclusion : E →ₗᵢ[ℂ] TraceFreeHilbert hfactor hdiff hfinite hunit :=
  UniformSpace.Completion.toComplₗᵢ

@[simp] theorem traceFreeInclusion_inner (x y : M.toStarSubalgebra) :
    inner ℂ (traceFreeInclusion hfactor hdiff hfinite hunit (copy x))
      (traceFreeInclusion hfactor hdiff hfinite hunit (copy y)) = τ₀ (star x*y) :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (copy x) (copy y)

theorem traceFreeInclusion_denseRange :
    DenseRange (traceFreeInclusion hfactor hdiff hfinite hunit) :=
  UniformSpace.Completion.denseRange_coe

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/
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

attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundCStar
attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundOrder
attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundPreorder
attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundLE
attribute [local instance] OAI.Generator.Tracial.traceHilbertBoundStarOrder
theorem traceFreeTrace_mul_square_le (a x : M.toStarSubalgebra) :
    (τ₀ (star (a*x)*(a*x))).re ≤ ‖a‖^2 * (τ₀ (star x*x)).re := by
  have hp : 0 ≤ algebraMap ℝ M.toStarSubalgebra (‖a‖^2)-star a*a :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq)
  have h := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1 _
    (star_left_conjugate_nonneg hp x)
  have he : star x*(algebraMap ℝ M.toStarSubalgebra (‖a‖^2)-star a*a)*x =
      (‖a‖^2) • (star x*x)-star (a*x)*(a*x) := by
    simp only [Algebra.algebraMap_eq_smul_one,mul_sub,sub_mul,mul_smul_comm,
      smul_mul_assoc,mul_one,star_mul,mul_assoc]
  rw [he,map_sub, ContinuousLinearMap.map_smul_of_tower, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact sub_nonneg.mp h

theorem traceFreeCopy_mul_norm_le (a x : M.toStarSubalgebra) :
    ‖copy (a*x)‖ ≤ ‖a‖ * ‖copy x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, traceFreeCopy_norm_sq, traceFreeCopy_norm_sq]
  exact traceFreeTrace_mul_square_le hfactor hdiff hfinite hunit a x

end

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

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

def traceFreeLeftOnPreHilbert (a : M.toStarSubalgebra) : E →L[ℂ] E :=
  LinearMap.mkContinuous (LinearMap.mulLeft ℂ (copy a)) ‖a‖ (by
    intro x
    obtain ⟨x,rfl⟩ := (copy).surjective x
    exact traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit a x)

@[simp] theorem traceFreeLeftOnPreHilbert_apply (a : M.toStarSubalgebra) (x : E) :
    traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a x = copy a*x := rfl

def traceFreeLeftAction (a : M.toStarSubalgebra) : K →L[ℂ] K :=
  ((ι).toContinuousLinearMap.comp (traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a)).extend
    (ι).toContinuousLinearMap

local notation "L" => traceFreeLeftAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeLeftAction_inclusion (a : M.toStarSubalgebra) (x : E) :
    L a (ι x) = ι (copy a*x) := by
  exact ContinuousLinearMap.extend_eq
    ((ι).toContinuousLinearMap.comp (traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a))
    (e := (ι).toContinuousLinearMap) (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    ((ι).isometry.isUniformInducing) x

@[simp] theorem traceFreeLeftAction_coe (a : M.toStarSubalgebra) (x : E) :
    L a (x : K) = ((copy a*x : E) : K) :=
  traceFreeLeftAction_inclusion hfactor hdiff hfinite hunit a x

@[simp] theorem traceFreeLeftAction_one : L 1 = 1 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [traceFreeLeftAction_coe,map_one,one_mul,one_apply_eq_self]

@[simp] theorem traceFreeLeftAction_mul (a b : M.toStarSubalgebra) :
    L (a*b) = L a*L b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [mul_apply_eq_comp,traceFreeLeftAction_coe,map_mul,mul_assoc]

attribute [local instance] OAI.Generator.Tracial.traceHilbertActionCStar
local instance traceHilbertActionOrder_rd8c884_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertActionStarOrder_rd8c884_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
@[simp] theorem traceFreeLeftAction_add (a b : M.toStarSubalgebra) :
    L (a+b) = L a+L b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [add_apply,traceFreeLeftAction_coe,map_add,add_mul,UniformSpace.Completion.coe_add]

@[simp] theorem traceFreeLeftAction_smul (c : ℂ) (a : M.toStarSubalgebra) :
    L (c • a) = c • L a := by
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (L (c • a)).continuous ((c • L a : K →L[ℂ] K)).continuous) ?_
  intro b
  change L (c • a) (ι b) = c • L a (ι b)
  rw [traceFreeLeftAction_inclusion,traceFreeLeftAction_inclusion,map_smul,smul_mul_assoc]
  exact (ι).map_smul c _

@[simp] theorem traceFreeLeftAction_zero : L 0 = 0 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [traceFreeLeftAction_coe,map_zero,zero_mul,zero_apply,UniformSpace.Completion.coe_zero]

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
local instance traceHilbertRightOperatorCStar_rd8c884_1 : CStarAlgebra (K →L[ℂ] K) := {}
theorem traceFreeCopy_star_norm (x : M.toStarSubalgebra) : ‖copy (star x)‖ = ‖copy x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [traceFreeCopy_norm_sq,traceFreeCopy_norm_sq,star_star,
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2]

local instance traceHilbertRightOrder_rd8c884_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertRightStarOrder_rd8c884_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
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

local instance traceHilbertClosureCStar_rd8c884_1 : CStarAlgebra M.toStarSubalgebra := {}
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

end Generator.Tracial

end

end OAI
end


