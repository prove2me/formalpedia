-- Prove2me | Definitions.Def_OAIQ025S002
-- name    : OAIQ025S002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:44:12.057984+00:00
-- url     : https://prove2.me/theorems/de4a6e0e-cfac-44e1-85b6-ff85c6405013
-- title:
--   Definitions bundle OAIQ025S002 of the split of OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 37 definitions, 4 instances and 19 theorems. The definitions and types are `OAI.Release061.chartDensityMeasure`, `OAI.Release061.chartInverseExtension`, `OAI.Release061.chartLeftDensity`, `OAI.Release061.chartLeftMap`, `OAI.Release061.chartPart`, `OAI.Release061.complexifyRealContinuousEquiv`, `OAI.Release061.complexifyRealEquiv`, `OAI.Release061.complexifyRealLinear`, `OAI.Release061.conjugateMulAction`, `OAI.Release061.differentialSubfield`, `OAI.Release061.etaleDerivationExtension`, `OAI.Release061.fiberPolynomial`, `OAI.Release061.germDirectionalDerivative`, `OAI.Release061.graphOffsetDifferentialEquiv`, `OAI.Release061.halfPlaneShift`, `OAI.Release061.homeomorphOfInverseOn`, `OAI.Release061.independentSupportCoordinates`, `OAI.Release061.inwardDistance`, `OAI.Release061.linePolynomial`, `OAI.Release061.linearConjugateChart`, `OAI.Release061.linearCoordinatePolynomial`, `OAI.Release061.normalRealCovector`, `OAI.Release061.parabolicScale`, `OAI.Release061.parameterPeak`, `OAI.Release061.peakLinear`, `OAI.Release061.quadraticDomain`, `OAI.Release061.quadraticDomainCoordinates`, `OAI.Release061.radialLine`, `OAI.Release061.radialPlane`, `OAI.Release061.realComplexBlock`, `OAI.Release061.realParameter`, `OAI.Release061.real_triangularDifferentialEquiv`, `OAI.Release061.residualQuadraticCoefficients`, `OAI.Release061.supportLinearCoordinates`, `OAI.Release061.transcendenceDifferentialBasis`, `OAI.Release061.triangularDifferentialEquiv`, `OAI.Release061.unitImaginaryHalfPlane`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `SymmetricDomains_AlgebraicBranchRamification`, `SymmetricDomains_AnalyticDirectionalDerivationFun`, `SymmetricDomains_AnalyticImplicitScalar`, `SymmetricDomains_AnalyticZeroNull`, `SymmetricDomains_BoundaryFiberClosureContinuity`, `SymmetricDomains_ChartDensityMeasureLeft`, `SymmetricDomains_ChartDimensionLeCoordinate`, `SymmetricDomains_ChartLeftDensityJacobian`, `SymmetricDomains_ChoosePositiveC1Regularization`, `SymmetricDomains_ComplexifyRealContinuousEquiv`, `SymmetricDomains_ConjugateMulActionCompact`, `SymmetricDomains_DifferentialMemSpanTranscendence`, `SymmetricDomains_DiscRelationCompactLocal`, `SymmetricDomains_EtaleDerivationExtensionUnique`, `SymmetricDomains_FiberPolynomialNatDegree`, `SymmetricDomains_FiniteCoveringRamifiedSection`, `SymmetricDomains_HomeomorphInverse`, `SymmetricDomains_IndependentComplexConormalRows`, `SymmetricDomains_Model`, `SymmetricDomains_ModelChartOpen`, `SymmetricDomains_OffsetDerivative`, `SymmetricDomains_ParameterPeakMaximizer`, `SymmetricDomains_PolynomialRelationDependentPartials`, `SymmetricDomains_PolynomialRemovableLocal`, `SymmetricDomains_QuadraticDomainConnectedComponent`, `SymmetricDomains_RawQuadraticModelNormalization`, `SymmetricDomains_RealPolynomialAnalyticRoot`, `SymmetricDomains_SupportedWeightedLimit`, `SymmetricDomains_WeightedTaylorUniformlyCompact`.
--
--   **Imports.** It imports the published bundle `Def_SymmetricDomains`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ025S003`; the statements `OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric` and `OAI.Release061.original_supported_hermitian_model`; the proofs of `OAI.Release061.NashBoundaryChart.scaling_chart`, `OAI.Release061.NashBoundaryScalingChart.independent_support_rows`, `OAI.Release061.original_small_slope_good_supported_boundary` and `OAI.Release061.prime_boundary_generic_fiber`.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_SymmetricDomains

section
-- module Solutions.OAIQ025_SD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticImplicitScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061


open Set Filter Topology

noncomputable def triangularDifferentialEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E × ℂ →L[ℂ] ℂ) (ha : L (0, 1) ≠ 0) : (E × ℂ) ≃L[ℂ] (E × ℂ) := by
  let A := ContinuousLinearMap.fst ℂ E ℂ
  let B := ContinuousLinearMap.snd ℂ E ℂ
  let C := L.comp ((ContinuousLinearMap.inl ℂ E ℂ).comp A)
  let inv := A.prod ((L (0, 1))⁻¹ • (B - C))
  have hL : ∀ (u : E) (v : ℂ), L (u, v) = L (u, 0) + v * L (0, 1) := by
    intro u v
    have h : (u, v) = (u, 0) + v • (0, (1 : ℂ)) := by simp
    rw [h, map_add, map_smul]
    simp
  refine ContinuousLinearEquiv.equivOfInverse (A.prod L) inv ?_ ?_
  · intro p
    ext
    · rfl
    · change (L (0, 1))⁻¹ * (L (p.1, p.2) - L (p.1, 0)) = p.2
      rw [hL p.1 p.2]
      field_simp [ha]
      ring
  · intro p
    ext
    · rfl
    · change L (p.1, (L (0, 1))⁻¹ * (p.2 - L (p.1, 0))) = p.2
      rw [hL]
      field_simp [ha]
      ring

@[simp] theorem triangularDifferentialEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E × ℂ →L[ℂ] ℂ) (ha : L (0, 1) ≠ 0) (p : E × ℂ) :
    triangularDifferentialEquiv L ha p = (p.1, L p) := rfl

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRemovableLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology


noncomputable def linePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (x v : Fin n → ℂ) :
    Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C
      (fun i => Polynomial.C (x i) + Polynomial.X * Polynomial.C (v i)) P

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiberPolynomialNatDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


noncomputable def fiberPolynomial {X Y : Type*} (π : X → Y)
    (hfin : ∀ y, (π ⁻¹' {y}).Finite) (h : X → ℂ) (y : Y) : Polynomial ℂ := by
  classical
  exact ∏ x ∈ (hfin y).toFinset, (Polynomial.X - C (h x))

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DiscRelationCompactLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

def peakLinear {n : ℕ} (p q : Affine n) : ℂ :=
  ∑ i, (2 : ℂ) * (starRingEnd ℂ (p i) * (q i - p i))

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRelationDependentPartials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Algebra KaehlerDifferential _root_.Module
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin

noncomputable def transcendenceDifferentialBasis
    {R K ι : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    (x : ι → K) (hx : IsTranscendenceBasis R x) : Basis ι K Ω[K⁄R] := by
  let P := MvPolynomial ι R
  let A := Algebra.adjoin R (range x)
  let L := IntermediateField.adjoin R (range x)
  let f : P →ₐ[R] L := (IsScalarTower.toAlgHom R A L).comp hx.1.aevalEquiv.toAlgHom
  let : Algebra P L := f.toRingHom.toAlgebra
  let : Algebra P K := (MvPolynomial.aeval x).toRingHom.toAlgebra
  let : IsScalarTower R P L := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  let : IsScalarTower R P K := IsScalarTower.of_algebraMap_eq fun r =>
    (MvPolynomial.aeval x).commutes r |>.symm
  let : IsScalarTower P L K := IsScalarTower.of_algebraMap_eq fun p => rfl
  let : IsFractionRing P L := IsFractionRing.of_ringEquiv_left
    hx.1.aevalEquiv.toRingEquiv (fun _ => rfl)
  let : Algebra.IsAlgebraic L K := hx.isAlgebraic_field
  let : Algebra.FormallyEtale P L :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors P)
  let : Algebra.FormallyEtale L K := Algebra.FormallyEtale.of_isSeparable L K
  let : Algebra.FormallyEtale P K := Algebra.FormallyEtale.comp P L K
  exact ((KaehlerDifferential.mvPolynomialBasis R ι).baseChange K).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R P K)

@[simp]
theorem transcendenceDifferentialBasis_apply
    {R K ι : Type*} [Field R] [CharZero R] [Field K] [Algebra R K]
    (x : ι → K) (hx : IsTranscendenceBasis R x) (i : ι) :
    transcendenceDifferentialBasis x hx i = D R K (x i) := by
  have hpoly : KaehlerDifferential.mvPolynomialBasis R ι i =
      D R (MvPolynomial ι R) (MvPolynomial.X i) := by
    apply (KaehlerDifferential.mvPolynomialBasis R ι).repr.injective
    simp
  simp only [transcendenceDifferentialBasis,Basis.map_apply,Basis.baseChange_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul,one_smul,hpoly,KaehlerDifferential.map_D]
  change D R K ((MvPolynomial.aeval x) (MvPolynomial.X i)) = _
  simp

end

open Set Algebra KaehlerDifferential _root_.Module

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DifferentialMemSpanTranscendence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Algebra KaehlerDifferential _root_.Module
open scoped TensorProduct

def differentialSubfield {R K : Type*} [Field R] [Field K] [Algebra R K]
    (M : Submodule K Ω[K⁄R]) : IntermediateField R K where
  carrier := {x | D R K x ∈ M}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by intro x y hx hy; simpa only [mem_ofPred_eq, map_add] using M.add_mem hx hy
  mul_mem' := by
    intro x y hx hy
    change D R K (x*y) ∈ M
    rw [Derivation.leibniz]
    exact M.add_mem (M.smul_mem x hy) (M.smul_mem y hx)
  inv_mem' := by
    intro x hx
    change D R K x⁻¹ ∈ M
    rw [Derivation.leibniz_inv]
    exact M.smul_mem _ hx
  algebraMap_mem' := by intro r; simp

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteCoveringRamifiedSection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Function

open Complex
open scoped UpperHalfPlane
open Function.Periodic

noncomputable def halfPlaneShift (a : ℝ) : ℍ ≃ₜ ℍ where
  toFun z := a +ᵥ z
  invFun z := (-a) +ᵥ z
  left_inv z := by simp [← add_vadd]
  right_inv z := by simp [← add_vadd]
  continuous_toFun := (continuous_const.add UpperHalfPlane.continuous_coe).upperHalfPlaneMk _
  continuous_invFun := (continuous_const.add UpperHalfPlane.continuous_coe).upperHalfPlaneMk _

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AlgebraicBranchRamification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Filter Set Complex UpperHalfPlane Function
open scoped Topology

noncomputable def unitImaginaryHalfPlane : ℍ := ⟨Complex.I,by simp⟩

end

open Filter Set Metric Complex
open scoped Topology

noncomputable def realParameter {n : ℕ} (s : Fin n → ℝ) : Fin n → ℂ := fun i => (s i : ℂ)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticDirectionalDerivationFun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def germDirectionalDerivative (v : E) :
    Filter.Germ (𝓝 (0 : E)) ℂ → Filter.Germ (𝓝 (0 : E)) ℂ :=
  Quotient.map' (fun f x => fderiv ℂ f x v) (by
    intro f g h
    exact (h.fderiv (𝕜 := ℂ)).mono fun x hx => congrArg (fun L => L v) hx)

@[simp] theorem germDirectionalDerivative_ofFun (v : E) (f : E → ℂ) :
    germDirectionalDerivative E v (f : Filter.Germ (𝓝 (0 : E)) ℂ) =
      ((fun x => fderiv ℂ f x v) : Filter.Germ (𝓝 (0 : E)) ℂ) := rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChoosePositiveC1Regularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
namespace Release061

def realComplexBlock (k : ℕ) : ((Fin k → ℝ) × (Fin k → ℝ)) ≃L[ℝ] (Fin k → ℂ) where
  toFun p i := (p.1 i : ℂ)+Complex.I*(p.2 i : ℂ)
  invFun z := (fun i => (z i).re,fun i => (z i).im)
  left_inv p := by ext i <;> simp
  right_inv z := by funext i; apply Complex.ext <;> simp
  map_add' p q := by ext i; simp; ring
  map_smul' r p := by ext i; simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

open scoped Topology
open Set Filter Metric

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_WeightedTaylorUniformlyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Metric Asymptotics
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def parabolicScale (u : ℝ) (x : E × F) : E × F := (u • x.1,u^2 • x.2)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticZeroNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialPlane (p : E × ℝ) (q : E × ℝ) : E × ℝ := p + (q.2 • q.1, q.2)

def radialLine (p : E × ℝ) (y : E) : ℝ →ᵃ[ℝ] E × ℝ where
  toFun t := radialPlane p (y,t)
  linear := (LinearMap.id.smulRight y).prod LinearMap.id
  map_vadd' t u := by
    change p + ((u+t) • y,u+t) = (u • y,u)+(p+(t • y,t))
    simp only [add_smul]
    change p + ((u • y,u)+(t • y,t)) = (u • y,u)+(p+(t • y,t))
    abel

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ConjugateMulActionCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set

@[instance_reducible] def conjugateMulAction {G X Y : Type*} [Monoid G] [MulAction G X]
    (e : X ≃ Y) : MulAction G Y where
  smul g y := e (g • e.symm y)
  one_smul y := by
    change e ((1 : G) • e.symm y) = y
    simp
  mul_smul g h y := by
    change e ((g*h) • e.symm y) = e (g • e.symm (e (h • e.symm y)))
    simp [mul_smul]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BoundaryFiberClosureContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology Metric Classical

def inwardDistance {S E : Type*} [NormedAddCommGroup E]
    (A : S → Set E) (s : S) : ℝ :=
  if (A s).Nonempty then min 1 (infDist 0 (A s)) else 1

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HomeomorphInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
namespace Release061
open Set Filter Metric
open scoped Topology

noncomputable def homeomorphOfInverseOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} {T : Set Y} {F : X → Y} {G : Y → X}
    (hF : ContinuousOn F S) (hG : ContinuousOn G T)
    (hFm : MapsTo F S T) (hGm : MapsTo G T S)
    (hleft : ∀ x ∈ S, G (F x) = x) (hright : ∀ y ∈ T, F (G y) = y) : S ≃ₜ T where
  toFun x := ⟨F x,hFm x.property⟩
  invFun y := ⟨G y,hGm y.property⟩
  left_inv x := Subtype.ext (hleft x x.property)
  right_inv y := Subtype.ext (hright y y.property)
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp hF).subtype_mk _
  continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp hG).subtype_mk _

end Release061



end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealPolynomialAnalyticRoot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

noncomputable def real_triangularDifferentialEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E × ℝ →L[ℝ] ℝ) (ha : L (0, 1) ≠ 0) : (E × ℝ) ≃L[ℝ] (E × ℝ) := by
  let A := ContinuousLinearMap.fst ℝ E ℝ
  let B := ContinuousLinearMap.snd ℝ E ℝ
  let C := L.comp ((ContinuousLinearMap.inl ℝ E ℝ).comp A)
  let inv := A.prod ((L (0, 1))⁻¹ • (B - C))
  have hL : ∀ (u : E) (v : ℝ), L (u, v) = L (u, 0) + v * L (0, 1) := by
    intro u v
    have h : (u, v) = (u, 0) + v • (0, (1 : ℝ)) := by simp
    rw [h, map_add, map_smul]
    simp
  refine ContinuousLinearEquiv.equivOfInverse (A.prod L) inv ?_ ?_
  · intro p
    ext
    · rfl
    · change (L (0, 1))⁻¹ * (L (p.1, p.2) - L (p.1, 0)) = p.2
      rw [hL p.1 p.2]
      field_simp [ha]
      ring
  · intro p
    ext
    · rfl
    · change L (p.1, (L (0, 1))⁻¹ * (p.2 - L (p.1, 0))) = p.2
      rw [hL]
      field_simp [ha]
      ring

@[simp] theorem real_triangularDifferentialEquiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E × ℝ →L[ℝ] ℝ) (ha : L (0, 1) ≠ 0) (p : E × ℝ) :
    real_triangularDifferentialEquiv L ha p = (p.1, L p) := rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartLeftDensityJacobian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def chartLeftMap (e : OpenPartialHomeomorph G E) (g : G) (x : E) : E :=
  e (g*e.symm x)

def chartLeftDensity (e : OpenPartialHomeomorph G E) (x : E) : ℝ :=
  |(fderiv ℝ (chartLeftMap e (e.symm x)) (e 1)).det|⁻¹

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartDensityMeasureLeft
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]

def chartInverseExtension (e : OpenPartialHomeomorph G E) : E → G :=
  by classical exact e.target.piecewise e.symm (fun _ => 1)

def chartPart (e : OpenPartialHomeomorph G E) (A : Set G) : Set E :=
  e.target ∩ chartInverseExtension e ⁻¹' A

def chartDensityMeasure (e : OpenPartialHomeomorph G E) (μE : Measure E)
    (ρ : E → ℝ) : Measure G :=
  Measure.map (chartInverseExtension e)
    ((μE.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict e.target)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EtaleDerivationExtensionUnique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Algebra KaehlerDifferential
open scoped TensorProduct

noncomputable def etaleDerivationExtension
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] (d : Derivation R A B) : Derivation R B B :=
  ((LinearMap.liftBaseChange B d.liftKaehlerDifferential).comp
    (tensorKaehlerEquivOfFormallyEtale R A B).symm.toLinearMap).compDer (D R B)

@[simp] theorem etaleDerivationExtension_algebraMap
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] (d : Derivation R A B) (a : A) :
    etaleDerivationExtension R A B d (algebraMap A B a) = d a := by
  change (LinearMap.liftBaseChange B d.liftKaehlerDifferential)
    ((tensorKaehlerEquivOfFormallyEtale R A B).symm (D R B (algebraMap A B a))) = _
  simp only [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul,Derivation.liftKaehlerDifferential_comp_D,one_smul]

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ChartDimensionLeCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Algebra

noncomputable def linearCoordinatePolynomial {m N : ℕ}
    (L : (Fin N → ℂ) →L[ℂ] (Fin m → ℂ)) (i : Fin m) : MvPolynomial (Fin N) ℂ :=
  ∑ j, MvPolynomial.C (L (Pi.single j 1) i) * MvPolynomial.X j

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ComplexifyRealContinuousEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Complex

def complexifyRealLinear {k j : ℕ}
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ)) :
    (Fin k → ℂ) →ₗ[ℂ] (Fin j → ℂ) where
  toFun z := fun i => (L (fun t => (z t).re) i : ℂ)+I*(L (fun t => (z t).im) i : ℂ)
  map_add' z w := by
    funext i
    change (L (fun t => ((z+w) t).re) i : ℂ)+I*(L (fun t => ((z+w) t).im) i : ℂ) = _
    have hr : (fun t => ((z+w) t).re) = (fun t => (z t).re)+(fun t => (w t).re) := rfl
    have hi : (fun t => ((z+w) t).im) = (fun t => (z t).im)+(fun t => (w t).im) := rfl
    rw [hr,hi,map_add,map_add]
    simp only [Pi.add_apply,ofReal_add]
    ring
  map_smul' c z := by
    funext i
    change (L (fun t => ((c • z) t).re) i : ℂ)+I*(L (fun t => ((c • z) t).im) i : ℂ) = _
    have hr : (fun t => ((c • z) t).re) =
        c.re • (fun t => (z t).re)-c.im • (fun t => (z t).im) := rfl
    have hi : (fun t => ((c • z) t).im) =
        c.re • (fun t => (z t).im)+c.im • (fun t => (z t).re) := rfl
    rw [hr,hi,map_sub,map_add,map_smul,map_smul,map_smul,map_smul]
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    apply Complex.ext <;> simp [mul_re,mul_im]

@[simp] lemma complexifyRealLinear_re {k j : ℕ}
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ)) (z : Fin k → ℂ) (i : Fin j) :
    (complexifyRealLinear L z i).re = L (fun t => (z t).re) i := by
  simp [complexifyRealLinear]

@[simp] lemma complexifyRealLinear_im {k j : ℕ}
    (L : (Fin k → ℝ) →ₗ[ℝ] (Fin j → ℝ)) (z : Fin k → ℂ) (i : Fin j) :
    (complexifyRealLinear L z i).im = L (fun t => (z t).im) i := by
  simp [complexifyRealLinear]

def complexifyRealEquiv {k j : ℕ} (e : (Fin k → ℝ) ≃ₗ[ℝ] (Fin j → ℝ)) :
    (Fin k → ℂ) ≃ₗ[ℂ] (Fin j → ℂ) where
  toLinearMap := complexifyRealLinear e.toLinearMap
  invFun := complexifyRealLinear e.symm.toLinearMap
  left_inv z := by
    funext i
    apply Complex.ext <;> simp
  right_inv z := by
    funext i
    apply Complex.ext <;> simp

def complexifyRealContinuousEquiv {k j : ℕ}
    (e : (Fin k → ℝ) ≃L[ℝ] (Fin j → ℝ)) :
    (Fin k → ℂ) ≃L[ℂ] (Fin j → ℂ) :=
  (complexifyRealEquiv e.toLinearEquiv).toContinuousLinearEquiv

@[simp] lemma complexifyRealContinuousEquiv_im {k j : ℕ}
    (e : (Fin k → ℝ) ≃L[ℝ] (Fin j → ℝ)) (z : Fin k → ℂ) (i : Fin j) :
    (complexifyRealContinuousEquiv e z i).im = e (fun t => (z t).im) i := by
  exact complexifyRealLinear_im e.toLinearEquiv.toLinearMap z i

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IndependentComplexConormalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex

def normalRealCovector {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ} :
    (Fin k → ℝ) →ₗ[ℝ] Module.Dual ℝ (E × (Fin k → ℂ)) :=
  -∑ i : Fin k, (LinearMap.proj i).smulRight
    (Complex.imLm.comp ((LinearMap.proj i).comp (LinearMap.snd ℝ E (Fin k → ℂ))))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelChartOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

def supportLinearCoordinates (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) :
    (E × (Fin (k+1) → ℂ)) ≃L[ℂ] (E × (Fin (k+1) → ℂ)) :=
  (ContinuousLinearEquiv.refl ℂ E).prodCongr (complexifyRealContinuousEquiv e)

@[simp] lemma supportLinearCoordinates_fst
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) (x : E × (Fin (k+1) → ℂ)) :
    (supportLinearCoordinates e x).1 = x.1 := rfl

@[simp] lemma supportLinearCoordinates_im
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) (x : E × (Fin (k+1) → ℂ))
    (i : Fin (k+1)) :
    ((supportLinearCoordinates e x).2 i).im = e (fun t => (x.2 t).im) i :=
  complexifyRealContinuousEquiv_im e x.2 i

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def linearConjugateChart (e : E ≃L[ℂ] F) (f : OpenPartialHomeomorph E E) :
    OpenPartialHomeomorph F F :=
  (e.symm.toHomeomorph.toOpenPartialHomeomorph.trans f).trans
    e.toHomeomorph.toOpenPartialHomeomorph

@[simp] lemma linearConjugateChart_source (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) :
    (linearConjugateChart e f).source = e.symm ⁻¹' f.source := by
  simp [linearConjugateChart]

@[simp] lemma linearConjugateChart_target (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) :
    (linearConjugateChart e f).target = e.symm ⁻¹' f.target := by
  simp [linearConjugateChart]

@[simp] lemma linearConjugateChart_apply (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (x : F) :
    linearConjugateChart e f x = e (f (e.symm x)) := rfl

@[simp] lemma linearConjugateChart_symm_apply (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (x : F) :
    (linearConjugateChart e f).symm x = e (f.symm (e.symm x)) := rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OffsetDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
open scoped Classical
variable {E S V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def graphOffsetDifferentialEquiv (L : S →L[ℝ] V) :
    (S × V) ≃L[ℝ] (S × V) := by
  let P := ContinuousLinearMap.fst ℝ S V
  let Q := ContinuousLinearMap.snd ℝ S V
  refine ContinuousLinearEquiv.equivOfInverse (P.prod (Q-L.comp P))
    (P.prod (Q+L.comp P)) ?_ ?_
  · intro p
    apply Prod.ext
    · rfl
    · change p.2-L p.1+L p.1=p.2
      exact sub_add_cancel _ _
  · intro p
    apply Prod.ext
    · rfl
    · change p.2+L p.1-L p.1=p.2
      exact add_sub_cancel_right _ _

@[simp] theorem graphOffsetDifferentialEquiv_apply (L : S →L[ℝ] V) (p : S × V) :
    graphOffsetDifferentialEquiv L p = (p.1,p.2-L p.1) := rfl

end

open Set Filter Topology Metric
open scoped Classical

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ParameterPeakMaximizer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex Filter Metric
open scoped Topology

def parameterPeak {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (p q : Affine n) : ℂ :=
  (MvPolynomial.eval q P / MvPolynomial.eval p P) *
    Complex.exp (peakLinear p q + a (q-p))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_QuadraticDomainConnectedComponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

def quadraticDomain (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ)) :
    Set (E × (Fin k → ℂ)) := {p | (fun i => (p.2 i).im-H p.1 i) ∈ C}

def quadraticDomainCoordinates (H : E → Fin k → ℝ) (hH : Continuous H) :
    (E × (Fin k → ℂ)) ≃ₜ (E × ((Fin k → ℝ) × (Fin k → ℝ))) where
  toFun p := (p.1,(fun i => (p.2 i).re,fun i => (p.2 i).im-H p.1 i))
  invFun p := (p.1,fun i => ((p.2.1 i : ℂ)+I*((p.2.2 i+H p.1 i : ℝ) : ℂ)))
  left_inv p := by
    apply Prod.ext
    · rfl
    funext i
    apply Complex.ext <;> simp
  right_inv p := by
    apply Prod.ext
    · rfl
    apply Prod.ext <;> funext i <;> simp
  continuous_toFun := by
    apply Continuous.prodMk continuous_fst
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      exact Complex.continuous_re.comp ((continuous_apply i).comp continuous_snd)
    · apply continuous_pi
      intro i
      exact (Complex.continuous_im.comp ((continuous_apply i).comp continuous_snd)).sub
        (((continuous_apply i).comp hH).comp continuous_fst)
  continuous_invFun := by
    apply Continuous.prodMk continuous_fst
    apply continuous_pi
    intro i
    exact (Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (continuous_fst.comp continuous_snd))).add
      ((Complex.continuous_ofReal.comp
        (((continuous_apply i).comp (continuous_snd.comp continuous_snd)).add
          (((continuous_apply i).comp hH).comp continuous_fst))).const_mul I)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RawQuadraticModelNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

def residualQuadraticCoefficients {r k l : ℕ}
    (L : (Fin k → ℝ) ≃L[ℝ] (Fin l → ℝ))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Affine r) (Fin l → ℝ)) :
    Fin k → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ := fun i =>
  let P := ((ContinuousLinearMap.proj i).comp (-L.symm.toContinuousLinearMap)).compContinuousMultilinearMap Q
  (ContinuousLinearMap.coeLM ℝ).comp
    ((continuousMultilinearCurryFin1 ℝ (Affine r) ℝ).toLinearEquiv.toLinearMap.comp
      P.curryLeft.toLinearMap)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportedWeightedLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric Complex
open scoped Classical

def independentSupportCoordinates {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β) :
    (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ) := by
  let L := Matrix.mulVecLin (Matrix.of β)
  have hi : Function.Injective L := Matrix.mulVec_injective_iff.mpr
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hβ)))
  exact (LinearEquiv.ofBijective L ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv

end Release061

end

end OAI
end


