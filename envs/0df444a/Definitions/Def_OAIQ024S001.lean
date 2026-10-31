-- Prove2me | Definitions.Def_OAIQ024S001
-- name    : OAIQ024S001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:17:21.058984+00:00
-- url     : https://prove2.me/theorems/6f394c7b-fac5-4e1e-8084-2e5803b5aa3b
-- title:
--   Definitions bundle OAIQ024S001 of the split of OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SKRatio.ratio_cutoff`, carved from OpenAI's openai/math development (OpenAI, *Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 209 declarations of OpenAI's Lean: 106 definitions, 1 inductive type or structure, 22 instances and 80 theorems. The definitions and types are `OAI.SKRatio.Certificate.gaussianNormalizer`, `OAI.SKRatio.Certificate.gaussianWeight`, `OAI.SKRatio.Fields.pairBoltzmannMean`, `OAI.SKRatio.Fields.pairBoltzmannWeight`, `OAI.SKRatio.MatrixNet.bilinearCoefficient`, `OAI.SKRatio.MatrixNet.clippedSquare`, `OAI.SKRatio.Observation.Channel.likelihood`, `OAI.SKRatio.Observation.Channel.normSq`, `OAI.SKRatio.Observation.Channel.reference`, `OAI.SKRatio.Observation.History`, `OAI.SKRatio.Observation.History.likelihood`, `OAI.SKRatio.Observation.History.reference`, `OAI.SKRatio.Observation.Prior`, `OAI.SKRatio.Observation.linear`, `OAI.SKRatio.Observation.logRemainder`, `OAI.SKRatio.Planted.modelField`, `OAI.SKRatio.Planted.normalizingExponent`, `OAI.SKRatio.Planted.rankForm`, `OAI.SKRatio.Scalar.centered`, `OAI.SKRatio.Scalar.densityFactor`, `OAI.SKRatio.Scalar.fieldLaw`, `OAI.SKRatio.Scalar.l2Norm`, `OAI.SKRatio.Scalar.likelihood`, `OAI.SKRatio.Scalar.sd`, `OAI.SKRatio.Scalar.variance`, `OAI.SKRatio.TwoSpin.leadingCoefficient`, `OAI.SKRatio.TwoSpin.pairBaseMass`, `OAI.SKRatio.TwoSpin.pairConditionalMean`, `OAI.SKRatio.TwoSpin.pairDensity`, `OAI.SKRatio.TwoSpin.pairGrad₁`, `OAI.SKRatio.TwoSpin.pairGrad₂`, `OAI.SKRatio.TwoSpin.pairInterMean`, `OAI.SKRatio.TwoSpin.pairMean`, `OAI.SKRatio.TwoSpin.pairPrefactor`, `OAI.SKRatio.TwoSpin.pairResidual`, `OAI.SKRatio.TwoSpin.pairVariance`, `OAI.SKRatio.TwoSpin.polynomialSum`, `OAI.SKRatio.TwoSpin.rationalCoefficient`, `OAI.SKRatio.TwoSpin.remainder`, `OAI.SKRatio.TwoSpin.remainder0` and 67 more.
--
--   **Sources.** They come from these modules of lean/OAI/Probability, in whole or in part: `SKRatio_Calculus_Expectation`, `SKRatio_Calculus_TwoSpin`, `SKRatio_Certificates_CertifiedGaussian`, `SKRatio_Dynamics_GaussMoment`, `SKRatio_Dynamics_LogQuadratic`, `SKRatio_Dynamics_StepMass`, `SKRatio_Dynamics_TestHistogram`, `SKRatio_Entropy_FiniteEntropy`, `SKRatio_Entropy_GaussianChannel`, `SKRatio_Entropy_GaussianHistory`, `SKRatio_FiniteChain_EntropicCovariance`, `SKRatio_Gaussian_EmpiricalIntervals`, `SKRatio_Gaussian_ExponentialEvents`, `SKRatio_Gaussian_Planted`, `SKRatio_Gaussian_PlantedEmpirical`, `SKRatio_Matrices_DiagonalSqrt`, `SKRatio_Matrices_ExpSum`, `SKRatio_Matrices_FiniteMax`, `SKRatio_Matrices_GOERegression`, `SKRatio_Matrices_GaussianCoordinates`, `SKRatio_Matrices_GaussianQuadratic`, `SKRatio_Matrices_GaussianSquareMatrix`, `SKRatio_Matrices_GaussianSquareTails`, `SKRatio_Matrices_GaussianSupport`, `SKRatio_Matrices_MatrixCoordinates`, `SKRatio_Matrices_MatrixQuad`, `SKRatio_Matrices_QuadraticCoeff`, `SKRatio_Matrices_RandomMatrixBounded`, `SKRatio_Matrices_Spin`, `SKRatio_Matrices_StandardGaussianProduct`, `SKRatio_Matrices_UnitBall`, `SKRatio_Quantization_BinProjected`, `SKRatio_Variational_ScalarDensity`, `SKRatio_Variational_ScalarHilbert`, `SKRatio_Variational_ScalarMoments`, `SKRatio_Variational_ScalarMonotone`.
--
--   **Imports.** It imports the published bundle `Def_SKRatio`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ024S002`, `OAIQ024S003`, `OAIQ024S004`, `OAIQ024S008`, `OAIQ024S009` and `OAIQ024S010`; the statements `OAI.SKRatio.Certificate.Data.J0K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J0K2.integral_bound`, `OAI.SKRatio.Certificate.Data.J0K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J1K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J1K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J2K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J2K7.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K4.integral_bound`, `OAI.SKRatio.Certificate.Data.J3K7.integral_bound`, `OAI.SKRatio.Certificate.Data.J4K0.integral_bound`, `OAI.SKRatio.Certificate.Data.J4K7.integral_bound` and `OAI.SKRatio.Planted.residual_norm_rare`.
-- source:
--   OpenAI, Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability at commit adc7f12

import Mathlib
import Definitions.Def_SKRatio

section
-- module Solutions.OAIQ024_SK.Compat
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
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_TwoSpin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace SKRatio.TwoSpin

def polynomialSum (l : List (ℤ × ℕ × ℕ × ℕ)) (a b t : ℝ) : ℝ :=
  (l.map fun c => (c.1 : ℝ)*a^c.2.1*b^c.2.2.1*t^c.2.2.2).sum

def rationalCoefficient (a b t : ℝ) : ℝ :=
  (1-t)/((1+a*t)*(1+b*t)) +
  (t+2*t^2*((a+t)/(1+a*t))*((b+t)/(1+b*t)))*
    ((1-t^2)*(1+a)*(1+b)*(1+t))/((1+a*t)^2*(1+b*t)^2)

def leadingCoefficient (a b t : ℝ) : ℝ :=
  1+a*b*t+(1-a^2-b^2+2*a^2*b^2)*t^2

def remainder0 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-1, 0, 0, 0),
   (-1, 0, 1, 0),
   (2, 0, 2, 0),
   (2, 0, 3, 0),
   (-1, 1, 0, 0),
   (4, 1, 1, 0),
   (2, 1, 2, 0),
   (-3, 1, 3, 0),
   (2, 2, 0, 0),
   (2, 2, 1, 0),
   (-6, 2, 2, 0),
   (-6, 2, 3, 0),
   (2, 3, 0, 0),
   (-3, 3, 1, 0),
   (-6, 3, 2, 0)]

def remainder1 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(1, 0, 0, 1),
   (2, 0, 1, 1),
   (-2, 0, 2, 1),
   (3, 0, 4, 1),
   (2, 1, 0, 1),
   (-7, 1, 1, 1),
   (-2, 1, 2, 1),
   (6, 1, 3, 1),
   (-1, 1, 4, 1),
   (-2, 2, 0, 1),
   (-2, 2, 1, 1),
   (-3, 2, 2, 1),
   (-9, 2, 3, 1),
   (-6, 2, 4, 1),
   (6, 3, 1, 1),
   (-9, 3, 2, 1),
   (-18, 3, 3, 1),
   (3, 4, 0, 1),
   (-1, 4, 1, 1),
   (-6, 4, 2, 1)]

def remainder2 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(2, 0, 0, 2),
   (-1, 0, 1, 2),
   (-3, 0, 2, 2),
   (-1, 0, 3, 2),
   (1, 0, 5, 2),
   (-1, 1, 0, 2),
   (-7, 1, 1, 2),
   (-15, 1, 2, 2),
   (9, 1, 4, 2),
   (-3, 2, 0, 2),
   (-15, 2, 1, 2),
   (-4, 2, 2, 2),
   (7, 2, 3, 2),
   (-3, 2, 4, 2),
   (-2, 2, 5, 2),
   (-1, 3, 0, 2),
   (7, 3, 2, 2),
   (-9, 3, 3, 2),
   (-18, 3, 4, 2),
   (9, 4, 1, 2),
   (-3, 4, 2, 2),
   (-18, 4, 3, 2),
   (1, 5, 0, 2),
   (-2, 5, 2, 2)]

def remainder3 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-2, 0, 0, 3),
   (-4, 0, 1, 3),
   (-2, 0, 2, 3),
   (-4, 1, 0, 3),
   (-7, 1, 1, 3),
   (-3, 1, 2, 3),
   (-3, 1, 3, 3),
   (3, 1, 5, 3),
   (-2, 2, 0, 3),
   (-3, 2, 1, 3),
   (-10, 2, 2, 3),
   (9, 2, 4, 3),
   (-3, 3, 1, 3),
   (5, 3, 3, 3),
   (-3, 3, 4, 3),
   (-6, 3, 5, 3),
   (9, 4, 2, 3),
   (-3, 4, 3, 3),
   (-18, 4, 4, 3),
   (3, 5, 1, 3),
   (-6, 5, 3, 3)]

def remainder4 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-2, 0, 0, 4),
   (-2, 0, 1, 4),
   (-2, 1, 0, 4),
   (-2, 1, 1, 4),
   (-3, 2, 3, 4),
   (3, 2, 5, 4),
   (-3, 3, 2, 4),
   (3, 3, 4, 4),
   (3, 4, 3, 4),
   (-1, 4, 4, 4),
   (-6, 4, 5, 4),
   (3, 5, 2, 4),
   (-6, 5, 4, 4)]

def remainder5 : List (ℤ × ℕ × ℕ × ℕ) :=
  [(-1, 3, 3, 5),
   (1, 3, 5, 5),
   (1, 5, 3, 5),
   (-2, 5, 5, 5)]

def remainder (a b t : ℝ) : ℝ :=
  polynomialSum remainder0 a b t +
  polynomialSum remainder1 a b t +
  polynomialSum remainder2 a b t +
  polynomialSum remainder3 a b t +
  polynomialSum remainder4 a b t +
  polynomialSum remainder5 a b t

def pairBaseMass (a b : ℝ) (x y : Bool) : ℝ :=
  (1+a*spinValue x)*(1+b*spinValue y)/4

def pairMean (a b : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  ∑ x,∑ y,pairBaseMass a b x y*F x y

def pairDensity (a b u : ℝ) (x y : Bool) : ℝ :=
  (1+u*spinValue x*spinValue y)/(1+u*a*b)

def pairInterMean (a b u : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  pairMean a b (fun x y=>pairDensity a b u x y*F x y)

def pairResidual (a u : ℝ) (x y : Bool) : ℝ :=
  (spinValue x-a)*(1-u*spinValue x*spinValue y)/(1+u*a*spinValue y)

def pairVariance (a u : ℝ) (y : Bool) : ℝ :=
  (1-a^2)*(1-u^2)/(1+u*a*spinValue y)^2

def pairGrad₁ (b p r : ℝ) (y : Bool) : ℝ := p+r*(spinValue y-b)

def pairGrad₂ (a s r : ℝ) (x : Bool) : ℝ := s+r*(spinValue x-a)

def pairConditionalMean (a t : ℝ) (y : Bool) : ℝ :=
  (a+t*spinValue y)/(1+t*a*spinValue y)

def signedCoefficient (a b t : ℝ) (x y : Bool) : ℝ :=
  (spinValue x*spinValue y-t)/((1+t*a*spinValue y)*(1+t*b*spinValue x)) +
  (t+2*t^2*pairConditionalMean a t y*pairConditionalMean b t x)*
    ((1-t^2)*(1+a*spinValue x)*(1+b*spinValue y)*(1+t*spinValue x*spinValue y))/
      ((1+t*a*spinValue y)^2*(1+t*b*spinValue x)^2)

def pairPrefactor (a b t : ℝ) : ℝ :=
  (1-a^2)*(1-b^2)*(1-t^2)/(1+t*a*b)

end SKRatio.TwoSpin

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Calculus_Expectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma spinValue_true : spinValue true = 1 := rfl
@[simp] lemma spinValue_false : spinValue false = -1 := rfl
@[simp] lemma spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]

def pairBoltzmannWeight (α γ J : ℝ) (x y : Bool) : ℝ :=
  exp (α*spinValue x+γ*spinValue y+J*spinValue x*spinValue y)
def pairBoltzmannMean (α γ J : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  (∑ x,∑ y,pairBoltzmannWeight α γ J x y*F x y)/(∑ x,∑ y,pairBoltzmannWeight α γ J x y)

end SKRatio.Fields
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_Planted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Filter
namespace SKRatio.Planted
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def normalizingExponent (β : ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (Edge n) : ℝ)*(β^2/n)/2

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_StandardGaussianProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKRatioGaussian

def standardGaussianProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SKRatioGaussian

open Filter
open scoped Topology

end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def variance (β : ℝ) : ℝ≥0 := Real.toNNReal (β^2)

@[simp] lemma variance_coe (β : ℝ) : (variance β : ℝ) = β^2 :=
  Real.coe_toNNReal _ (sq_nonneg β)

def fieldLaw (β : ℝ) : Measure ℝ := gaussianReal (β^2) (variance β)
instance instIsProbabilityMeasureRealFieldLaw (β : ℝ) : IsProbabilityMeasure (fieldLaw β) := by
  unfold fieldLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Certificates_CertifiedGaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open Real Set MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate

def gaussianWeight (x : ℝ) : ℝ := exp (-x^2/2)
def gaussianNormalizer : ℝ := (sqrt (2*Real.pi))⁻¹

end SKRatio.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_GaussMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

noncomputable def gaussMoment (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x^k*Real.exp (-a*x^2)

lemma integrable_gaussMoment {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (gaussMoment a k) := by
  have hk : (-1:ℝ) < (k:ℝ) := by have := (Nat.cast_nonneg k : (0:ℝ)≤k); linarith
  have hh := integrable_rpow_mul_exp_neg_mul_sq ha hk
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  exact (Real.rpow_natCast x k).symm |> congrArg (fun t => t*Real.exp (-a*x^2))

noncomputable def momentEnvelope (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ((k:ℝ)*(|x|+1)^(k-1)+2*a*(|x|+1)^(k+1))*Real.exp a*Real.exp (-(a/2)*x^2)

noncomputable def diffMoment (a : ℝ) (k : ℕ) (h x : ℝ) : ℝ :=
  (gaussMoment a k (x+h)-gaussMoment a k x)/h

noncomputable def momentL1 (a : ℝ) (ha : 0 < a) (k : ℕ) (y : ℝ) : Lp ℝ 1 (volume : Measure ℝ) :=
  Integrable.toL1 (fun x : ℝ => gaussMoment a k (x+y))
    ((integrable_gaussMoment ha k).comp_add_right y)

noncomputable def gaussianTaylor (a c : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, ((-c)^k/(Nat.factorial k : ℝ))*gaussMoment a (2*k) x

end SKRatioClock.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_LogQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SKRatioClock.Clock

noncomputable def logQuadratic : ℝ → ℝ :=
  Function.update (fun x => (Real.log (1+x)-x)/x^2) 0 (-(1/2:ℝ))

noncomputable def poissonMass (m : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-m)*m^k/(k.factorial:ℝ)

noncomputable def centralIndex (q x : ℝ) (M : ℕ) : ℕ :=
  ⌊q*(M:ℝ)+x*Real.sqrt M⌋₊

noncomputable def binomialMass (q : ℝ) (M k : ℕ) : ℝ :=
  (M.choose k:ℝ)*q^k*(1-q)^(M-k)

end SKRatioClock.Clock

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_StepMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

noncomputable def stepMass (p : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' j : ℕ, (Set.Ico (j:ℝ) (j+1)).indicator (fun _ => p j) x

noncomputable def histogram (q : ℝ) (n : ℕ) (p : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt n*stepMass p (q*n+x*Real.sqrt n)

end SKRatioClock.Clock

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Dynamics_TestHistogram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKRatioClock.Clock

noncomputable def testHistogram (q : ℝ) (n : ℕ) (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  stepMass a (q*n+x*Real.sqrt n)

end SKRatioClock.Clock

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_EntropicCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Real
namespace SKRatio.Observation
attribute [local instance] Classical.propDecidable
variable {α : Type*} [Fintype α]

structure Prior (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

instance instCoeFunPriorForallReal : CoeFun (Prior α) (fun _ => α → ℝ) := ⟨Prior.mass⟩

@[ext] lemma Prior.ext {p q : Prior α} (h : p.mass = q.mass) : p = q := by
  cases p; cases q; congr

variable {ι : Type*} [Fintype ι]

def linear (v : α → ι → ℝ) (a : ι → ℝ) (x : α) : ℝ := ∑ i, a i*v x i

end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_FiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open Real
namespace SKRatio.Observation
variable {α : Type*} [Fintype α]

def logRemainder (u a : ℝ) : ℝ := u*log (u/a)-u+a

end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GaussianChannel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation.Channel
variable {α : Type*} [Fintype α] {d : ℕ}

def reference (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance reference_probability (d : ℕ) : IsProbabilityMeasure (reference d) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

variable (v : α → Fin d → ℝ)

def normSq (x : α) : ℝ := ∑ i, v x i^2

def likelihood (t : ℝ) (x : α) (z : Fin d → ℝ) : ℝ :=
  exp (sqrt t*(∑ i, v x i*z i)-t*normSq v x/2)

omit [Fintype α] in
lemma likelihood_pos (t : ℝ) (x : α) (z : Fin d → ℝ) :
    0 < likelihood v t x z := exp_pos _

end SKRatio.Observation.Channel

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Entropy_GaussianHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Real Set Filter
namespace SKRatio.Observation

abbrev History (d : ℕ) : ℕ → Type
  | 0 => Unit
  | k+1 => History d k × (Fin d → ℝ)

namespace History
variable {α : Type*} {d : ℕ}

@[reducible] instance historyMeasurable (d : ℕ) : (k : ℕ) → MeasurableSpace (History d k)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | k+1 => by
    change MeasurableSpace (History d k × (Fin d → ℝ))
    letI := historyMeasurable d k
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

@[reducible] instance historyTopology (d : ℕ) : (k : ℕ) → TopologicalSpace (History d k)
  | 0 => inferInstanceAs (TopologicalSpace Unit)
  | k+1 => by
    change TopologicalSpace (History d k × (Fin d → ℝ))
    letI := historyTopology d k
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance historySecondCountable (d : ℕ) : (k : ℕ) → SecondCountableTopology (History d k)
  | 0 => inferInstanceAs (SecondCountableTopology Unit)
  | k+1 => by
    change SecondCountableTopology (History d k × (Fin d → ℝ))
    let := historySecondCountable d k
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance historyBorel (d : ℕ) : (k : ℕ) → BorelSpace (History d k)
  | 0 => inferInstanceAs (BorelSpace Unit)
  | k+1 => by
    change BorelSpace (History d k × (Fin d → ℝ))
    let := historyBorel d k
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def reference (d : ℕ) : (k : ℕ) → Measure (History d k)
  | 0 => Measure.dirac ()
  | k+1 => (reference d k).prod (Channel.reference d)

instance reference_probability (d : ℕ) : (k : ℕ) → IsProbabilityMeasure (reference d k)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | k+1 => by
    change IsProbabilityMeasure ((reference d k).prod (Channel.reference d))
    let := reference_probability d k
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable (v : α → Fin d → ℝ)

def likelihood (t : ℝ) (x : α) : {k : ℕ} → History d k → ℝ
  | 0, _ => 1
  | _+1, h => likelihood t x h.1 * Channel.likelihood v t x h.2

lemma likelihood_pos (t : ℝ) (x : α) : ∀ {k : ℕ} (h : History d k),
    0 < likelihood v t x h
  | 0, _ => zero_lt_one
  | _+1, h => mul_pos (likelihood_pos t x h.1) (Channel.likelihood_pos v t x h.2)

end History
end SKRatio.Observation

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_ExponentialEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

def ExponentialEmpiricalConcentration {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (ρ : ∀ n, Measure (H n)) (X : ∀ n, H n → Fin n → E) (ν : Measure E) : Prop :=
  ∀ (f : E → ℝ) (K : ℝ≥0), LipschitzWith K f → ∀ B : ℝ,
    (∀ x, |f x| ≤ B) → ∀ ε : ℝ, 0 < ε →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n in atTop,
      ρ n {h | ε ≤ |(∑ i, f (X n h i))/(n:ℝ) - ∫ x, f x ∂ν|} ≤
        ENNReal.ofReal (C * Real.exp (-c*(n:ℝ)))

def ExponentiallyRare {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, Set (H n)) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n in atTop,
    ρ n (A n) ≤ ENNReal.ofReal (C * Real.exp (-c*(n:ℝ)))

def ExponentialConvergence {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) {E : Type*} [PseudoMetricSpace E]
    (X : ∀ n, H n → E) (x : E) : Prop :=
  ∀ ε : ℝ, 0 < ε → ExponentiallyRare ρ (fun n => {h | ε ≤ dist (X n h) x})

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_EmpiricalIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def cdfRamp (a b x : ℝ) : ℝ := max 0 (min 1 ((b-x)/(b-a)))

end SKRatioClock.Regression

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GOERegression
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise

namespace SKRatioClock.Regression

local instance matrixMeasurable {n m : ℕ} : MeasurableSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin n → Fin m → ℝ))

noncomputable def standardArrayLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance instIsProbabilityMeasureForallRealStandardArrayLaw {ι : Type*} [Fintype ι] : IsProbabilityMeasure (standardArrayLaw ι) := by
  unfold standardArrayLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

noncomputable def sandwichCLM {a n b : ℕ}
    (A : Matrix (Fin a) (Fin n) ℝ) (B : Matrix (Fin n) (Fin b) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin a) (Fin b) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun G => A * G * B
    map_add' := by intro G H; simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := by intro c G; simp [Matrix.mul_smul, Matrix.smul_mul] }

@[simp] lemma sandwichCLM_apply {a n b : ℕ}
    (A : Matrix (Fin a) (Fin n) ℝ) (B : Matrix (Fin n) (Fin b) ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) : sandwichCLM A B G = A * G * B := rfl

noncomputable def entryCLM {n m : ℕ} (i : Fin n) (j : Fin m) :
    Matrix (Fin n) (Fin m) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin n → Fin m → ℝ) →L[ℝ] (Fin m → ℝ))

@[simp] lemma entryCLM_apply {n m : ℕ} (i : Fin n) (j : Fin m)
    (G : Matrix (Fin n) (Fin m) ℝ) : entryCLM i j G = G i j := rfl

noncomputable def sharedGaussianField {n : ℕ} (m a b : ℝ)
    (g : Option (Fin n) → ℝ) : Fin n → ℝ := fun i => m + a*g (some i) + b*g none

noncomputable def sharedGaussianFieldCLM (n : ℕ) (a b : ℝ) :
    (Option (Fin n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => a •
    (ContinuousLinearMap.proj (some i) : (Option (Fin n) → ℝ) →L[ℝ] ℝ) +
      b • ContinuousLinearMap.proj none

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianSquareTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

noncomputable def squareTail (R x : ℝ) : ℝ := if R < |x| then x^2 else 0

def ExponentialSquareTails {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (X : ∀ n, H n → Fin n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ExponentiallyRare ρ (fun n => {h | ε ≤ (∑ i, squareTail R (X n h i))/(n:ℝ)})

noncomputable def clippedSquare (R x : ℝ) : ℝ := (min |x| R)^2

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_ExpSum
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKRatioGaussian

instance instIsProbabilityMeasureForallFinRealStandardGaussianProduct_1 (n : ℕ) : IsProbabilityMeasure (standardGaussianProduct n) := by
  unfold standardGaussianProduct
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def expSum (κ : ℝ) (x : ι → ℝ) : ℝ := ∑ i, Real.exp (κ * x i)
def softWeight (κ : ℝ) (x : ι → ℝ) (i : ι) : ℝ := Real.exp (κ * x i) / expSum κ x
def smoothMax (κ : ℝ) (x : ι → ℝ) : ℝ := log (expSum κ x) / κ

variable {ι : Type*} [Fintype ι] [Nonempty ι]

def affineProcess {n : ℕ} (m : ι → ℝ) (a : ι → Fin n → ℝ) (z : Fin n → ℝ) (i : ι) : ℝ :=
  m i + ∑ k, a i k * z k

def interpolatedCoeff {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) : ℝ :=
  sin t * a i k + cos t * b i k

def interpolatedCoeffDeriv {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) (i : ι) (k : Fin n) : ℝ :=
  cos t * a i k - sin t * b i k

def processBound {n : ℕ} (a b : ι → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ k, (|a i k| + |b i k|) * |z k|

def interpolationDerivative {n : ℕ} (κ : ℝ) (m : ι → ℝ) (a b : ι → Fin n → ℝ)
    (t : ℝ) (z : Fin n → ℝ) : ℝ :=
  ∑ i, softWeight κ (affineProcess m (interpolatedCoeff a b t) z) i *
    ∑ k, interpolatedCoeffDeriv a b t i k * z k

end SKRatioGaussian
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_FiniteMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKRatioGaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def finiteMax (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

section CompactIndex
variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

def supProcess {n : ℕ} (m : I → ℝ) (a : I → Fin n → ℝ) (z : Fin n → ℝ) : ℝ :=
  sSup (Set.range (affineProcess m a z))

end CompactIndex
end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianCoordinates
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
namespace SKRatioGaussian
section ArbitraryCoordinates
variable {I κ : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]
  [Fintype κ]

def gaussianCoordinates (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance instIsProbabilityMeasureForallRealGaussianCoordinates : IsProbabilityMeasure (gaussianCoordinates κ) := by
  unfold gaussianCoordinates
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

def gaussianAffine (m : I → ℝ) (a : I → κ → ℝ) (z : κ → ℝ) (i : I) : ℝ :=
  m i + ∑ k, a i k * z k

def gaussianSup (m : I → ℝ) (a : I → κ → ℝ) (z : κ → ℝ) : ℝ :=
  sSup (Set.range (gaussianAffine m a z))

end ArbitraryCoordinates
end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_MatrixCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKRatioGaussian
abbrev MatrixCoordinates (ι : Type*) := (ι × ι) ⊕ ι

variable {ι : Type*}

def goeMatrix (r : ℝ) (g : MatrixCoordinates ι → ℝ) : Matrix ι ι ℝ :=
  fun i k => sqrt (2*r)/2 * (g (.inl (i,k)) + g (.inl (k,i)))

end SKRatioGaussian

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_Spin
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter

namespace SKRatioGaussian

abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Disorder (n : ℕ) := Edge n → ℝ

def coupling {n : ℕ} (g : Disorder n) (i k : Fin n) : ℝ :=
  if h : i < k then g ⟨(i, k), h⟩ else
    if h : k < i then g ⟨(k, i), h⟩ else 0

def disorderLaw (β : ℝ) (n : ℕ) : Measure (Disorder n) :=
  Measure.pi (fun _ : Edge n => gaussianReal 0 (Real.toNNReal (β ^ 2 / n)))

section FiniteSpinCalculus

variable {n : ℕ}

instance disorderLaw_probability (β : ℝ) (n : ℕ) : IsProbabilityMeasure (disorderLaw β n) := by
  unfold disorderLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end FiniteSpinCalculus

end SKRatioGaussian

end

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianSupport
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKRatioGaussian.GaussianRegression

def matrixCLM {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) :
    (κ → ℝ) →L[ℝ] (ι → ℝ) := A.mulVecLin.toContinuousLinearMap

@[simp] lemma matrixCLM_apply {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) (x : κ → ℝ) :
    matrixCLM A x = A *ᵥ x := rfl

end SKRatioGaussian.GaussianRegression
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goeEntryCoeff (r : ℝ) : Matrix (ι × ι) (MatrixCoordinates ι) ℝ :=
  fun p a => sqrt (2*r)/2 * ((if a=Sum.inl p then 1 else 0)+
    (if a=Sum.inl (p.2,p.1) then 1 else 0))

end SKRatioGaussian
end
end

section
noncomputable section
namespace SKRatioGaussian
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators
variable {n : ℕ}

def goeDisorder (r : ℝ) (g : MatrixCoordinates (Fin n)→ℝ) : Disorder n :=
  fun e=>goeMatrix r g e.1.1 e.1.2

end SKRatioGaussian

end
end

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_PlantedEmpirical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression

def modelField (β : ℝ) (n : ℕ) : (Option (Fin n) → ℝ) → Fin n → ℝ :=
  sharedGaussianField (β^2) β (β/sqrt n)

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_QuadraticCoeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace SKRatioGaussian
section GaussianQuadratic
variable {ι : Type*} [Fintype ι]

def quadraticCoeff (r : ℝ) (w : EuclideanSpace ℝ ι) : MatrixCoordinates ι → ℝ
  | Sum.inl (i, k) => Real.sqrt (2 * r) * w i * w k
  | Sum.inr _ => 0

def linearCoeff (r : ℝ) (w : EuclideanSpace ℝ ι) : MatrixCoordinates ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => 2 * Real.sqrt r * ‖w‖ * w i

end GaussianQuadratic
end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_DiagonalSqrt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace SKRatioGaussian
section DiagonalGeometry
variable {ι : Type*} [Fintype ι]

def diagonalSqrt (a : ι → ℝ) (p : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => Real.sqrt (a i) * p i)

end DiagonalGeometry

end SKRatioGaussian

open Real

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianQuadratic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
namespace SKRatioGaussian
open scoped BigOperators

section Quadratic
variable {ι : Type*} [Fintype ι]

def gaussianQuadratic (a : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, a i * (x i)^2

end Quadratic

end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RandomMatrixBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def bilinearCoefficient {n : ℕ} (x y : Fin n → ℝ) (p : Fin n × Fin n) : ℝ :=
  if p.1 < p.2 then x p.1 * y p.2 + x p.2 * y p.1 else 0

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GaussianSquareMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.MatrixNet
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def clippedSquare (R z : ℝ) : ℝ := min (z^2) (R^2)

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_MatrixQuad
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
noncomputable section
open scoped BigOperators Topology
open Filter Real
namespace SKRatioGaussian
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def matrixQuad (M : Matrix ι ι ℝ) (p : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, ∑ k, p i * M i k * p k

def matrixOperator (M : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  M.toEuclideanLin.toContinuousLinearMap

end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_UnitBall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open Real
namespace SKRatioGaussian

section DiagonalProcess
variable {ι : Type*} [Fintype ι]

abbrev UnitBall (ι : Type*) [Fintype ι] :=
  ↥(Metric.closedBall (0 : EuclideanSpace ℝ ι) 1)

instance instNonemptyUnitBall : Nonempty (UnitBall ι) := ⟨⟨0, by simp⟩⟩

def diagonalOffset (a : ι → ℝ) (z q : ℝ) (p : UnitBall ι) : ℝ :=
  -z^2 * q * ‖diagonalSqrt a p‖^2

def diagonalProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ)
    (g : MatrixCoordinates ι → ℝ) : ℝ :=
  gaussianSup (diagonalOffset a z q)
    (fun p k => z * quadraticCoeff r (diagonalSqrt a p) k) g

def diagonalLinearProcess (r : ℝ) (a : ι → ℝ) (z q : ℝ)
    (g : MatrixCoordinates ι → ℝ) : ℝ :=
  gaussianSup (diagonalOffset a z q)
    (fun p k => z * linearCoeff r (diagonalSqrt a p) k) g

def diagonalWeights (r : ℝ) (a : ι → ℝ) : MatrixCoordinates ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => r * a i

def diagonalT (r : ℝ) (a : ι → ℝ) (g : MatrixCoordinates ι → ℝ) : ℝ :=
  sqrt (gaussianQuadratic (diagonalWeights r a) g)

end DiagonalProcess
end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProjected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def rankForm (H v p : Fin n → ℝ) : ℝ :=
  ((∑ i, p i*H i)*(∑ i, p i*v i)+(∑ i, p i)*(∑ i, p i*H i*v i)-
    ((∑ i, H i)/(n:ℝ))*(∑ i, p i)*(∑ i, p i*v i))/(n:ℝ)

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarHilbert
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Real
namespace SKRatio.Scalar

section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def l2Norm (μ : Measure α) (f : α → ℝ) : ℝ := sqrt (∫ x, f x^2 ∂μ)

end Measure

section Probability
variable {μ : Measure ℝ} [IsProbabilityMeasure μ]

def centered (μ : Measure ℝ) (f : ℝ → ℝ) (h : ℝ) : ℝ := f h-(∫ t, f t ∂μ)
def sd (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ := l2Norm μ (centered μ f)

end Probability
end SKRatio.Scalar

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def densityFactor (β z : ℝ) : ℝ := z/β*exp ((z^2-β^2)/2)

end SKRatio.Scalar

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Variational_ScalarMonotone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Real
namespace SKRatio.Scalar

def likelihood (β z h : ℝ) : ℝ :=
  (β/z)*exp ((β^2-z^2)/2+(1/(2*β^2)-1/(2*z^2))*h^2)

end SKRatio.Scalar

end

end OAI
end


