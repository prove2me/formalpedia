-- Prove2me | Definitions.Def_OAIQ254M001
-- name    : OAIQ254M001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:46:38.161201+00:00
-- url     : https://prove2.me/theorems/eb1f191a-107b-4925-a389-621d58cd1507
-- title:
--   Definitions bundle OAIQ254M001 of the split of OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1125 declarations of OpenAI's Lean: 949 definitions, 9 inductive types or structures, 12 instances and 155 theorems. The definitions and types are `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.polynomial`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.GroupAssignment.collect`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryRecovery.sideVariable`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.exponentialCoefficients`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeGroupedRates.boundedComplement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeGroupedRates.boundedComplementEquiv`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeGroupedRates.supportIndexEquiv`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldNativeGroupedRates.supportSubtypeEquiv`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Contractions.coefficientStep`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.Contractions.coefficients`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.multiplicity`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldParameters.statisticComplement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCFinish.SingleWord`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCRegroup.PairedWords`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCRegroup.Positions`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCRegroup.SplitWords`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldStageCRegroup.unpair`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalPopulations.law`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Expression`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Expression.Compiled`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Expression.CompiledFamily`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Expression.compile`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Expression.compileFamily`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Expression.compileFinFamily`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Expression.cost`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Expression.eval`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Gate.mapInput`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Gate.mapRegister`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Gate.mapSource`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.MatrixAlgorithm.pad`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.Substituted`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.Substituted.step`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.append`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.mapInput`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.mapSource`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.newIndex`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.oldIndex`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.registerCost`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.Program.substitute`, `OAI.MatrixAllFields.MatrixMultiplication.Arithmetic.RectangularAdmissibleExponent` and 918 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixFields_Arithmetic_ArithmeticComplexity`, `MatrixFields_Arithmetic_ArithmeticExponent`, `MatrixFields_Arithmetic_ArithmeticPrograms`, `MatrixFields_Arithmetic_CommonDimensions`, `MatrixFields_Arithmetic_ComplexArithmeticGrowth`, `MatrixFields_Arithmetic_ComplexArithmeticLowerBound`, `MatrixFields_Arithmetic_RecursiveBlockPrograms`, `MatrixFields_CapacityA_CapA1_1_14I0`, `MatrixFields_CapacityA_CapA1_2_13I0`, `MatrixFields_CapacityA_CapA1_3_12I0`, `MatrixFields_CapacityA_CapA1_4_11I0`, `MatrixFields_CapacityA_CapA1_5_10I0`, `MatrixFields_CapacityA_CapA1_6_9I0`, `MatrixFields_CapacityA_CapA1_7_8I0`, `MatrixFields_CapacityA_CapA2_2_12I0`, `MatrixFields_CapacityA_CapA2_3_11I0`, `MatrixFields_CapacityA_CapA2_4_10I0`, `MatrixFields_CapacityA_CapA2_5_9I0`, `MatrixFields_CapacityA_CapA2_6_8I0`, `MatrixFields_CapacityA_CapA2_7_7I0`, `MatrixFields_CapacityA_CapA3_3_10I0`, `MatrixFields_CapacityA_CapA3_4_9I0`, `MatrixFields_CapacityA_CapA3_5_8I0`, `MatrixFields_CapacityA_CapA3_6_7I0`, `MatrixFields_CapacityA_CapA4_4_8I0`, `MatrixFields_CapacityA_CapA4_5_7I0`, `MatrixFields_CapacityA_CapA4_6_6I0`, `MatrixFields_CapacityA_CapA5_5_6I0`, `MatrixFields_CapacityB_CapB1_1_6I0`, `MatrixFields_CapacityB_CapB1_1_6I1`, `MatrixFields_CapacityB_CapB1_1_6I2`, `MatrixFields_CapacityB_CapB1_2_5I0`, `MatrixFields_CapacityB_CapB1_2_5I1`, `MatrixFields_CapacityB_CapB1_2_5I2`, `MatrixFields_CapacityB_CapB1_3_4I0`, `MatrixFields_CapacityB_CapB1_3_4I1`, `MatrixFields_CapacityB_CapB1_3_4I2`, `MatrixFields_CapacityB_CapB1_4_3I0`, `MatrixFields_CapacityB_CapB1_4_3I1`, `MatrixFields_CapacityB_CapB1_4_3I2`, `MatrixFields_CapacityB_CapB1_5_2I0`, `MatrixFields_CapacityB_CapB1_5_2I1`, `MatrixFields_CapacityB_CapB1_5_2I2`, `MatrixFields_CapacityB_CapB1_6_1I0`, `MatrixFields_CapacityB_CapB1_6_1I1`, `MatrixFields_CapacityB_CapB1_6_1I2`, `MatrixFields_CapacityB_CapB2_1_5I0`, `MatrixFields_CapacityB_CapB2_1_5I1`, `MatrixFields_CapacityB_CapB2_1_5I2`, `MatrixFields_CapacityB_CapB2_2_4I0`, `MatrixFields_CapacityB_CapB2_2_4I1`, `MatrixFields_CapacityB_CapB2_2_4I2`, `MatrixFields_CapacityB_CapB2_3_3I0`, `MatrixFields_CapacityB_CapB2_3_3I1`, `MatrixFields_CapacityB_CapB2_3_3I2`, `MatrixFields_CapacityB_CapB2_4_2I0`, `MatrixFields_CapacityB_CapB2_4_2I1`, `MatrixFields_CapacityB_CapB2_4_2I2`, `MatrixFields_CapacityB_CapB2_5_1I0`, `MatrixFields_CapacityB_CapB2_5_1I1`, `MatrixFields_CapacityB_CapB2_5_1I2`, `MatrixFields_CapacityB_CapB3_1_4I0`, `MatrixFields_CapacityB_CapB3_1_4I1`, `MatrixFields_CapacityB_CapB3_1_4I2`, `MatrixFields_CapacityB_CapB3_2_3I0`, `MatrixFields_CapacityB_CapB3_2_3I1`, `MatrixFields_CapacityB_CapB3_2_3I2`, `MatrixFields_CapacityB_CapB3_3_2I0`, `MatrixFields_CapacityB_CapB3_3_2I1`, `MatrixFields_CapacityB_CapB3_3_2I2`, `MatrixFields_CapacityB_CapB3_4_1I0`, `MatrixFields_CapacityB_CapB3_4_1I1`, `MatrixFields_CapacityB_CapB3_4_1I2`, `MatrixFields_CapacityB_CapB4_1_3I0`, `MatrixFields_CapacityB_CapB4_1_3I1`, `MatrixFields_CapacityB_CapB4_1_3I2`, `MatrixFields_CapacityB_CapB4_2_2I0`, `MatrixFields_CapacityB_CapB4_2_2I1`, `MatrixFields_CapacityB_CapB4_2_2I2`, `MatrixFields_CapacityB_CapB4_3_1I0`, `MatrixFields_CapacityB_CapB4_3_1I1`, `MatrixFields_CapacityB_CapB4_3_1I2`, `MatrixFields_CapacityB_CapB5_1_2I0`, `MatrixFields_CapacityB_CapB5_1_2I1`, `MatrixFields_CapacityB_CapB5_1_2I2`, `MatrixFields_CapacityB_CapB5_2_1I0`, `MatrixFields_CapacityB_CapB5_2_1I1`, `MatrixFields_CapacityB_CapB5_2_1I2`, `MatrixFields_CapacityB_CapB6_1_1I0`, `MatrixFields_CapacityB_CapB6_1_1I1`, `MatrixFields_CapacityB_CapB6_1_1I2`, `MatrixFields_Certificates_CertificatesReplay`, `MatrixFields_Certificates_SparseContraction`, `MatrixFields_Construction_ExactStatisticWords`, `MatrixFields_Construction_ExpressionFamily`, `MatrixFields_Construction_FiniteCover`, `MatrixFields_Construction_JointCompatibilityCountProducer`, `MatrixFields_Construction_JointCompatibilityIncidence`, `MatrixFields_Construction_JointCompatibilityScaling`, `MatrixFields_Construction_JointLossCounts`, `MatrixFields_Construction_OrderedLimits`, `MatrixFields_Construction_Subdivision`, `MatrixFields_Entropy_FiniteAverage`, `MatrixFields_Entropy_FloorExponentialRates`, `MatrixFields_Entropy_GroupBranchLaws`, `MatrixFields_Entropy_GroupProjectedEntropy`, `MatrixFields_Entropy_JointCompatibilityEntropyBound`, `MatrixFields_Entropy_JointCompatibilityRateLimit`, `MatrixFields_Entropy_JointExtractionRates`, `MatrixFields_Entropy_NativeLaws`, `MatrixFields_Entropy_RectangularGrowth`, `MatrixFields_Entropy_ZeroLeafRates`, `MatrixFields_Extraction_GroupPairWindows`, `MatrixFields_Extraction_JointMaskedSelection`, `MatrixFields_Extraction_JointPairClassWindows`, `MatrixFields_Histories_GroupOrbitCount`, `MatrixFields_Histories_HistoryChildLaws`, `MatrixFields_Histories_HistoryGroupCore`, `MatrixFields_Histories_HistoryRecovery`, `MatrixFields_Histories_HistoryRecoveryBudget`, `MatrixFields_Histories_HistorySourceAssignment`, `MatrixFields_Histories_HistorySums`, `MatrixFields_Histories_InheritedMaskMargins`, `MatrixFields_Histories_InverseLinearRecovery`, `MatrixFields_Parameters_ComplementSums`, `MatrixFields_Parameters_JointPopulationMixedCompatibility`, `MatrixFields_Parameters_ParametersCompatibility`, `MatrixFields_Parameters_ParametersContractions`, `MatrixFields_Parameters_ParametersHalfComplement`, `MatrixFields_Parameters_ParametersWeights`, `MatrixFields_Parameters_TerminalPopulations`, `MatrixFields_Tensors_CWStageCPlacements`, `MatrixFields_Tensors_CWStageCStatistics`, `MatrixFields_Tensors_CWWordDimensionParameters`, `MatrixFields_Tensors_CWZeroGeometry`, `MatrixFields_Tensors_TerminalRelabel`.
--
--   **Imports.** It imports the published bundle `Def_MatrixFields`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ254M002`, `OAIQ254M003`, `OAIQ254M004` and `OAIQ254M005`; the statements `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial_sound` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalized_log_error_48`; the proofs of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.checkPolynomial_sound`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalizedLogBall_sound` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldCertificates.Replay.normalized_log_error_48`.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Mathlib
import Definitions.Def_MatrixFields

section
-- module Solutions.OAIQ254_MF.Compat
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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ArithmeticComplexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Program

variable {F Input : Type*}

@[simp] theorem eval_step_zero [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ [Field F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

def scalarAlgorithm (F : Type*) [Field F] : MatrixAlgorithm F 1 1 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

@[simp] theorem scalarAlgorithm_cost (F : Type*) [Field F] : (scalarAlgorithm F).cost = 1 := rfl

def innerSize (n : ℕ) (k : ℝ) : ℕ := ⌈(n : ℝ) ^ k⌉₊

@[simp] theorem innerSize_zero (n : ℕ) : innerSize n 0 = 1 := by
  simp [innerSize]

@[simp] theorem innerSize_one (n : ℕ) : innerSize n 1 = n := by
  simp [innerSize]

def RectangularAdmissibleExponent (F : Type*) [Field F] (k τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n → ∃ P : MatrixAlgorithm F n (innerSize n k) n,
      P.Correct ∧ (P.cost : ℝ) ≤ C * (n : ℝ) ^ (τ + ε)

def rectangularOmega (F : Type*) [Field F] (k : ℝ) : ℝ :=
  sInf {τ : ℝ | RectangularAdmissibleExponent F k τ}

end MatrixMultiplication.Arithmetic

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ArithmeticPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Gate

variable {Input R S : Type*}

def mapRegister (f : R → S) : Gate F Input R → Gate F Input S
  | .constant z => .constant z
  | .input i => .input i
  | .add i j => .add (f i) (f j)
  | .sub i j => .sub (f i) (f j)
  | .mul i j => .mul (f i) (f j)

theorem eval_mapRegister (g : Gate F Input R) (f : R → S)
    (inputs : Input → F) (registers : S → F) :
    (g.mapRegister f).eval inputs registers = g.eval inputs (fun i => registers (f i)) := by
  cases g <;> rfl

omit [Field F] in
@[simp] theorem cost_mapRegister (g : Gate F Input R) (f : R → S) :
    (g.mapRegister f).cost = g.cost := by
  cases g <;> rfl

end Gate

namespace Program

variable {Input : Type*}

def oldIndex (r s : ℕ) (i : Fin r) : Fin (r + s) := ⟨s + i.val, by omega⟩

def newIndex (r s : ℕ) (i : Fin s) : Fin (r + s) := ⟨i.val, by omega⟩

@[simp] theorem oldIndex_zero (r : ℕ) (i : Fin r) : oldIndex r 0 i = i := by
  apply Fin.ext
  simp [oldIndex]

@[simp] theorem oldIndex_succ (r s : ℕ) (i : Fin r) :
    oldIndex r (s + 1) i = (oldIndex r s i).succ := by
  apply Fin.ext
  simp only [oldIndex, Fin.val_succ]
  omega

@[simp] theorem newIndex_zero (r s : ℕ) : newIndex r (s + 1) 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem newIndex_succ (r s : ℕ) (i : Fin s) :
    newIndex r (s + 1) i.succ = (newIndex r s i).succ := by
  apply Fin.ext
  rfl

def append {r : ℕ} (p : Program F Input r) : {s : ℕ} → Program F Input s → Program F Input (r + s)
  | 0, .nil => p
  | s + 1, .step q g => (p.append q).step (g.mapRegister (newIndex r s))

theorem eval_append_new {r s : ℕ} (p : Program F Input r) (q : Program F Input s)
    (inputs : Input → F) :
    ∀ i : Fin s, (p.append q).eval inputs (newIndex r s i) = q.eval inputs i := by
  induction q with
  | nil => intro i; exact Fin.elim0 i
  | @step s q g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [append, newIndex_zero, eval_step_zero, Gate.eval_mapRegister]
      rw [funext ih]
    · simpa only [append, newIndex_succ, eval_step_succ] using ih j

theorem eval_append_old {r s : ℕ} (p : Program F Input r) (q : Program F Input s)
    (inputs : Input → F) :
    ∀ i : Fin r, (p.append q).eval inputs (oldIndex r s i) = p.eval inputs i := by
  induction q with
  | nil => intro i; simp [append]
  | @step s q g ih =>
    intro i
    simpa only [append, oldIndex_succ, eval_step_succ] using ih i

omit [Field F] in
@[simp] theorem cost_append {r s : ℕ} (p : Program F Input r) (q : Program F Input s) :
    (p.append q).cost = p.cost + q.cost := by
  induction q with
  | nil => simp [append, cost]
  | @step s q g ih => simp [append, ih, Nat.add_assoc]

end Program

inductive Expression (F Input : Type*) where
  | constant : F → Expression F Input
  | input : Input → Expression F Input
  | add : Expression F Input → Expression F Input → Expression F Input
  | sub : Expression F Input → Expression F Input → Expression F Input
  | mul : Expression F Input → Expression F Input → Expression F Input

namespace Expression

variable {Input : Type*}

def eval (inputs : Input → F) : Expression F Input → F
  | .constant z => z
  | .input i => inputs i
  | .add e f => e.eval inputs + f.eval inputs
  | .sub e f => e.eval inputs - f.eval inputs
  | .mul e f => e.eval inputs * f.eval inputs

def cost : Expression F Input → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add e f => e.cost + f.cost + 1
  | .sub e f => e.cost + f.cost + 1
  | .mul e f => e.cost + f.cost + 1

structure Compiled (e : Expression F Input) where
  registers : ℕ
  program : Program F Input registers
  output : Fin registers
  correct : ∀ inputs, program.eval inputs output = e.eval inputs
  cost_eq : program.cost = e.cost

def compile : (e : Expression F Input) → Compiled e
  | .constant z =>
    { registers := 1
      program := Program.nil.step (.constant z)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .input i =>
    { registers := 1
      program := Program.nil.step (.input i)
      output := 0
      correct := fun _ => rfl
      cost_eq := rfl }
  | .add e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.add (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .sub e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.sub (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }
  | .mul e f =>
    let p := compile e
    let q := compile f
    { registers := p.registers + q.registers + 1
      program := (p.program.append q.program).step
        (.mul (Program.oldIndex _ _ p.output) (Program.newIndex _ _ q.output))
      output := 0
      correct := by
        intro inputs
        simp only [Program.eval_step_zero, Gate.eval, Program.eval_append_old,
          Program.eval_append_new, p.correct, q.correct, eval]
      cost_eq := by
        simp only [Program.cost_step, Program.cost_append, Gate.cost, p.cost_eq, q.cost_eq, cost] }

end Expression
end MatrixMultiplication.Arithmetic

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ExpressionFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic.Expression

variable {F : Type*} [Field F]

variable {Input Output : Type*}

structure CompiledFamily [Fintype Output] (expressions : Output → Expression F Input) where
  registers : ℕ
  program : Program F Input registers
  output : Output → Fin registers
  correct : ∀ inputs i, program.eval inputs (output i) = (expressions i).eval inputs
  cost_eq : program.cost = ∑ i, (expressions i).cost

def compileFinFamily : (n : ℕ) → (expressions : Fin n → Expression F Input) →
    CompiledFamily expressions
  | 0, _ =>
    { registers := 0
      program := Program.nil
      output := Fin.elim0
      correct := by
        intro inputs i
        exact Fin.elim0 i
      cost_eq := by simp [Program.cost] }
  | n + 1, expressions =>
    let p := compile (expressions 0)
    let q := compileFinFamily n (fun i => expressions i.succ)
    { registers := p.registers + q.registers
      program := p.program.append q.program
      output := Fin.cases (Program.oldIndex _ _ p.output)
        (fun i => Program.newIndex _ _ (q.output i))
      correct := by
        intro inputs i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Program.eval_append_old p.program q.program inputs p.output).trans
            (p.correct inputs)
        · exact (Program.eval_append_new p.program q.program inputs (q.output j)).trans
            (q.correct inputs j)
      cost_eq := by
        rw [Program.cost_append, p.cost_eq, q.cost_eq, Fin.sum_univ_succ] }

def compileFamily [Fintype Output] (expressions : Output → Expression F Input) :
    CompiledFamily expressions :=
  let e := Fintype.equivFin Output
  let p := compileFinFamily (Fintype.card Output) (fun i => expressions (e.symm i))
  { registers := p.registers
    program := p.program
    output := fun i => p.output (e i)
    correct := by
      intro inputs i
      simpa only [Equiv.symm_apply_apply] using p.correct inputs (e i)
    cost_eq := by
      rw [p.cost_eq]
      exact e.symm.sum_comp (fun i => (expressions i).cost) }

end MatrixMultiplication.Arithmetic.Expression

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ComplexArithmeticLowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Arithmetic

inductive Gate (Input Register : Type*) where
  | constant : ℂ → Gate Input Register
  | input : Input → Gate Input Register
  | add : Register → Register → Gate Input Register
  | sub : Register → Register → Gate Input Register
  | mul : Register → Register → Gate Input Register

namespace Gate

variable {Input Register : Type*}

def eval (inputs : Input → ℂ) (registers : Register → ℂ) : Gate Input Register → ℂ
  | .constant z => z
  | .input i => inputs i
  | .add i j => registers i + registers j
  | .sub i j => registers i - registers j
  | .mul i j => registers i * registers j

def cost : Gate Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

inductive Program (Input : Type*) : ℕ → Type _ where
  | nil : Program Input 0
  | step {r : ℕ} : Program Input r → Gate Input (Fin r) → Program Input (r + 1)

namespace Program

variable {Input : Type*}

def eval : {r : ℕ} → Program Input r → (Input → ℂ) → Fin r → ℂ
  | 0, .nil, _ => Fin.elim0
  | _ + 1, .step p g, inputs =>
    Fin.cases (g.eval inputs (p.eval inputs)) (p.eval inputs)

def cost : {r : ℕ} → Program Input r → ℕ
  | 0, .nil => 0
  | _ + 1, .step p g => p.cost + g.cost

@[simp] theorem eval_step_zero {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) (inputs : Input → ℂ) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program Input r)
    (g : Gate Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

abbrev MatrixInput (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

structure MatrixAlgorithm (n : ℕ) where
  registers : ℕ
  program : Program (MatrixInput n) registers
  output : Fin n → Fin n → Fin registers

namespace MatrixAlgorithm

def cost {n : ℕ} (P : MatrixAlgorithm n) : ℕ := P.program.cost

end MatrixAlgorithm

def scalarAlgorithm : MatrixAlgorithm 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

@[simp] theorem scalarAlgorithm_cost : scalarAlgorithm.cost = 1 := rfl

end Arithmetic

end MatrixMultiplication.Foundation

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_TerminalRelabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

namespace MatrixMultiplication.Foundation






namespace Tensor

variable {K X Y Z U V W : Type*} [CommSemiring K]

def directSumProductEquiv (ι κ X U : Type*) :
    ((ι × κ) × (X × U)) ≃ ((ι × X) × (κ × U)) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def directSumPowerEquiv (ι X : Type*) (n : ℕ) :
    ((Fin n → ι) × (Fin n → X)) ≃ (Fin n → ι × X) where
  toFun x i := (x.1 i, x.2 i)
  invFun x := (fun i => (x i).1, fun i => (x i).2)
  left_inv _ := rfl
  right_inv _ := rfl

section Rectangular

variable {A B C : Type*}

def rectangularSquareX (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((A × B) × (B × C)) × (C × A)) where
  toFun x := (((x.1.1, x.2.2.1), (x.1.2.1, x.2.2.2)), (x.1.2.2, x.2.1))
  invFun x := ((x.1.1.1, x.1.2.1, x.2.1), (x.2.2, x.1.1.2, x.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareY (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((B × C) × (C × A)) × (A × B)) where
  toFun y := (((y.1.2.1, y.2.2.2), (y.1.2.2, y.2.1)), (y.1.1, y.2.2.1))
  invFun y := ((y.2.1, y.1.1.1, y.1.2.1), (y.1.2.2, y.2.2, y.1.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

def rectangularSquareZ (A B C : Type*) :
    ((A × B × C) × (A × B × C)) ≃ (((C × A) × (A × B)) × (B × C)) where
  toFun z := (((z.1.2.2, z.2.1), (z.1.1, z.2.2.1)), (z.1.2.1, z.2.2.2))
  invFun z := ((z.1.2.1, z.2.1, z.1.1.1), (z.1.1.2, z.1.2.2, z.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

end Rectangular

end Tensor
end MatrixMultiplication.Foundation

end




section




noncomputable section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.TerminalRelabel

variable {K I A B C I' A' B' C' : Type*} [CommSemiring K]

def taggedPair (eI : I' ≃ I) (eA : A' ≃ A) (eB : B' ≃ B) :
    I' × (A' × B') → I × (A × B) :=
  fun x => (eI x.1, (eA x.2.1, eB x.2.2))

end MatrixMultiplication.TerminalRelabel

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_RecursiveBlockPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Gate

variable {Input Input' Register : Type*}

def mapInput (f : Input → Input') : Gate F Input Register → Gate F Input' Register
  | .constant z => .constant z
  | .input i => .input (f i)
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapInput (f : Input → Input') (g : Gate F Input Register)
    (inputs : Input' → F) (registers : Register → F) :
    (g.mapInput f).eval inputs registers = g.eval (inputs ∘ f) registers := by
  cases g <;> rfl

omit [Field F] in
@[simp] theorem cost_mapInput (f : Input → Input') (g : Gate F Input Register) :
    (g.mapInput f).cost = g.cost := by
  cases g <;> rfl

def mapSource (f : Input → Input' ⊕ F) : Gate F Input Register → Gate F Input' Register
  | .constant z => .constant z
  | .input i => match f i with
    | .inl j => .input j
    | .inr z => .constant z
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ F) (g : Gate F Input Register)
    (inputs : Input' → F) (registers : Register → F) :
    (g.mapSource f).eval inputs registers =
      g.eval (fun i => Sum.elim inputs id (f i)) registers := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, eval]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

omit [Field F] in
@[simp] theorem cost_mapSource (f : Input → Input' ⊕ F) (g : Gate F Input Register) :
    (g.mapSource f).cost = g.cost := by
  cases g with
  | input i => cases h : f i <;> simp [mapSource, h, cost]
  | constant => rfl
  | add => rfl
  | sub => rfl
  | mul => rfl

end Gate

namespace Program

variable {Input Input' Mid : Type*}

def mapInput (f : Input → Input') : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapInput f).step (g.mapInput f)

@[simp] theorem eval_mapInput (f : Input → Input') {r : ℕ} (p : Program F Input r)
    (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapInput f).eval inputs i = p.eval (inputs ∘ f) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapInput, eval_step_zero, Gate.eval_mapInput]
      rw [funext ih]
    · exact ih j

omit [Field F] in
@[simp] theorem cost_mapInput (f : Input → Input') {r : ℕ} (p : Program F Input r) :
    (p.mapInput f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapInput, cost_step, Gate.cost_mapInput, ih]

def mapSource (f : Input → Input' ⊕ F) : {r : ℕ} → Program F Input r → Program F Input' r
  | 0, .nil => .nil
  | _ + 1, .step p g => (p.mapSource f).step (g.mapSource f)

@[simp] theorem eval_mapSource (f : Input → Input' ⊕ F) {r : ℕ}
    (p : Program F Input r) (inputs : Input' → F) :
    ∀ i : Fin r, (p.mapSource f).eval inputs i =
      p.eval (fun j => Sum.elim inputs id (f j)) i := by
  induction p with
  | nil => intro i; exact Fin.elim0 i
  | @step r p g ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [mapSource, eval_step_zero, Gate.eval_mapSource]
      rw [funext ih]
    · exact ih j

omit [Field F] in
@[simp] theorem cost_mapSource (f : Input → Input' ⊕ F) {r : ℕ}
    (p : Program F Input r) : (p.mapSource f).cost = p.cost := by
  induction p with
  | nil => rfl
  | step p g ih => simp only [mapSource, cost_step, Gate.cost_mapSource, ih]

structure Substituted {r s : ℕ} (p : Program F Input r) (q : Program F Mid s)
    (wires : Mid → Fin r) where
  registers : ℕ
  program : Program F Input registers
  oldOutput : Fin r → Fin registers
  output : Fin s → Fin registers
  correctOld : ∀ inputs i, program.eval inputs (oldOutput i) = p.eval inputs i
  correct : ∀ inputs i, program.eval inputs (output i) =
    q.eval (fun j => p.eval inputs (wires j)) i
  cost_eq : program.cost = p.cost + q.cost

namespace Substituted

def step {r s : ℕ} {p : Program F Input r} {q : Program F Mid s}
    {wires : Mid → Fin r} (a : Substituted p q wires)
    (g : Gate F Mid (Fin s)) (h : Gate F Input (Fin a.registers))
    (heval : ∀ inputs, h.eval inputs (a.program.eval inputs) =
      g.eval (fun j => p.eval inputs (wires j))
        (q.eval (fun j => p.eval inputs (wires j))))
    (hcost : h.cost = g.cost) : Substituted p (q.step g) wires where
  registers := a.registers + 1
  program := a.program.step h
  oldOutput := fun i => (a.oldOutput i).succ
  output := Fin.cases 0 (fun i => (a.output i).succ)
  correctOld := by
    intro inputs i
    exact a.correctOld inputs i
  correct := by
    intro inputs i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact heval inputs
    · exact a.correct inputs j
  cost_eq := by
    simp only [cost_step, a.cost_eq, hcost, Nat.add_assoc]

end Substituted

def substitute {r : ℕ} (p : Program F Input r) :
    {s : ℕ} → (q : Program F Mid s) → (wires : Mid → Fin r) → Substituted p q wires
  | 0, .nil, wires =>
    { registers := r
      program := p
      oldOutput := id
      output := Fin.elim0
      correctOld := fun _ _ => rfl
      correct := fun _ i => Fin.elim0 i
      cost_eq := by simp only [cost, Nat.add_zero] }
  | _ + 1, .step q g, wires =>
    let a := substitute p q wires
    match g with
    | .input j =>
      { registers := a.registers
        program := a.program
        oldOutput := a.oldOutput
        output := Fin.cases (a.oldOutput (wires j)) a.output
        correctOld := a.correctOld
        correct := by
          intro inputs i
          refine Fin.cases ?_ (fun k => ?_) i
          · exact a.correctOld inputs (wires j)
          · exact a.correct inputs k
        cost_eq := by
          simpa only [cost_step, Gate.cost, Nat.add_zero] using a.cost_eq }
    | .constant z =>
      a.step (.constant z) (.constant z) (fun _ => rfl) rfl
    | .add i j =>
      a.step (.add i j) (.add (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .sub i j =>
      a.step (.sub i j) (.sub (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl
    | .mul i j =>
      a.step (.mul i j) (.mul (a.output i) (a.output j))
        (by intro inputs; simp only [Gate.eval, a.correct]) rfl

end Program

end MatrixMultiplication.Arithmetic

end




noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

def zeroPadMatrix {a b : ℕ} (A B : ℕ) (M : Matrix (Fin a) (Fin b) F) :
    Matrix (Fin A) (Fin B) F :=
  fun i j => if hi : i.val < a then
    if hj : j.val < b then M ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
  else 0

@[simp] theorem zeroPadMatrix_castLE {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B)
    (M : Matrix (Fin a) (Fin b) F) (i : Fin a) (j : Fin b) :
    zeroPadMatrix A B M (Fin.castLE ha i) (Fin.castLE hb j) = M i j := by
  simp [zeroPadMatrix, i.is_lt, j.is_lt]

def padSource {a b c A B C : ℕ} : MatrixInput A B C → MatrixInput a b c ⊕ F
  | .inl (i, j) => if hi : i.val < a then
      if hj : j.val < b then .inl (.inl (⟨i.val, hi⟩, ⟨j.val, hj⟩)) else .inr 0
    else .inr 0
  | .inr (j, k) => if hj : j.val < b then
      if hk : k.val < c then .inl (.inr (⟨j.val, hj⟩, ⟨k.val, hk⟩)) else .inr 0
    else .inr 0

namespace MatrixAlgorithm

def pad {a b c A B C : ℕ} (ha : a ≤ A) (_hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) : MatrixAlgorithm F a b c where
  registers := P.registers
  program := P.program.mapSource (padSource (a := a) (b := b) (c := c))
  output := fun i k => P.output (Fin.castLE ha i) (Fin.castLE hc k)

@[simp] theorem pad_cost_eq {a b c A B C : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (P : MatrixAlgorithm F A B C) : (pad ha hb hc P).cost = P.cost :=
  Program.cost_mapSource (padSource (a := a) (b := b) (c := c)) P.program

end MatrixAlgorithm

end MatrixMultiplication.Arithmetic







namespace MatrixMultiplication.Arithmetic.RecursiveBlock

open MatrixMultiplication.Foundation

variable {F : Type*} [Field F]

namespace LinearExpression

variable {Input : Type*}

def sumFin : (n : ℕ) → (Fin n → Expression F Input) → Expression F Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin n (fun i => f i.succ))

def linear {Term : Type*} [Fintype Term] (a : Term → F) (wire : Term → Input) :
    Expression F Input :=
  sumFin (Fintype.card Term) (fun i =>
    .mul (.constant (a ((Fintype.equivFin Term).symm i)))
      (.input (wire ((Fintype.equivFin Term).symm i))))

end LinearExpression

structure Family (F Input Output : Type*) where
  registers : ℕ
  program : Program F Input registers
  output : Output → Fin registers

namespace Family

variable {Input Mid Output : Type*}

def eval (p : Family F Input Output) (inputs : Input → F) (o : Output) : F :=
  p.program.eval inputs (p.output o)

def cost (p : Family F Input Output) : ℕ := p.program.cost

def expressions [Fintype Output] (e : Output → Expression F Input) : Family F Input Output :=
  let p := Expression.compileFamily e
  ⟨p.registers, p.program, p.output⟩

def compose (p : Family F Input Mid) (q : Family F Mid Output) : Family F Input Output :=
  let s := p.program.substitute q.program p.output
  ⟨s.registers, s.program, fun o => s.output (q.output o)⟩

def mapInputs {NewInput : Type*} (f : Input → NewInput) (p : Family F Input Output) :
    Family F NewInput Output :=
  ⟨p.registers, p.program.mapInput f, p.output⟩

def parallel : (r : ℕ) → (Fin r → Family F Input Output) → Family F Input (Fin r × Output)
  | 0, _ => ⟨0, Program.nil, fun o => Fin.elim0 o.1⟩
  | r + 1, p =>
    let head := p 0
    let tail := parallel r (fun i => p i.succ)
    { registers := head.registers + tail.registers
      program := head.program.append tail.program
      output := fun o => Fin.cases
        (Program.oldIndex _ _ (head.output o.2))
        (fun i => Program.newIndex _ _ (tail.output (i, o.2))) o.1 }

def copies (r : ℕ) (p : Family F Input Output) :
    Family F (Fin r × Input) (Fin r × Output) :=
  parallel r (fun i => p.mapInputs (fun x => (i, x)))

def ofMatrix {m l q : ℕ} (p : MatrixAlgorithm F m l q) :
    Family F (MatrixInput m l q) (Fin m × Fin q) :=
  ⟨p.registers, p.program, fun o => p.output o.1 o.2⟩

omit [Field F] in
@[simp] theorem cost_ofMatrix {m l q : ℕ} (p : MatrixAlgorithm F m l q) :
    (ofMatrix p).cost = p.cost := rfl

end Family

section BlockIdentities

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

def join {n m : ℕ} (i : Fin n) (j : Fin m) : Fin (n * m) := finProdFinEquiv (i, j)

def leftBlock (a : Fin r → Fin n₁ × Fin n₂ → F)
    (A : Matrix (Fin (n₁ * m₁)) (Fin (n₂ * m₂)) F) (q : Fin r) :
    Matrix (Fin m₁) (Fin m₂) F :=
  fun s t => ∑ x, a q x * A (join x.1 s) (join x.2 t)

def rightBlock (b : Fin r → Fin n₂ × Fin n₃ → F)
    (B : Matrix (Fin (n₂ * m₂)) (Fin (n₃ * m₃)) F) (q : Fin r) :
    Matrix (Fin m₂) (Fin m₃) F :=
  fun t u => ∑ y, b q y * B (join y.1 t) (join y.2 u)

end BlockIdentities

section BlockPrograms

variable {n₁ n₂ n₃ r m₁ m₂ m₃ : ℕ}

def inputExpressions (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) :
    Fin r × MatrixInput m₁ m₂ m₃ →
      Expression F (MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
  | (q, .inl (s, t)) => LinearExpression.linear (a q)
      (fun x => .inl (join x.1 s, join x.2 t))
  | (q, .inr (t, u)) => LinearExpression.linear (b q)
      (fun y => .inr (join y.1 t, join y.2 u))

def inputFamily (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) :
    Family F (MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
      (Fin r × MatrixInput m₁ m₂ m₃) :=
  Family.expressions (inputExpressions a b)

def recursiveProducts (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (p : MatrixAlgorithm F m₁ m₂ m₃) :
    Family F (MatrixInput (n₁ * m₁) (n₂ * m₂) (n₃ * m₃))
      (Fin r × (Fin m₁ × Fin m₃)) :=
  (inputFamily a b).compose (Family.copies r (Family.ofMatrix p))

def outputExpressions (c : Fin r → Fin n₃ × Fin n₁ → F) :
    Fin (n₁ * m₁) × Fin (n₃ * m₃) → Expression F (Fin r × (Fin m₁ × Fin m₃)) :=
  fun o => LinearExpression.linear
    (fun q => c q ((finProdFinEquiv.symm o.2).1, (finProdFinEquiv.symm o.1).1))
    (fun q => (q, ((finProdFinEquiv.symm o.1).2, (finProdFinEquiv.symm o.2).2)))

def outputFamily (c : Fin r → Fin n₃ × Fin n₁ → F) :
    Family F (Fin r × (Fin m₁ × Fin m₃)) (Fin (n₁ * m₁) × Fin (n₃ * m₃)) :=
  Family.expressions (outputExpressions c)

def algorithm (a : Fin r → Fin n₁ × Fin n₂ → F)
    (b : Fin r → Fin n₂ × Fin n₃ → F) (c : Fin r → Fin n₃ × Fin n₁ → F)
    (p : MatrixAlgorithm F m₁ m₂ m₃) :
    MatrixAlgorithm F (n₁ * m₁) (n₂ * m₂) (n₃ * m₃) :=
  let f := (recursiveProducts a b p).compose (outputFamily c)
  ⟨f.registers, f.program, fun i k => f.output (i, k)⟩

end BlockPrograms

end MatrixMultiplication.Arithmetic.RecursiveBlock

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ArithmeticExponent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic
section

namespace Program

variable {F Input : Type*}

def registerCost : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost p.registerCost

end Program

section ElementaryMatrices

variable {F : Type*} [Field F] {a b c : ℕ}

def elementaryLeft (i : Fin a) (j : Fin b) : Matrix (Fin a) (Fin b) F :=
  fun x y => if x = i then if y = j then 1 else 0 else 0

def elementaryRight (j : Fin b) (k : Fin c) : Matrix (Fin b) (Fin c) F :=
  fun y z => if z = k then if y = j then 1 else 0 else 0

end ElementaryMatrices

end

end MatrixMultiplication.Arithmetic

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_CommonDimensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CommonDimensions

variable {K H : Type*} [CommSemiring K] [Fintype H] [DecidableEq H]

def pairWords (A B : H → Type*) :
    ((∀ h, A h) × (∀ h, B h)) ≃ (∀ h, A h × B h) where
  toFun x h := (x.1 h, x.2 h)
  invFun x := (fun h => (x h).1, fun h => (x h).2)
  left_inv _ := rfl
  right_inv _ := rfl

end MatrixMultiplication.CommonDimensions

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Arithmetic_ComplexArithmeticGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

structure Family (Input Output : Type*) where
  registers : ℕ
  program : Program Input registers
  output : Output → Fin registers

namespace Family

variable {Input Mid Output : Type*}

def cost (p : Family Input Output) : ℕ := p.program.cost

def ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    Family (MatrixInput m) (Fin m × Fin m) :=
  ⟨p.registers, p.program, fun o => p.output o.1 o.2⟩

@[simp] theorem cost_ofMatrix {m : ℕ} (p : MatrixAlgorithm m) :
    (ofMatrix p).cost = p.cost := rfl

end Family

end MatrixMultiplication.Foundation.Arithmetic.RecursiveBlock

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointLossCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.JointLossCounts

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Ω V I : Type*}

variable [DecidableEq V]

def retained (passing : Finset V) (bad : V → Ω → Prop) (ω : Ω) : Finset V :=
  passing.filter (fun v => ¬ bad v ω)

end MatrixMultiplication.JointLossCounts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointExtractionRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.JointExtractionRates

open Filter
open scoped BigOperators Topology

def goodCount {Ω E : Type*} [Fintype E] (good : Ω → E → Prop) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter (good ω)).card

def goodIncidence {Ω E : Type*} [Fintype Ω] (good : Ω → E → Prop) (e : E) : ℕ := by
  classical
  exact (Finset.univ.filter (fun ω => good ω e)).card

end MatrixMultiplication.JointExtractionRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointMaskedSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.JointHashing

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {P R : Type*} [Fintype P] [CommRing R]

def pivot [DecidableEq P] (i : P) (u : Rˣ) (t : R) : P → R :=
  Pi.single i ((↑(u⁻¹) : R) * t)

end MatrixMultiplication.JointHashing





end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ParametersWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

def multiplicity : Fin 6 → ℕ := (Matrix.vecCons (1) (Matrix.vecCons (10) (Matrix.vecCons (25) (Matrix.vecCons (2) (Matrix.vecCons (10) (Matrix.vecCons (1) Matrix.vecEmpty))))))

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_CertificatesReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation.RationalLogCertificate

open scoped BigOperators

noncomputable def sumPower (t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / (i + 1)

noncomputable def realApprox (n : ℕ) (x : ℝ) : ℝ :=
  sumPower ((x - 1) / (x + 1)) n - sumPower (-((x - 1) / (x + 1))) n

end MatrixMultiplication.Foundation.RationalLogCertificate

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldCertificates.Replay

open MatrixMultiplication.Foundation.RationalLogCertificate

noncomputable def polynomial (t : ℝ) : List ℚ → ℝ
  | [] => 0
  | a :: as => (a : ℝ) + t * polynomial t as

end MatrixMultiplication.AllFieldCertificates.Replay

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_JointPairClassWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

def pushforwardCounts {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (b : B) : ℕ := by
  classical
  exact ∑ a, if label a = b then counts a else 0

end MatrixMultiplication.Foundation






namespace MatrixMultiplication.JointPairClassWindows

open MatrixMultiplication.Foundation

attribute [local instance] Classical.propDecidable

variable {I A C : Type*} [Fintype I] [Fintype A] [Fintype C]
  [DecidableEq I] [DecidableEq A] [DecidableEq C]

abbrev Fiber (k : I → C) (c : C) := {i : I // k i = c}

def fiberWord (z : I → A) (k : I → C) (c : C) : Fiber k c → A :=
  fun i => z i.val

def conditionalCenter (f : A → C) (c : C) (q : A → ℝ) (mass : ℝ) : A → ℝ :=
  fun a => if f a = c then q a / mass else 0

end MatrixMultiplication.JointPairClassWindows

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ComplementSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldParameters

theorem list_map_involution_perm {α : Type*} (xs : List α) (f : α → α)
    (hn : xs.Nodup) (hm : ∀ x ∈ xs, f x ∈ xs)
    (hi : ∀ x ∈ xs, f (f x) = x) : (xs.map f).Perm xs := by
  have hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y := by
    intro x hx y hy hxy
    simpa only [hi x hx, hi y hy] using congrArg f hxy
  apply (List.perm_ext_iff_of_nodup (List.Nodup.map_on hinj hn) hn).2
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hm x hx
  · intro hy
    exact List.mem_map.mpr ⟨f y, hm y hy, hi y hy⟩

theorem list_weighted_involution_sum {α : Type*} (xs : List α) (f : α → α)
    (hn : xs.Nodup) (hm : ∀ x ∈ xs, f x ∈ xs)
    (hi : ∀ x ∈ xs, f (f x) = x) (w h : α → ℝ)
    (hw : ∀ x ∈ xs, w (f x) = w x) :
    (xs.map (fun x => w x * h (f x))).sum =
      (xs.map (fun x => w x * h x)).sum := by
  calc
    _ = ((xs.map f).map (fun x => w x * h x)).sum := by
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      simp only [Function.comp_apply, hw x hx]
    _ = _ := ((list_map_involution_perm xs f hn hm hi).map _).sum_eq

end MatrixMultiplication.AllFieldParameters

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ParametersCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

def statisticComplement (k : Fin 5) : Fin 5 := ⟨4 - k.val, by omega⟩

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_FiniteAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def average (f : Ω → ℝ) : ℝ := (∑ ω, f ω) / Fintype.card Ω

theorem average_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    average f = average g := by
  unfold average
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

@[simp] theorem average_const [Nonempty Ω] (c : ℝ) :
    average (fun _ : Ω => c) = c := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [average, hcard]

@[simp] theorem average_zero : average (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [average]

theorem average_add (f g : Ω → ℝ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_sub (f g : Ω → ℝ) :
    average (fun ω => f ω - g ω) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, sub_div]

theorem average_mul_const (f : Ω → ℝ) (c : ℝ) :
    average (fun ω => f ω * c) = average f * c := by
  simp only [average, ← Finset.sum_mul]
  ring

theorem average_const_mul (c : ℝ) (f : Ω → ℝ) :
    average (fun ω => c * f ω) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_finset_sum {I : Type*} (s : Finset I) (f : I → Ω → ℝ) :
    average (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, average (f i) := by
  unfold average
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem average_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω))
    (Nat.cast_nonneg _)

theorem average_indicator_eq (P : Ω → Prop) [DecidablePred P] :
    average (fun ω => if P ω then (1 : ℝ) else 0) =
      ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ) := by
  simp [average]

theorem average_equiv (e : Ω ≃ Γ) (f : Γ → ℝ) :
    average (fun ω => f (e ω)) = average f := by
  unfold average
  rw [Fintype.card_congr e, e.sum_comp]

theorem average_prod (f : Ω → ℝ) (g : Γ → ℝ) :
    average (fun p : Ω × Γ => f p.1 * g p.2) = average f * average g := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  exact mul_div_mul_comm _ _ _ _

theorem average_prod_average (f : Ω × Γ → ℝ) :
    average f = average (fun ω => average (fun γ => f (ω, γ))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

@[simp] theorem average_prod_fst [Nonempty Γ] (f : Ω → ℝ) :
    average (fun p : Ω × Γ => f p.1) = average f := by
  simpa using average_prod f (fun _ : Γ => (1 : ℝ))

@[simp] theorem average_prod_snd [Nonempty Ω] (g : Γ → ℝ) :
    average (fun p : Ω × Γ => g p.2) = average g := by
  simpa using average_prod (fun _ : Ω => (1 : ℝ)) g

theorem average_centered_sq [Nonempty Ω] (f : Ω → ℝ) :
    average (fun ω => (f ω - average f) ^ 2) =
      average (fun ω => f ω ^ 2) - (average f) ^ 2 := by
  calc
    average (fun ω => (f ω - average f) ^ 2) =
        average (fun ω => f ω ^ 2 - (2 * average f) * f ω + (average f) ^ 2) := by
      apply average_congr
      intro ω
      ring
    _ = _ := by rw [average_add, average_sub, average_const_mul, average_const]; ring

section Coordinates

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]

theorem average_pi_eval (i : I) (f : X i → ℝ) :
    average (fun ω : ∀ i, X i => f (ω i)) = average f := by
  classical
  change average (fun ω => (fun p : X i × (∀ j : {j // j ≠ i}, X j) => f p.1)
    ((Equiv.piSplitAt i X) ω)) = average f
  rw [average_equiv (Equiv.piSplitAt i X)
    (fun p : X i × (∀ j : {j // j ≠ i}, X j) => f p.1), average_prod_fst]

theorem average_pi_restrict (D : Finset I) (f : (∀ i : {i // i ∈ D}, X i) → ℝ) :
    average (fun ω : ∀ i, X i => f (fun i => ω i)) = average f := by
  classical
  change average (fun ω =>
    (fun p : (∀ i : {i // i ∈ D}, X i) × (∀ i : {i // i ∉ D}, X i) => f p.1)
      ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ D) X) ω)) = average f
  rw [average_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ D) X)
    (fun p : (∀ i : {i // i ∈ D}, X i) × (∀ i : {i // i ∉ D}, X i) => f p.1),
    average_prod_fst]

theorem average_prod_pi_restrict (D : Finset I)
    (f : ((∀ i : {i // i ∈ D}, X i) × (∀ i : {i // i ∈ D}, X i)) → ℝ) :
    average (fun p : (∀ i, X i) × (∀ i, X i) =>
      f ((fun i => p.1 i), (fun i => p.2 i))) = average f := by
  classical
  rw [average_prod_average]
  calc
    _ = average (fun x : ∀ i, X i =>
        average (fun y : ∀ i : {i // i ∈ D}, X i => f ((fun i => x i), y))) := by
      apply average_congr
      intro x
      exact average_pi_restrict D (fun y => f ((fun i => x i), y))
    _ = average (fun x : ∀ i : {i // i ∈ D}, X i => average (fun y => f (x, y))) :=
      average_pi_restrict D (fun x => average (fun y => f (x, y)))
    _ = average f := (average_prod_average f).symm

theorem average_pi_eval_mul (i j : I) (hij : i ≠ j) (f : X i → ℝ) (g : X j → ℝ) :
    average (fun ω : ∀ i, X i => f (ω i) * g (ω j)) = average f * average g := by
  classical
  change average (fun ω =>
    (fun p : X i × (∀ k : {k // k ≠ i}, X k) =>
      f p.1 * g (p.2 ⟨j, Ne.symm hij⟩)) ((Equiv.piSplitAt i X) ω)) = _
  rw [average_equiv (Equiv.piSplitAt i X)
    (fun p : X i × (∀ k : {k // k ≠ i}, X k) =>
      f p.1 * g (p.2 ⟨j, Ne.symm hij⟩)),
    average_prod f (fun k : ∀ k : {k // k ≠ i}, X k => g (k ⟨j, Ne.symm hij⟩))]
  exact congrArg (fun t => average f * t)
    (average_pi_eval (X := fun k : {k // k ≠ i} => X k) ⟨j, Ne.symm hij⟩ g)

theorem average_pi_sum_centered_sq (f : ∀ i, X i → ℝ) :
    average (fun ω : ∀ i, X i => (∑ i, (f i (ω i) - average (f i))) ^ 2) =
      ∑ i, average (fun x => (f i x - average (f i)) ^ 2) := by
  classical
  let c : ∀ i, X i → ℝ := fun i x => f i x - average (f i)
  have hc (i : I) : average (c i) = 0 := by
    simp [c, average_sub]
  change average (fun ω : ∀ i, X i => (∑ i, c i (ω i)) ^ 2) =
    ∑ i, average (fun x => (c i x) ^ 2)
  calc
    _ = ∑ i, ∑ j, average (fun ω : ∀ i, X i => c i (ω i) * c j (ω j)) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, average_finset_sum]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j, average (fun ω : ∀ i, X i => c i (ω i) * c j (ω j))) =
            average (fun ω : ∀ i, X i => c i (ω i) * c i (ω i)) := by
          apply Finset.sum_eq_single i
          · intro j hj hji
            rw [average_pi_eval_mul i j (Ne.symm hji), hc, hc, zero_mul]
          · simp
        _ = average (fun x => (c i x) ^ 2) := by
          simp only [pow_two]
          exact average_pi_eval i (fun x => c i x * c i x)

end Coordinates

theorem deviation_bound (f : Ω → ℝ) (μ δ : ℝ) (hδ : 0 < δ) :
    average (fun ω => if δ ≤ |f ω - μ| then (1 : ℝ) else 0) * δ ^ 2 ≤
      average (fun ω => (f ω - μ) ^ 2) := by
  rw [← average_mul_const]
  apply average_mono
  intro ω
  split_ifs with h
  · simp only [one_mul]
    have hh := (sq_le_sq₀ (le_of_lt hδ) (abs_nonneg (f ω - μ))).2 h
    simpa only [sq_abs] using hh
  · simp only [zero_mul]
    exact sq_nonneg _

end

end MatrixMultiplication.PermutationMatching

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_FiniteCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

open scoped BigOperators

namespace MatrixMultiplication.FiniteCover

variable {Ω M G : Type*}

theorem exists_avoiding [Fintype Ω] [DecidableEq Ω] [DecidableEq M]
    (s : Finset M) (bad : M → Finset Ω) (t : ℕ)
    (hbad : ∀ m ∈ s, (bad m).card ≤ t)
    (hbudget : s.card * t < Fintype.card Ω) :
    ∃ ω : Ω, ∀ m ∈ s, ω ∉ bad m := by
  classical
  have hcard : (s.biUnion bad).card ≤ s.card * t := by
    calc
      (s.biUnion bad).card ≤ ∑ m ∈ s, (bad m).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ s, t := Finset.sum_le_sum fun m hm => hbad m hm
      _ = s.card * t := by simp
  by_contra hn
  have hsub : (Finset.univ : Finset Ω) ⊆ s.biUnion bad := by
    intro ω hω
    by_contra hout
    apply hn
    refine ⟨ω, ?_⟩
    intro m hm hmem
    exact hout (Finset.mem_biUnion.mpr ⟨m, hm, hmem⟩)
  have := Finset.card_le_card hsub
  simp only [Finset.card_univ] at this
  exact (not_lt_of_ge (this.trans hcard)) hbudget

def avoidingWords [Fintype G] [DecidableEq G] (bad : Finset G) (L : ℕ) :
    Finset (Fin L → G) := Finset.univ.filter fun f => ∀ i, f i ∈ bad

theorem card_avoidingWords [Fintype G] [DecidableEq G] (bad : Finset G) (L : ℕ) :
    (avoidingWords bad L).card = bad.card ^ L := by
  classical
  let e : {f : Fin L → G // f ∈ avoidingWords bad L} ≃ (Fin L → {g // g ∈ bad}) :=
    { toFun := fun f i => ⟨f.1 i, (Finset.mem_filter.mp f.2).2 i⟩
      invFun := fun f => ⟨fun i => (f i).1, by simp [avoidingWords]⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  calc
    (avoidingWords bad L).card = Fintype.card {f : Fin L → G // f ∈ avoidingWords bad L} := by simp
    _ = Fintype.card (Fin L → {g // g ∈ bad}) := Fintype.card_congr e
    _ = bad.card ^ L := by simp

theorem exists_cover [Fintype G] [DecidableEq G] [DecidableEq M]
    (s : Finset M) (good : G → M → Prop) [∀ g, DecidablePred (good g)]
    (t L : ℕ)
    (hbad : ∀ m ∈ s, (Finset.univ.filter fun g => ¬good g m).card ≤ t)
    (hbudget : s.card * t ^ L < Fintype.card G ^ L) :
    ∃ f : Fin L → G, ∀ m ∈ s, ∃ i, good (f i) m := by
  classical
  let bad : M → Finset G := fun m => Finset.univ.filter fun g => ¬good g m
  have hb : ∀ m ∈ s, (avoidingWords (bad m) L).card ≤ t ^ L := by
    intro m hm
    rw [card_avoidingWords]
    exact Nat.pow_le_pow_left (hbad m hm) L
  obtain ⟨f, hf⟩ := exists_avoiding s (fun m => avoidingWords (bad m) L) (t ^ L) hb
    (by simpa using hbudget)
  refine ⟨f, ?_⟩
  intro m hm
  by_contra hn
  apply hf m hm
  simp only [avoidingWords, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun hi => hn ⟨i, hi⟩

end MatrixMultiplication.FiniteCover

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InverseLinearRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.ExactRecovery

variable {K X Y Z I A B C : Type*} [CommSemiring K]

def presence [Fintype I] [DecidableEq I] (p : I → X → Prop)
    [∀ i, DecidablePred (p i)] (x : X) : Finset I :=
  Finset.univ.filter fun i => p i x

@[simp] theorem mem_presence [Fintype I] [DecidableEq I] (p : I → X → Prop)
    [∀ i, DecidablePred (p i)] (x : X) (i : I) :
    i ∈ presence p x ↔ p i x := by simp [presence]

end MatrixMultiplication.ExactRecovery

end




section
open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.OrbitRecovery

variable {G X Y Z : Type*} [Group G] [Fintype G]
    [MulAction G X] [MulAction G Y] [MulAction G Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def badShifts (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (x : X) (y : Y) (z : Z) : Finset G :=
  Finset.univ.filter fun g => ¬(px (g • x) ∧ py (g • y) ∧ pz (g • z))

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem badShifts_card_le (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (x : X) (y : Y) (z : Z) :
    (badShifts (G := G) px py pz x y z).card ≤
      (Finset.univ.filter fun g : G => ¬px (g • x)).card +
      (Finset.univ.filter fun g : G => ¬py (g • y)).card +
      (Finset.univ.filter fun g : G => ¬pz (g • z)).card := by
  classical
  have heq : badShifts (G := G) px py pz x y z =
      (Finset.univ.filter fun g : G => ¬px (g • x)) ∪
      ((Finset.univ.filter fun g : G => ¬py (g • y)) ∪
        (Finset.univ.filter fun g : G => ¬pz (g • z))) := by
    ext g
    by_cases hx : px (g • x) <;> by_cases hy : py (g • y) <;>
      by_cases hz : pz (g • z) <;> simp [badShifts, hx, hy, hz]
  rw [heq]
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add_left (Finset.card_union_le _ _) _).trans (le_of_eq (Nat.add_assoc _ _ _).symm))

theorem floor_loss_fraction (γ : ℝ) (hγ : 0 ≤ γ) :
    (Nat.floor (3 * γ * Fintype.card G) : ℝ) / Fintype.card G ≤ 3 * γ := by
  have hg : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hg).mpr
  exact Nat.floor_le (by positivity)

end MatrixMultiplication.OrbitRecovery

end




section
noncomputable section

namespace MatrixMultiplication.RecoveryGrowth

open Filter
open scoped Topology BigOperators

def shiftCount (b C : ℝ) (N : ℕ) : ℕ :=
  ⌈(b + 1) * (N : ℝ) / Real.log ((N : ℝ) / (3 * C))⌉₊

def replicationCount (b C : ℝ) (N : ℕ) : ℕ :=
  2 ^ (3 * shiftCount b C N)

theorem shiftCount_pos {b C : ℝ} {N : ℕ}
    (hb : 0 ≤ b) (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    0 < shiftCount b C N := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  exact Nat.ceil_pos.2 (div_pos (mul_pos (by linarith) hN0) hlog)

theorem support_loss_bound {b C : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 3 * C < (N : ℝ)) :
    Real.exp (b * N) * (3 * C / (N : ℝ)) ^ shiftCount b C N ≤
      Real.exp (-(N : ℝ)) := by
  have hC3 : 0 < 3 * C := by linarith
  have hN0 : 0 < (N : ℝ) := hC3.trans hN
  have hlog : 0 < Real.log ((N : ℝ) / (3 * C)) :=
    Real.log_pos ((one_lt_div hC3).2 hN)
  have hceil : (b + 1) * (N : ℝ) ≤
      (shiftCount b C N : ℝ) * Real.log ((N : ℝ) / (3 * C)) := by
    exact (div_le_iff₀ hlog).1 (Nat.le_ceil _)
  have hbase : 3 * C / (N : ℝ) =
      Real.exp (-Real.log ((N : ℝ) / (3 * C))) := by
    rw [Real.exp_neg, Real.exp_log (div_pos hN0 hC3)]
    simp
  rw [hbase, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem cardinal_budget {b C : ℝ} {N S t g : ℕ}
    (hC : 0 < C) (hN : 3 * C < (N : ℝ)) (hg : 0 < g)
    (hS : (S : ℝ) ≤ Real.exp (b * N))
    (ht : (t : ℝ) / (g : ℝ) ≤ 3 * C / (N : ℝ)) :
    S * t ^ shiftCount b C N < g ^ shiftCount b C N := by
  have hgr : 0 < (g : ℝ) := by exact_mod_cast hg
  have hN0 : 0 < (N : ℝ) := by linarith
  have hpow := pow_le_pow_left₀
    (div_nonneg (Nat.cast_nonneg t) hgr.le) ht (shiftCount b C N)
  have hprob : (S : ℝ) * ((t : ℝ) / (g : ℝ)) ^ shiftCount b C N < 1 := by
    calc
      (S : ℝ) * ((t : ℝ) / (g : ℝ)) ^ shiftCount b C N ≤
          Real.exp (b * N) * (3 * C / (N : ℝ)) ^ shiftCount b C N :=
        mul_le_mul hS hpow (pow_nonneg (div_nonneg (Nat.cast_nonneg t) hgr.le) _)
          (Real.exp_pos _).le
      _ ≤ Real.exp (-(N : ℝ)) := support_loss_bound hC hN
      _ < 1 := by rw [Real.exp_lt_one_iff]; linarith
  rw [div_pow, ← mul_div_assoc] at hprob
  have hreal := (div_lt_iff₀ (pow_pos hgr (shiftCount b C N))).1 hprob
  simp only [one_mul] at hreal
  exact_mod_cast hreal

end MatrixMultiplication.RecoveryGrowth

end
end




section
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.InverseLinearRecovery

abbrev MaskRectangles (L : ℕ) := Finset (Fin L) × Finset (Fin L) × Finset (Fin L)

end MatrixMultiplication.InverseLinearRecovery

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_InheritedMaskMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.InheritedMasks

open MatrixMultiplication.Foundation
open scoped BigOperators

section ClassWords

variable {C : Type*} (P A : C → Type*)
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

abbrev ClassWords := ∀ c, P c → A c

def SameClassOrbit (w v : ClassWords P A) : Prop :=
  ∃ e : ∀ c, Equiv.Perm (P c), ∀ c, w c ∘ e c = v c

abbrev Profile := ∀ c, A c → Fin (Fintype.card (P c) + 1)

end ClassWords

section Windows

variable {I : Type*} [Fintype I]

theorem weighted_window (w x : I → ℝ) (μ η : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hx : ∀ i, |x i - μ| ≤ η) :
    |(∑ i, w i * x i) - μ| ≤ η := by
  have heq : (∑ i, w i * x i) - μ = ∑ i, w i * (x i - μ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [heq]
  calc
    |∑ i, w i * (x i - μ)| ≤ ∑ i, |w i * (x i - μ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |x i - μ| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * η := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (hw i)
    _ = η := by rw [← Finset.sum_mul, hsum, one_mul]

theorem product_coordinate_error {a b a' b' τ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb' : 0 ≤ b') (hb1' : b' ≤ 1)
    (hea : |a - a'| ≤ τ) (heb : |b - b'| ≤ τ) :
    |a * b - a' * b'| ≤ 2 * τ := by
  have ht : 0 ≤ τ := le_trans (abs_nonneg _) hea
  have heq : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [heq]
  calc
    |a * (b - b') + (a - a') * b'| ≤ |a * (b - b')| + |(a - a') * b'| := abs_add_le _ _
    _ = a * |b - b'| + |a - a'| * b' := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb']
    _ ≤ a * τ + τ * b' := add_le_add
      (mul_le_mul_of_nonneg_left heb ha) (mul_le_mul_of_nonneg_right hea hb')
    _ ≤ 2 * τ := by nlinarith

theorem inherited_margin {actual expected prescribed η τ α : ℝ}
    (hchild : |expected - prescribed| ≤ 2 * τ)
    (happrox : |actual - expected| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    |actual - prescribed| ≤ η / 2 := by
  calc
    |actual - prescribed| = |(actual - expected) + (expected - prescribed)| := by ring_nf
    _ ≤ |actual - expected| + |expected - prescribed| := abs_add_le _ _
    _ ≤ α + 2 * τ := add_le_add happrox hchild
    _ ≤ η / 2 := by linarith

end Windows

end MatrixMultiplication.InheritedMasks

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators

variable {P : Type*} [DecidableEq P]

def membership (B : Finset P) (p : Equiv.Perm P) (i : P) : ℝ :=
  if p i ∈ B then 1 else 0

@[simp] theorem membership_sq (B : Finset P) (p : Equiv.Perm P) (i : P) :
    membership B p i * membership B p i = membership B p i := by
  simp only [membership]
  split_ifs <;> norm_num

variable [Fintype P]

theorem sum_membership (B : Finset P) (p : Equiv.Perm P) :
    (∑ i : P, membership B p i) = (B.card : ℝ) := by
  unfold membership
  rw [Equiv.sum_comp p (fun i => if i ∈ B then (1 : ℝ) else 0)]
  simp

theorem sum_perm_right (f : Equiv.Perm P → ℝ) (q : Equiv.Perm P) :
    (∑ p : Equiv.Perm P, f (p * q)) = ∑ p : Equiv.Perm P, f p := by
  exact Equiv.sum_comp (Equiv.mulRight q) f

theorem sum_membership_position_eq (B : Finset P) (i j : P) :
    (∑ p : Equiv.Perm P, membership B p i) =
      ∑ p : Equiv.Perm P, membership B p j := by
  calc
    _ = ∑ p : Equiv.Perm P, membership B (p * Equiv.swap i j) j := by
      simp [membership, Equiv.Perm.mul_apply]
    _ = _ := sum_perm_right (fun p => membership B p j) _

theorem card_mul_sum_membership (B : Finset P) (i : P) :
    (Fintype.card P : ℝ) * (∑ p : Equiv.Perm P, membership B p i) =
      (Fintype.card (Equiv.Perm P) : ℝ) * B.card := by
  calc
    _ = ∑ j : P, ∑ p : Equiv.Perm P, membership B p i := by simp
    _ = ∑ j : P, ∑ p : Equiv.Perm P, membership B p j := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_membership_position_eq B i j
    _ = ∑ p : Equiv.Perm P, ∑ j : P, membership B p j := Finset.sum_comm
    _ = _ := by simp [sum_membership]

theorem average_membership [Nonempty P] (B : Finset P) (i : P) :
    average (fun p : Equiv.Perm P => membership B p i) =
      (B.card : ℝ) / Fintype.card P := by
  have hn : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card (Equiv.Perm P) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold average
  apply (div_eq_div_iff hp hn).2
  simpa only [mul_comm] using card_mul_sum_membership B i

theorem sum_membership_mul_position_eq (B : Finset P) {i j k : P}
    (hij : i ≠ j) (hik : i ≠ k) :
    (∑ p : Equiv.Perm P, membership B p i * membership B p j) =
      ∑ p : Equiv.Perm P, membership B p i * membership B p k := by
  calc
    _ = ∑ p : Equiv.Perm P,
        membership B (p * Equiv.swap j k) i *
          membership B (p * Equiv.swap j k) k := by
      simp [membership, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hij hik]
    _ = _ := sum_perm_right (fun p => membership B p i * membership B p k) _

theorem card_sub_one_mul_sum_membership_mul (B : Finset P) {i j : P}
    (hij : i ≠ j) :
    ((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j) =
      ((B.card : ℝ) - 1) * (∑ p : Equiv.Perm P, membership B p i) := by
  have hcard : (((Finset.univ : Finset P).erase i).card : ℝ) =
      (Fintype.card P : ℝ) - 1 := by
    have h := congrArg (fun n : ℕ => (n : ℝ))
      (Finset.card_erase_add_one (Finset.mem_univ i))
    simp only [Nat.cast_add, Nat.cast_one, Finset.card_univ] at h
    linarith
  have herase :
      (∑ k ∈ (Finset.univ : Finset P).erase i,
        ∑ p : Equiv.Perm P, membership B p i * membership B p k) =
      ((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j) := by
    calc
      _ = ∑ k ∈ (Finset.univ : Finset P).erase i,
          ∑ p : Equiv.Perm P, membership B p i * membership B p j := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_membership_mul_position_eq B (Finset.mem_erase.mp hk).1.symm hij
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  have htotal :
      (∑ k : P, ∑ p : Equiv.Perm P, membership B p i * membership B p k) =
      (B.card : ℝ) * (∑ p : Equiv.Perm P, membership B p i) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_membership]
    rw [← Finset.sum_mul, mul_comm]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset P)
    (fun k => ∑ p : Equiv.Perm P, membership B p i * membership B p k)
    (Finset.mem_univ i)
  rw [herase, htotal] at hsplit
  simp only [membership_sq] at hsplit
  nlinarith only [hsplit]

theorem average_membership_mul_of_ne (B : Finset P) {i j : P} (hij : i ≠ j) :
    average (fun p : Equiv.Perm P => membership B p i * membership B p j) =
      (B.card : ℝ) * ((B.card : ℝ) - 1) /
        ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1)) := by
  have hnlarge : 1 < Fintype.card P := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
  have hnlarge' : (1 : ℝ) < Fintype.card P := by exact_mod_cast hnlarge
  have hn : (Fintype.card P : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card P : ℝ) - 1 ≠ 0 := by linarith
  have hp : (Fintype.card (Equiv.Perm P) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold average
  apply (div_eq_div_iff hp (mul_ne_zero hn hn1)).2
  calc
    _ = (Fintype.card P : ℝ) * (((Fintype.card P : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i * membership B p j)) := by ring
    _ = (Fintype.card P : ℝ) * (((B.card : ℝ) - 1) *
        (∑ p : Equiv.Perm P, membership B p i)) := by
      rw [card_sub_one_mul_sum_membership_mul B hij]
    _ = ((B.card : ℝ) - 1) * ((Fintype.card P : ℝ) *
        (∑ p : Equiv.Perm P, membership B p i)) := by ring
    _ = ((B.card : ℝ) - 1) * ((Fintype.card (Equiv.Perm P) : ℝ) * B.card) := by
      rw [card_mul_sum_membership B i]
    _ = _ := by ring

end MatrixMultiplication.PermutationMatching

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators

variable {P : Type*} [Fintype P] [DecidableEq P]

def matchingCount (A B : Finset P) (p : Equiv.Perm P) : ℝ :=
  ∑ i ∈ A, membership B p i

theorem average_matchingCount [Nonempty P] (A B : Finset P) :
    average (matchingCount A B) =
      (A.card : ℝ) * (B.card : ℝ) / (Fintype.card P : ℝ) := by
  unfold matchingCount
  rw [average_finset_sum]
  simp only [average_membership, Finset.sum_const, nsmul_eq_mul]
  ring

theorem average_matchingCount_sq [Nonempty P] (A B : Finset P) :
    average (fun p => matchingCount A B p ^ 2) =
      (A.card : ℝ) * (B.card : ℝ) / (Fintype.card P : ℝ) +
      (A.card : ℝ) * ((A.card : ℝ) - 1) * (B.card : ℝ) *
        ((B.card : ℝ) - 1) /
        ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1)) := by
  let u : ℝ := (B.card : ℝ) / (Fintype.card P : ℝ)
  let v : ℝ := (B.card : ℝ) * ((B.card : ℝ) - 1) /
    ((Fintype.card P : ℝ) * ((Fintype.card P : ℝ) - 1))
  have hpair (i j : P) :
      average (fun p => membership B p i * membership B p j) =
        v + if i = j then u - v else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [membership_sq]
      rw [average_membership]
      dsimp [u]
      ring
    · rw [average_membership_mul_of_ne B hij]
      simp [hij, v]
  have hsq (p : Equiv.Perm P) : matchingCount A B p ^ 2 =
      ∑ i ∈ A, ∑ j ∈ A, membership B p i * membership B p j := by
    unfold matchingCount
    rw [pow_two, Finset.sum_mul_sum]
  simp_rw [hsq]
  rw [average_finset_sum]
  simp_rw [average_finset_sum, hpair]
  have hinner (i : P) (hi : i ∈ A) :
      (∑ j ∈ A, (v + (if i = j then u - v else 0))) =
        (A.card : ℝ) * v + (u - v) := by
    rw [Finset.sum_add_distrib]
    simp [hi]
  rw [Finset.sum_congr rfl hinner]
  simp only [Finset.sum_const, nsmul_eq_mul]
  dsimp [u, v]
  ring

theorem matchingCount_variance [Nonempty P] (A B : Finset P)
    (hn : 2 ≤ Fintype.card P) :
    average (fun p => (matchingCount A B p - average (matchingCount A B)) ^ 2) =
      (A.card : ℝ) * ((Fintype.card P : ℝ) - (A.card : ℝ)) *
        (B.card : ℝ) * ((Fintype.card P : ℝ) - (B.card : ℝ)) /
        ((Fintype.card P : ℝ) ^ 2 * ((Fintype.card P : ℝ) - 1)) := by
  rw [average_centered_sq, average_matchingCount_sq, average_matchingCount]
  have hn' : (2 : ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have hn0 : (Fintype.card P : ℝ) ≠ 0 := by linarith
  have hn1 : (Fintype.card P : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hn0, hn1]
  ring

theorem matchingCount_variance_le (A B : Finset P)
    (hn : 2 ≤ Fintype.card P) :
    average (fun p => (matchingCount A B p - average (matchingCount A B)) ^ 2) ≤
      (Fintype.card P : ℝ) / 8 := by
  have : Nonempty P := Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) hn)
  rw [matchingCount_variance A B hn]
  have hn' : (2 : ℝ) ≤ Fintype.card P := by exact_mod_cast hn
  have ha : (A.card : ℝ) ≤ (Fintype.card P : ℝ) := by
    exact_mod_cast Finset.card_le_univ A
  have hb : (B.card : ℝ) ≤ (Fintype.card P : ℝ) := by
    exact_mod_cast Finset.card_le_univ B
  have ha0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hna : 0 ≤ (A.card : ℝ) * ((Fintype.card P : ℝ) - A.card) :=
    mul_nonneg ha0 (sub_nonneg.mpr ha)
  have hnb : 0 ≤ (B.card : ℝ) * ((Fintype.card P : ℝ) - B.card) :=
    mul_nonneg hb0 (sub_nonneg.mpr hb)
  have hqa : (A.card : ℝ) * ((Fintype.card P : ℝ) - A.card) ≤
      (Fintype.card P : ℝ) ^ 2 / 4 := by
    nlinarith only [sq_nonneg ((A.card : ℝ) - (Fintype.card P : ℝ) / 2)]
  have hqb : (B.card : ℝ) * ((Fintype.card P : ℝ) - B.card) ≤
      (Fintype.card P : ℝ) ^ 2 / 4 := by
    nlinarith only [sq_nonneg ((B.card : ℝ) - (Fintype.card P : ℝ) / 2)]
  have hprod := mul_le_mul hqa hqb hnb (by positivity :
    (0 : ℝ) ≤ (Fintype.card P : ℝ) ^ 2 / 4)
  have hn3 : 0 ≤ (Fintype.card P : ℝ) ^ 3 * ((Fintype.card P : ℝ) - 2) :=
    mul_nonneg (by positivity) (by linarith)
  have hn1pos : (0 : ℝ) < (Fintype.card P : ℝ) - 1 := by linarith
  have hnpos : (0 : ℝ) < Fintype.card P := by linarith
  apply (div_le_iff₀ (show (0 : ℝ) <
    (Fintype.card P : ℝ) ^ 2 * ((Fintype.card P : ℝ) - 1) by positivity)).mpr
  nlinarith only [hprod, hn3]

noncomputable def statisticPositions {A B : Type*} (w : P → A)
    (statistic : A → B) (b : B) : Finset P := by
  classical
  exact Finset.univ.filter fun i => statistic (w i) = b

end MatrixMultiplication.PermutationMatching

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

variable {P : Type*} [Fintype P] [DecidableEq P]

def twoHalfCount (A B : Finset P) (left right : Equiv.Perm P) : ℝ :=
  ∑ i : P, if left i ∈ A ∧ right i ∈ B then 1 else 0

theorem twoHalfCount_eq_matchingCount (A B : Finset P)
    (left right : Equiv.Perm P) :
    twoHalfCount A B left right =
      matchingCount A B (left.symm.trans right) := by
  classical
  unfold twoHalfCount matchingCount membership
  calc
    _ = ∑ i : P, if i ∈ A ∧ right (left.symm i) ∈ B then (1 : ℝ) else 0 := by
      simpa only [Equiv.symm_apply_apply] using
        Equiv.sum_comp left (fun i =>
          if i ∈ A ∧ right (left.symm i) ∈ B then (1 : ℝ) else 0)
    _ = ∑ i : P, if i ∈ A then
        (if right (left.symm i) ∈ B then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
    _ = _ := by
      simp only [Equiv.trans_apply, Finset.sum_ite_mem_eq]
      rfl

theorem twoHalfCount_statisticPositions {X Y S T : Type*}
    (leftWord : P → X) (rightWord : P → Y) (sl : X → S) (sr : Y → T)
    (s : S) (t : T) (left right : Equiv.Perm P) :
    twoHalfCount (statisticPositions leftWord sl s)
        (statisticPositions rightWord sr t) left right =
      ∑ i : P, if sl (leftWord (left i)) = s ∧ sr (rightWord (right i)) = t
        then (1 : ℝ) else 0 := by
  classical
  simp [twoHalfCount, statisticPositions]

section Families

variable {C : Type*} (Q : C → Type*)

def relativeFamily
    (left right : ∀ c, Equiv.Perm (Q c)) : ∀ c, Equiv.Perm (Q c) :=
  fun c => (left c).symm.trans (right c)

def relativeFamilyPairEquiv :
    ((∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c))) ≃
      ((∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c))) where
  toFun lr := (lr.1, relativeFamily Q lr.1 lr.2)
  invFun lq := (lq.1, fun c => (lq.1 c).trans (lq.2 c))
  left_inv := by
    rintro ⟨left, right⟩
    dsimp only
    apply Prod.ext
    · rfl
    · funext c
      ext i
      simp [relativeFamily]
  right_inv := by
    rintro ⟨left, relative⟩
    dsimp only
    apply Prod.ext
    · rfl
    · funext c
      ext i
      simp [relativeFamily]

variable [Fintype C] [DecidableEq C]
  [∀ c, Fintype (Q c)] [∀ c, DecidableEq (Q c)]

theorem average_relativeFamily (f : (∀ c, Equiv.Perm (Q c)) → ℝ) :
    average (fun lr :
        (∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c)) =>
      f (relativeFamily Q lr.1 lr.2)) = average f := by
  calc
    _ = average (fun lq :
        (∀ c, Equiv.Perm (Q c)) × (∀ c, Equiv.Perm (Q c)) => f lq.2) :=
      average_equiv (relativeFamilyPairEquiv Q) (fun lq => f lq.2)
    _ = _ := average_prod_snd f

omit [DecidableEq C] in
theorem sum_twoHalfCount_eq_matchingCount
    (A B : ∀ c, Finset (Q c)) (left right : ∀ c, Equiv.Perm (Q c)) :
    (∑ c, twoHalfCount (A c) (B c) (left c) (right c)) =
      ∑ c, matchingCount (A c) (B c) (relativeFamily Q left right c) := by
  simp only [twoHalfCount_eq_matchingCount, relativeFamily]

end Families

end MatrixMultiplication.PermutationMatching

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

section ClassProducts

variable {C : Type*} [Fintype C] [DecidableEq C] {P : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

abbrev ClassPermutations (P : C → Type*) := ∀ c, Equiv.Perm (P c)

def populationSize (P : C → Type*) [∀ c, Fintype (P c)] : ℝ :=
  ∑ c, (Fintype.card (P c) : ℝ)

def totalMatchingCount (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P) : ℝ :=
  ∑ c, matchingCount (A c) (B c) (p c)

def totalMatchingMean (A B : ∀ c, Finset (P c)) : ℝ :=
  ∑ c, average (matchingCount (A c) (B c))

omit [DecidableEq C] in
theorem totalMatchingMean_eq [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) :
    totalMatchingMean A B =
      ∑ c, ((A c).card : ℝ) * ((B c).card : ℝ) / (Fintype.card (P c) : ℝ) := by
  classical
  unfold totalMatchingMean
  apply Finset.sum_congr rfl
  intro c _
  exact average_matchingCount (A c) (B c)

theorem totalMatchingCount_variance_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) :
    average (fun p : ClassPermutations P =>
      (totalMatchingCount A B p - totalMatchingMean A B) ^ 2) ≤
        populationSize P / 8 := by
  classical
  calc
    _ = ∑ c, average (fun p : Equiv.Perm (P c) =>
        (matchingCount (A c) (B c) p - average (matchingCount (A c) (B c))) ^ 2) := by
      simpa only [totalMatchingCount, totalMatchingMean, Finset.sum_sub_distrib]
        using average_pi_sum_centered_sq (fun c => matchingCount (A c) (B c))
    _ ≤ ∑ c, (Fintype.card (P c) : ℝ) / 8 :=
      Finset.sum_le_sum fun c _ => matchingCount_variance_le (A c) (B c) (hn c)
    _ = populationSize P / 8 := by rw [← Finset.sum_div]; rfl

theorem totalMatchingCount_deviation_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c)) (δ : ℝ) (hδ : 0 < δ) :
    average (fun p : ClassPermutations P =>
      if δ ≤ |totalMatchingCount A B p - totalMatchingMean A B| then 1 else 0) ≤
        populationSize P / (8 * δ ^ 2) := by
  classical
  have h := (deviation_bound (totalMatchingCount A B) (totalMatchingMean A B) δ hδ).trans
    (totalMatchingCount_variance_le A B hn)
  calc
    _ ≤ (populationSize P / 8) / δ ^ 2 := (le_div_iff₀ (sq_pos_of_pos hδ)).2 h
    _ = _ := by rw [div_div]

theorem normalizedMatchingCount_deviation_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η : ℝ) (hη : 0 < η) :
    average (fun p : ClassPermutations P =>
      if η / 2 ≤ |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  have hδ : 0 < populationSize P * η / 2 := by positivity
  calc
    _ ≤ average (fun p : ClassPermutations P =>
        if populationSize P * η / 2 ≤
          |totalMatchingCount A B p - totalMatchingMean A B| then 1 else 0) := by
      apply average_mono
      intro p
      have hi : η / 2 ≤ |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| →
          populationSize P * η / 2 ≤
            |totalMatchingCount A B p - totalMatchingMean A B| := by
        intro hp
        rw [← sub_div, abs_div, abs_of_pos hm] at hp
        have hh := (le_div_iff₀ hm).mp hp
        nlinarith
      split_ifs <;> simp_all
    _ ≤ populationSize P / (8 * (populationSize P * η / 2) ^ 2) :=
      totalMatchingCount_deviation_le A B hn _ hδ
    _ = _ := by
      field_simp [ne_of_gt hm, ne_of_gt hη]
      ring

theorem inheritedMask_rejection_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean A B / populationSize P - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P =>
      if η < |totalMatchingCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  refine le_trans (average_mono ?_) (normalizedMatchingCount_deviation_le A B hn hm η hη)
  intro p
  have hi : η < |totalMatchingCount A B p / populationSize P - ν| →
      η / 2 ≤ |totalMatchingCount A B p / populationSize P -
        totalMatchingMean A B / populationSize P| := by
    intro hp
    have ht : |totalMatchingCount A B p / populationSize P - ν| ≤
        |totalMatchingCount A B p / populationSize P -
          totalMatchingMean A B / populationSize P| +
        |totalMatchingMean A B / populationSize P - ν| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (totalMatchingCount A B p / populationSize P - totalMatchingMean A B / populationSize P)
        (totalMatchingMean A B / populationSize P - ν)
    linarith
  split_ifs <;> simp_all

def totalTwoHalfCount (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P × ClassPermutations P) : ℝ :=
  ∑ c, twoHalfCount (A c) (B c) (p.1 c) (p.2 c)

theorem average_totalTwoHalfCount_test (A B : ∀ c, Finset (P c)) (f : ℝ → ℝ) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      f (totalTwoHalfCount A B p)) =
        average (fun p : ClassPermutations P => f (totalMatchingCount A B p)) := by
  calc
    _ = average (fun p : ClassPermutations P × ClassPermutations P =>
        f (totalMatchingCount A B (relativeFamily P p.1 p.2))) := by
      apply average_congr
      intro p
      exact congrArg f (sum_twoHalfCount_eq_matchingCount P A B p.1 p.2)
    _ = _ := average_relativeFamily P (fun p => f (totalMatchingCount A B p))

theorem twoHalf_inheritedMask_rejection_le (A B : ∀ c, Finset (P c))
    (hn : ∀ c, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize P) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean A B / populationSize P - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount A B p / populationSize P - ν| then 1 else 0) ≤
        1 / (2 * populationSize P * η ^ 2) := by
  classical
  rw [average_totalTwoHalfCount_test A B
    (fun k => if η < |k / populationSize P - ν| then 1 else 0)]
  exact inheritedMask_rejection_le A B hn hm η ν hη hmargin

def selectedTwoHalfCount (D : Finset C) (A B : ∀ c, Finset (P c))
    (p : ClassPermutations P × ClassPermutations P) : ℝ :=
  totalTwoHalfCount (fun c : D => A c) (fun c : D => B c)
    ((fun c => p.1 c), (fun c => p.2 c))

theorem selectedTwoHalfMask_rejection_le (D : Finset C) (A B : ∀ c, Finset (P c))
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c)) (η ν : ℝ) (hη : 0 < η)
    (hmargin : |totalMatchingMean (fun c : D => A c) (fun c : D => B c) /
      populationSize (fun c : D => P c) - ν| ≤ η / 2) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |selectedTwoHalfCount D A B p / populationSize (fun c : D => P c) - ν|
        then 1 else 0) ≤ 1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  classical
  have havg := average_prod_pi_restrict (X := fun c => Equiv.Perm (P c)) D
    (fun p : ClassPermutations (fun c : D => P c) ×
        ClassPermutations (fun c : D => P c) =>
      if η < |totalTwoHalfCount (fun c : D => A c) (fun c : D => B c) p /
        populationSize (fun c : D => P c) - ν| then (1 : ℝ) else 0)
  change average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |totalTwoHalfCount (fun c : D => A c) (fun c : D => B c)
        ((fun c => p.1 c), (fun c => p.2 c)) /
        populationSize (fun c : D => P c) - ν| then 1 else 0) ≤ _
  rw [havg]
  exact twoHalf_inheritedMask_rejection_le (P := fun c : D => P c)
    (fun c : D => A c) (fun c : D => B c)
    (fun c : D => hn c c.property) hm η ν hη hmargin

theorem inverse_linear_mask_constant {I : Type*} [Fintype I]
    (mass η : I → ℝ) (N : ℝ) :
    (∑ i, 1 / (2 * (mass i * N) * (η i) ^ 2)) =
      (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_div]
  congr 1
  ring

end ClassProducts

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open MatrixMultiplication.InheritedMasks
open Classical

noncomputable section

section ClassMixtures

variable {C : Type*} [Fintype C] [DecidableEq C] {P : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]

def classWeight (P : C → Type*) [∀ c, Fintype (P c)] (c : C) : ℝ :=
  (Fintype.card (P c) : ℝ) / populationSize P

def classDensity (A : ∀ c, Finset (P c)) (c : C) : ℝ :=
  ((A c).card : ℝ) / Fintype.card (P c)

def classProductMixture (P : C → Type*) [∀ c, Fintype (P c)]
    (left right : C → ℝ) : ℝ :=
  ∑ c, classWeight P c * (left c * right c)

omit [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classWeight_nonneg (hm : 0 < populationSize P) (c : C) :
    0 ≤ classWeight P c := div_nonneg (Nat.cast_nonneg _) (le_of_lt hm)

omit [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem sum_classWeight (hm : 0 < populationSize P) :
    ∑ c, classWeight P c = 1 := by
  unfold classWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hm)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_nonneg (A : ∀ c, Finset (P c)) (c : C) :
    0 ≤ classDensity A c := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (P c)] in
theorem classDensity_le_one [∀ c, Nonempty (P c)]
    (A : ∀ c, Finset (P c)) (c : C) : classDensity A c ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card (P c) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hn).2
  simpa using (Nat.cast_le.mpr (Finset.card_le_univ (A c)) :
    ((A c).card : ℝ) ≤ Fintype.card (P c))

omit [DecidableEq C] in
theorem totalMatchingMean_normalized_eq [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P) :
    totalMatchingMean A B / populationSize P =
      classProductMixture P (classDensity A) (classDensity B) := by
  classical
  rw [totalMatchingMean_eq, Finset.sum_div]
  unfold classProductMixture
  apply Finset.sum_congr rfl
  intro c _
  have hn : (Fintype.card (P c) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := P c)))
  dsimp [classWeight, classDensity]
  field_simp [hn, ne_of_gt hm]

omit [DecidableEq C] in
theorem totalMatchingMean_prescribed_error [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P)
    (left right : C → ℝ) (τ : ℝ)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ) :
    |totalMatchingMean A B / populationSize P -
      classProductMixture P left right| ≤ 2 * τ := by
  rw [totalMatchingMean_normalized_eq A B hm]
  have h := weighted_window (classWeight P)
    (fun c => classDensity A c * classDensity B c - left c * right c)
    0 (2 * τ) (classWeight_nonneg hm) (sum_classWeight hm) (by
      intro c
      simpa only [sub_zero] using product_coordinate_error
        (classDensity_nonneg A c) (classDensity_le_one A c)
        (hright0 c) (hright1 c) (hleft c) (hright c))
  simpa only [classProductMixture, sub_zero, mul_sub, Finset.sum_sub_distrib] using h

omit [DecidableEq C] in
theorem totalMatchingMean_inherited_margin [∀ c, Nonempty (P c)]
    (A B : ∀ c, Finset (P c)) (hm : 0 < populationSize P)
    (left right : C → ℝ) (η τ α ν : ℝ)
    (hright0 : ∀ c, 0 ≤ right c) (hright1 : ∀ c, right c ≤ 1)
    (hleft : ∀ c, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture P left right - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    |totalMatchingMean A B / populationSize P - ν| ≤ η / 2 := by
  have hchild := totalMatchingMean_prescribed_error A B hm left right τ
    hright0 hright1 hleft hright
  have h := inherited_margin (actual := ν)
    (expected := classProductMixture P left right)
    (prescribed := totalMatchingMean A B / populationSize P)
    (by simpa only [abs_sub_comm] using hchild)
    (by simpa only [abs_sub_comm] using happrox) hτ hα
  simpa only [abs_sub_comm] using h

theorem selectedTwoHalfMask_rejection_of_windows_le
    (D : Finset C) (A B : ∀ c, Finset (P c))
    (hn : ∀ c ∈ D, 2 ≤ Fintype.card (P c))
    (hm : 0 < populationSize (fun c : D => P c))
    (left right : C → ℝ) (η τ α ν : ℝ) (hη : 0 < η)
    (hright0 : ∀ c ∈ D, 0 ≤ right c) (hright1 : ∀ c ∈ D, right c ≤ 1)
    (hleft : ∀ c ∈ D, |classDensity A c - left c| ≤ τ)
    (hright : ∀ c ∈ D, |classDensity B c - right c| ≤ τ)
    (happrox : |classProductMixture (fun c : D => P c)
      (fun c => left c) (fun c => right c) - ν| ≤ α)
    (hτ : τ ≤ η / 8) (hα : α ≤ η / 4) :
    average (fun p : ClassPermutations P × ClassPermutations P =>
      if η < |selectedTwoHalfCount D A B p /
        populationSize (fun c : D => P c) - ν| then 1 else 0) ≤
      1 / (2 * populationSize (fun c : D => P c) * η ^ 2) := by
  let : ∀ c : D, Nonempty (P c) := fun c =>
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by decide : 0 < 2) (hn c c.property))
  apply selectedTwoHalfMask_rejection_le D A B hn hm η ν hη
  exact totalMatchingMean_inherited_margin (fun c : D => A c) (fun c : D => B c)
    hm (fun c => left c) (fun c => right c) η τ α ν
    (fun c => hright0 c c.property) (fun c => hright1 c c.property)
    (fun c => hleft c c.property) (fun c => hright c c.property) happrox hτ hα

end ClassMixtures

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_ExactStatisticWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section





noncomputable section

namespace MatrixMultiplication.ExactStatisticWords

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {A U : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]

omit [Fintype A] [DecidableEq U] in
theorem card_fixedWeight_fiber (statistic : U → A) (weight : U → ℕ)
    (statisticWeight : A → ℕ) (hweight : ∀ u, weight u = statisticWeight (statistic u))
    (a : ℕ) (s : A) (hs : statisticWeight s = a) :
    Fintype.card {u : {u : U // weight u = a} // statistic u.val = s} =
      Fintype.card {u : U // statistic u = s} := by
  apply Fintype.card_congr
  exact
    { toFun := fun u => ⟨u.val.val, u.property⟩
      invFun := fun u => ⟨⟨u.val, by rw [hweight, u.property, hs]⟩, u.property⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }

end MatrixMultiplication.ExactStatisticWords

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryChildLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.Staggering

theorem physical_order_unique (rho sigma : Equiv.Perm (Fin 3)) :
    ∃! phi : Equiv.Perm (Fin 3), rho.trans phi = sigma := by
  refine ⟨rho.symm.trans sigma, ?_, ?_⟩
  · ext i
    simp
  · intro phi hphi
    apply Equiv.ext
    intro i
    have h := Equiv.congr_fun hphi (rho.symm i)
    simpa using h

end MatrixMultiplication.Staggering

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.FiniteSchedule

open Staggering

def stageActive (K tick : ℕ) (stage : Fin 3) : Prop :=
  stage.val ≤ tick ∧ tick < K + stage.val

instance instDecidableStageActive (K tick : ℕ) (stage : Fin 3) : Decidable (stageActive K tick stage) :=
  inferInstanceAs (Decidable (stage.val ≤ tick ∧ tick < K + stage.val))

end MatrixMultiplication.FiniteSchedule

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_RectangularGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

def rectangularBlockCost (a b R K : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => R * rectangularBlockCost a b R K t + K * ((a * b) ^ t + (a ^ 2) ^ t)

@[simp] theorem rectangularBlockCost_zero (a b R K : ℕ) :
    rectangularBlockCost a b R K 0 = 1 := rfl

@[simp] theorem rectangularBlockCost_succ (a b R K t : ℕ) :
    rectangularBlockCost a b R K (t + 1) =
      R * rectangularBlockCost a b R K t + K * ((a * b) ^ t + (a ^ 2) ^ t) := rfl

end MatrixMultiplication.Arithmetic

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStageCPlacements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.CWStageC

open MatrixMultiplication.Foundation

def interior (i : Fin 5) : Fin 7 := ⟨i.val + 1, by have := i.isLt; omega⟩

theorem interior_injective : Function.Injective interior := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa only [interior, Nat.add_right_cancel_iff] using hval

end MatrixMultiplication.CWStageC

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

def SmallRow : Fin 4 → Type := (Matrix.vecCons (Unit) (Matrix.vecCons (Unit) (Matrix.vecCons (Fin 5) (Matrix.vecCons (Fin 5) Matrix.vecEmpty))))

def SmallInner : Fin 4 → Type := (Matrix.vecCons (Fin 5) (Matrix.vecCons (Fin 5) (Matrix.vecCons (Unit) (Matrix.vecCons (Unit) Matrix.vecEmpty))))

def Row (s : Fin 3) (b : Fin 4) : Type :=
  if s = 1 then SmallInner b else SmallRow b

def Middle (s : Fin 3) (b : Fin 4) : Type :=
  if s = 2 then SmallInner b else SmallRow b

def Column (s : Fin 3) (b : Fin 4) : Type :=
  if s = 0 then SmallInner b else SmallRow b

abbrev Word := Fin 2 → Fin 7

def shape (s : Fin 3) : Fin 3 → ℕ := fun i => if i = s then 2 else 1

def canonicalAtom : Fin 4 → (Fin 3 → ℕ) :=
  (Matrix.vecCons ((Matrix.vecCons (1) (Matrix.vecCons (1) (Matrix.vecCons (0) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (0) (Matrix.vecCons (0) (Matrix.vecCons (2) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (1) (Matrix.vecCons (0) (Matrix.vecCons (1) Matrix.vecEmpty)))) (Matrix.vecCons ((Matrix.vecCons (0) (Matrix.vecCons (1) (Matrix.vecCons (1) Matrix.vecEmpty)))) Matrix.vecEmpty))))

def branchAtom (s : Fin 3) (b : Fin 4) : Fin 3 → ℕ :=
  if s = 0 then (Matrix.vecCons (canonicalAtom b 2) (Matrix.vecCons (canonicalAtom b 1) (Matrix.vecCons (canonicalAtom b 0) Matrix.vecEmpty)))
  else if s = 1 then (Matrix.vecCons (canonicalAtom b 0) (Matrix.vecCons (canonicalAtom b 2) (Matrix.vecCons (canonicalAtom b 1) Matrix.vecEmpty)))
  else canonicalAtom b

abbrev Positions (counts : Fin 4 → ℕ) := Σ b : Fin 4, Fin (counts b)

abbrev RowWords (s : Fin 3) (counts : Fin 4 → ℕ) :=
  ∀ p : Positions counts, Row s p.1
abbrev MiddleWords (s : Fin 3) (counts : Fin 4 → ℕ) :=
  ∀ p : Positions counts, Middle s p.1
abbrev ColumnWords (s : Fin 3) (counts : Fin 4 → ℕ) :=
  ∀ p : Positions counts, Column s p.1

def singleCount (counts : Fin 4 → ℕ) : ℕ := counts 0 + counts 1
def crossCount (counts : Fin 4 → ℕ) : ℕ := counts 2 + counts 3

end MatrixMultiplication.CWStageCProducts

end

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H : Type*} [Fintype H]

abbrev HistoryRowWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, RowWords (side h) (counts h)
abbrev HistoryMiddleWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, MiddleWords (side h) (counts h)
abbrev HistoryColumnWords (side : H → Fin 3) (counts : H → Fin 4 → ℕ) :=
  ∀ h, ColumnWords (side h) (counts h)

end MatrixMultiplication.CWStageCProducts

end

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

def atomPermutation (s : Fin 3) (phi : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) :=
  if phi (Equiv.swap 2 s 0) = Equiv.swap 2 (phi s) 0 then Equiv.refl _
  else Equiv.swap 2 3

theorem branchAtom_transport (s : Fin 3) (phi : Equiv.Perm (Fin 3))
    (b : Fin 4) (i : Fin 3) :
    branchAtom (phi s) (atomPermutation s phi b) (phi i) = branchAtom s b i := by
  revert s phi b i
  decide +kernel

theorem shape_transport (s : Fin 3) (phi : Equiv.Perm (Fin 3)) (i : Fin 3) :
    shape (phi s) i = shape s (phi.symm i) := by
  have hiff : i = phi s ↔ phi.symm i = s := by
    constructor
    · intro h
      simp only [h, Equiv.symm_apply_apply]
    · intro h
      have hh := congrArg phi h
      simpa only [Equiv.apply_symm_apply] using hh
  simp only [shape, hiff]

end MatrixMultiplication.CWStageCProducts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWStageCStatistics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

abbrev ChildPair := Fin 7 × Fin 7

def joinChildren (p : ChildPair) : Word := (Matrix.vecCons (p.1) (Matrix.vecCons (p.2) Matrix.vecEmpty))
def splitChildren (w : Word) : ChildPair := (w 0, w 1)

@[simp] theorem joinChildren_zero (p : ChildPair) : joinChildren p 0 = p.1 := rfl
@[simp] theorem joinChildren_one (p : ChildPair) : joinChildren p 1 = p.2 := rfl

@[simp] theorem join_split_children (w : Word) : joinChildren (splitChildren w) = w := by
  funext i
  fin_cases i <;> rfl

theorem branchAtom_le_shape (s : Fin 3) (b : Fin 4) (i : Fin 3) :
    branchAtom s b i ≤ shape s i := by
  fin_cases s <;> fin_cases b <;> fin_cases i <;> decide

end MatrixMultiplication.CWStageCProducts

end

noncomputable section
section

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

abbrev ChildWords := (Fin 1 → Fin 7) × (Fin 1 → Fin 7)

def singletonChildWords (p : ChildPair) : ChildWords :=
  (fun _ => p.1, fun _ => p.2)

end MatrixMultiplication.CWStageCProducts

end

open scoped BigOperators
open MatrixMultiplication.Foundation

namespace MatrixMultiplication.CWStageCProducts

attribute [local instance] Classical.propDecidable Classical.decEq

def branchStatistic (s : Fin 3) (b : Fin 4) (i : Fin 3) : Fin 6 :=
  if i = s then if b.val < 2 then 3 else 2 else 1

end MatrixMultiplication.CWStageCProducts

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_GroupOrbitCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.RecoverySupport

variable {K X Y Z : Type*} [Zero K] [Fintype X] [Fintype Y] [Fintype Z]

def support (Q : X → Y → Z → K) : Finset (X × Y × Z) := by
  classical
  exact Finset.univ.filter fun p => Q p.1 p.2.1 p.2.2 ≠ 0

theorem support_card_le (Q : X → Y → Z → K) :
    (support Q).card ≤ Fintype.card X * Fintype.card Y * Fintype.card Z := by
  classical
  have h := Finset.card_filter_le (s := (Finset.univ : Finset (X × Y × Z)))
    (p := fun p => Q p.1 p.2.1 p.2.2 ≠ 0)
  simpa only [support, Finset.card_univ, Fintype.card_prod, Nat.mul_assoc] using h

theorem support_card_le_exp (Q : X → Y → Z → K) {bX bY bZ : ℝ} (N : ℕ)
    (hX : (Fintype.card X : ℝ) ≤ Real.exp (bX * N))
    (hY : (Fintype.card Y : ℝ) ≤ Real.exp (bY * N))
    (hZ : (Fintype.card Z : ℝ) ≤ Real.exp (bZ * N)) :
    ((support Q).card : ℝ) ≤ Real.exp ((bX + bY + bZ) * N) := by
  have hcard : ((support Q).card : ℝ) ≤
      (Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z := by
    exact_mod_cast support_card_le Q
  calc
    ((support Q).card : ℝ) ≤
        (Fintype.card X : ℝ) * Fintype.card Y * Fintype.card Z := hcard
    _ ≤ (Real.exp (bX * N) * Real.exp (bY * N)) * Real.exp (bZ * N) :=
      mul_le_mul (mul_le_mul hX hY (Nat.cast_nonneg _) (Real.exp_pos _).le)
        hZ (Nat.cast_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp ((bX + bY + bZ) * N) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

theorem word_card_eq_exp {d : ℕ} (hd : 0 < d) (a N : ℕ) :
    (Fintype.card (Fin (a * N) → Fin d) : ℝ) =
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hdr : 0 < (d : ℝ) := by exact_mod_cast hd
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  calc
    (d : ℝ) ^ (a * N) = Real.exp (((a * N : ℕ) : ℝ) * Real.log (d : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hdr]
    _ = Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
      simp only [Nat.cast_mul]
      congr 1
      ring

def cw5SupportRate (a : ℕ) : ℝ := 3 * (a : ℝ) * Real.log 7 + 1

theorem cw5SupportRate_pos (a : ℕ) : 0 < cw5SupportRate a := by
  have hlog : 0 ≤ Real.log 7 := Real.log_nonneg (by norm_num)
  have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg a)) hlog
  unfold cw5SupportRate
  linarith

end MatrixMultiplication.RecoverySupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.HistorySupport

variable {H : Type*}

abbrev HistoryWords (P : H → Type*) (l r : H → ℕ) (d : ℕ) :=
  ∀ h, P h → ((Fin (l h) → Fin d) × (Fin (r h) → Fin d))

def totalLength [Fintype H] (P : H → Type*) [∀ h, Fintype (P h)]
    (l r : H → ℕ) : ℕ :=
  ∑ h, Fintype.card (P h) * (l h + r h)

variable [Fintype H] [DecidableEq H]
variable (P : H → Type*) [∀ h, Fintype (P h)] [∀ h, DecidableEq (P h)]
variable (l r : H → ℕ)

theorem card_historyWords (d : ℕ) :
    Fintype.card (HistoryWords P l r d) = d ^ totalLength P l r := by
  change Fintype.card (∀ h, P h → ((Fin (l h) → Fin d) × (Fin (r h) → Fin d))) = _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, ← pow_add, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  unfold totalLength
  apply Finset.sum_congr rfl
  intro h _
  exact Nat.mul_comm _ _

theorem card_historyWords_le_pow {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (hlen : totalLength P l r ≤ a * N) :
    Fintype.card (HistoryWords P l r d) ≤ d ^ (a * N) := by
  rw [card_historyWords]
  exact Nat.pow_le_pow_right hd hlen

theorem card_historyWords_le_exp {d : ℕ} (hd : 0 < d) (a N : ℕ)
    (hlen : totalLength P l r ≤ a * N) :
    (Fintype.card (HistoryWords P l r d) : ℝ) ≤
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hpow : ((d ^ (a * N) : ℕ) : ℝ) =
      Real.exp (((a : ℝ) * Real.log (d : ℝ)) * N) := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using
      RecoverySupport.word_card_eq_exp hd a N
  rw [← hpow]
  exact_mod_cast card_historyWords_le_pow P l r hd a N hlen

theorem support_card_le_exp {K : Type*} [Zero K] {d : ℕ} (hd : 0 < d)
    (Q : HistoryWords P l r d → HistoryWords P l r d → HistoryWords P l r d → K)
    (a N : ℕ) (hlen : totalLength P l r ≤ a * N) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp ((3 * (a : ℝ) * Real.log (d : ℝ)) * N) := by
  have hdim := card_historyWords_le_exp P l r hd a N hlen
  have h := RecoverySupport.support_card_le_exp Q N hdim hdim hdim
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

theorem cw5_support_card_le_exp {K : Type*} [Zero K]
    (Q : HistoryWords P l r 7 → HistoryWords P l r 7 → HistoryWords P l r 7 → K)
    (a N : ℕ) (hlen : totalLength P l r ≤ a * N) :
    ((RecoverySupport.support Q).card : ℝ) ≤
      Real.exp (RecoverySupport.cw5SupportRate a * N) := by
  apply (support_card_le_exp P l r (by norm_num) Q a N hlen).trans
  apply Real.exp_le_exp.mpr
  unfold RecoverySupport.cw5SupportRate
  simp only [Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Nat.cast_nonneg N)

end MatrixMultiplication.HistorySupport

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]
  {P X Y : C → Type*}
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [∀ c, Fintype (X c)] [∀ c, DecidableEq (X c)]
  [∀ c, Fintype (Y c)] [∀ c, DecidableEq (Y c)]

abbrev PairProfile (P X Y : C → Type*) [∀ c, Fintype (P c)] :=
  InheritedMasks.Profile P X × InheritedMasks.Profile P Y

end

end MatrixMultiplication.PermutationMatching

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecoveryBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial




section
noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def sideVariable {V : Type*} (side : Fin 3) (x y z : V) : V := (Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty))) side

end MatrixMultiplication.AllFieldHistoryRecovery






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryGroupCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open MatrixMultiplication.Foundation
attribute [local instance] Classical.propDecidable Classical.decEq

namespace GroupAssignment

variable {I : Type*} {V E : I → Type*}

def collect (a : ∀ i, V i → Option (E i)) (v : ∀ i, V i) : Option (∀ i, E i) :=
  if h : ∃ e : ∀ i, E i, ∀ i, a i (v i) = some (e i) then
    some (Classical.choose h) else none

theorem collect_eq_some (a : ∀ i, V i → Option (E i)) (v : ∀ i, V i) (e : ∀ i, E i) :
    collect a v = some e ↔ ∀ i, a i (v i) = some (e i) := by
  unfold collect
  split_ifs with h
  · constructor
    · intro he i
      have heq := Option.some.inj he
      simpa only [heq] using Classical.choose_spec h i
    · intro he
      congr 1
      funext i
      exact Option.some.inj ((Classical.choose_spec h i).symm.trans (he i))
  · constructor
    · intro he
      cases he
    · intro he
      exact False.elim (h ⟨e, he⟩)

end GroupAssignment

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistoryRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.PermutationMatching

open MatrixMultiplication.InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

def fullOrbitFilter (G : Type*) {V : Type*} [SMul G V] [Fintype V]
    (v : V) : Finset V :=
  @Finset.filter V (fun w => ∃ g : G, g • v = w)
    (fun w => Classical.propDecidable (∃ g : G, g • v = w)) Finset.univ

def rejectedFilter {V : Type*} (orbit : Finset V) (bad : V → Prop) : Finset V :=
  @Finset.filter V bad (fun v => Classical.propDecidable (bad v)) orbit

theorem rejectedFilter_congr {V : Type*} (orbit : Finset V) (p q : V → Prop)
    (h : ∀ v, p v ↔ q v) : rejectedFilter orbit p = rejectedFilter orbit q := by
  ext v
  simp only [rejectedFilter, Finset.mem_filter, h]

end MatrixMultiplication.PermutationMatching

end

namespace MatrixMultiplication.OrbitLoss

variable {X : Type*} [DecidableEq X]

theorem missing_card_partition (s : Finset X) (pass assigned : X → Prop)
    [DecidablePred pass] [DecidablePred assigned] :
    (s.filter fun x => ¬(pass x ∧ assigned x)).card =
      (s.filter fun x => ¬pass x).card +
      (s.filter fun x => pass x ∧ ¬assigned x).card := by
  classical
  have heq : (s.filter fun x => ¬(pass x ∧ assigned x)) =
      (s.filter fun x => ¬pass x) ∪ (s.filter fun x => pass x ∧ ¬assigned x) := by
    ext x
    by_cases hp : pass x <;> simp [hp]
  have hd : Disjoint (s.filter fun x => ¬pass x)
      (s.filter fun x => pass x ∧ ¬assigned x) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2.1
  rw [heq, Finset.card_union_of_disjoint hd]

theorem missing_fraction_partition (s : Finset X) (pass assigned : X → Prop)
    [DecidablePred pass] [DecidablePred assigned] :
    ((s.filter fun x => ¬(pass x ∧ assigned x)).card : ℝ) / s.card =
      ((s.filter fun x => ¬pass x).card : ℝ) / s.card +
      ((s.filter fun x => pass x ∧ ¬assigned x).card : ℝ) / s.card := by
  rw [missing_card_partition, Nat.cast_add, add_div]

end MatrixMultiplication.OrbitLoss

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation AllFieldHistory
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

@[simp] theorem sideVariable_zero {V : Type*} (x y z : V) :
    sideVariable 0 x y z = x := rfl

@[simp] theorem sideVariable_one {V : Type*} (x y z : V) :
    sideVariable 1 x y z = y := rfl

@[simp] theorem sideVariable_two {V : Type*} (x y z : V) :
    sideVariable 2 x y z = z := rfl

end MatrixMultiplication.AllFieldHistoryRecovery

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistorySourceAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.GroupOrbitProjection

open PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

section UniformRestriction

variable {H S : Type*} [Fintype H] [Fintype S] [DecidableEq H] [DecidableEq S]

def curryFamily (X : H × S → Type*) : (∀ c, X c) ≃ (∀ h s, X (h, s)) where
  toFun x h s := x (h, s)
  invFun x c := x c.1 c.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem average_subtype_restrict {X : H → Type*} [∀ h, Fintype (X h)]
    [∀ h, Nonempty (X h)] (p : H → Prop) [DecidablePred p]
    (f : (∀ h : {h // p h}, X h.val) → ℝ) :
    average (fun x : ∀ h, X h => f (fun h => x h.val)) = average f := by
  change average (fun x =>
    (fun z : (∀ h : {h // p h}, X h.val) × (∀ h : {h // ¬p h}, X h.val) => f z.1)
      ((Equiv.piEquivPiSubtypeProd p X) x)) = average f
  rw [average_equiv (Equiv.piEquivPiSubtypeProd p X)
    (fun z : (∀ h : {h // p h}, X h.val) × (∀ h : {h // ¬p h}, X h.val) => f z.1),
    average_prod_fst]

theorem average_history_restrict {X : H × S → Type*} [∀ c, Fintype (X c)]
    [∀ c, Nonempty (X c)] (p : H → Prop) [DecidablePred p]
    (f : (∀ c : {h // p h} × S, X (c.1.val, c.2)) → ℝ) :
    average (fun x : ∀ c, X c => f (fun c => x (c.1.val, c.2))) = average f := by
  calc
    _ = average (fun x : ∀ h s, X (h, s) => f (fun c => x c.1.val c.2)) :=
      average_equiv (curryFamily X) _
    _ = average (fun x : ∀ h : {h // p h}, ∀ s, X (h.val, s) =>
        f (fun c => x c.1 c.2)) :=
      average_subtype_restrict (X := fun h => ∀ s, X (h, s)) p
        (fun x => f (fun c => x c.1 c.2))
    _ = average f :=
      average_equiv (curryFamily (fun c : {h // p h} × S => X (c.1.val, c.2))).symm f

theorem average_half_history_restrict {X : H × S → Type*} [∀ c, Fintype (X c)]
    [∀ c, Nonempty (X c)] (p : H → Prop) [DecidablePred p]
    (f : ((∀ c : {h // p h} × S, X (c.1.val, c.2)) ×
      (∀ c : {h // p h} × S, X (c.1.val, c.2))) → ℝ) :
    average (fun g : (∀ c, X c) × (∀ c, X c) =>
      f ((fun c => g.1 (c.1.val, c.2)), (fun c => g.2 (c.1.val, c.2)))) =
        average f := by
  rw [average_prod_average]
  calc
    _ = average (fun x : ∀ c, X c =>
        average (fun y : ∀ c : {h // p h} × S, X (c.1.val, c.2) =>
          f ((fun c => x (c.1.val, c.2)), y))) := by
      apply average_congr
      intro x
      exact average_history_restrict (X := X) p
        (fun y => f ((fun c => x (c.1.val, c.2)), y))
    _ = average (fun x : ∀ c : {h // p h} × S, X (c.1.val, c.2) =>
        average (fun y => f (x, y))) :=
      average_history_restrict (X := X) p (fun x => average (fun y => f (x, y)))
    _ = average f := (average_prod_average f).symm

end UniformRestriction

section FinsetUnion

variable {X I : Type*} [Fintype I]

theorem finset_union_fraction_le (samples : Finset X) (bad : I → X → Prop)
    (bound : I → ℝ)
    (hbound : ∀ i, (((samples.filter (bad i)).card : ℝ) / samples.card) ≤ bound i) :
    (((samples.filter (fun v => ∃ i, bad i v)).card : ℝ) / samples.card) ≤
      ∑ i, bound i := by
  have hset : samples.filter (fun v => ∃ i, bad i v) =
      Finset.univ.biUnion (fun i => samples.filter (bad i)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hv, i, hi⟩ => ⟨i, hv, hi⟩, fun ⟨i, hv, hi⟩ => ⟨hv, i, hi⟩⟩
  have hcard : ((samples.filter (fun v => ∃ i, bad i v)).card : ℝ) ≤
      ∑ i, ((samples.filter (bad i)).card : ℝ) := by
    rw [hset, ← Nat.cast_sum]
    exact Nat.cast_le.mpr Finset.card_biUnion_le
  calc
    _ ≤ (∑ i, ((samples.filter (bad i)).card : ℝ)) / samples.card :=
      div_le_div_of_nonneg_right hcard (Nat.cast_nonneg _)
    _ = ∑ i, ((samples.filter (bad i)).card : ℝ) / samples.card := Finset.sum_div _ _ _
    _ ≤ ∑ i, bound i := Finset.sum_le_sum (fun i _ => hbound i)

theorem rejected_union_fraction_le (samples : Finset X) (bad : I → X → Prop)
    (bound : I → ℝ)
    (hbound : ∀ i, ((rejectedFilter samples (bad i)).card : ℝ) / samples.card ≤ bound i) :
    ((rejectedFilter samples (fun v => ∃ i, bad i v)).card : ℝ) / samples.card ≤
      ∑ i, bound i := by
  have hh (i : I) : ((samples.filter (bad i)).card : ℝ) / samples.card ≤ bound i := by
    simpa only [rejectedFilter, Finset.filter_congr_decidable] using hbound i
  have heq : samples.filter (fun v => ∃ i, bad i v) =
      rejectedFilter samples (fun v => ∃ i, bad i v) := by
    ext v
    simp only [rejectedFilter, Finset.mem_filter]
  rw [← heq]
  exact finset_union_fraction_le samples bad bound hh

end FinsetUnion

end MatrixMultiplication.GroupOrbitProjection

end
end




section





noncomputable section

namespace MatrixMultiplication.AllFieldHistoryGroupedRecovery

open AllFieldHistory
open PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem filter_eq_rejected {V : Type*} (orbit : Finset V)
    (bad : V → Prop) (d : DecidablePred bad) :
    @Finset.filter V bad d orbit = rejectedFilter orbit bad := by
  ext v
  simp only [rejectedFilter, Finset.mem_filter]

end MatrixMultiplication.AllFieldHistoryGroupedRecovery






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Histories_HistorySums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldHistory

open AllFieldParameters
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem subtype_sum_indicator_inline_MatrixMultiplication_AllFieldHistorySums {A : Type*} [Fintype A]
    (P : A → Prop) [DecidablePred P] [Fintype {a // P a}] (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem list_filter_sum_inline_MatrixMultiplication_AllFieldHistorySums {A : Type*} (xs : List A) (p : A → Bool)
    (f : A → ℝ) :
    ((xs.filter p).map f).sum = (xs.map (fun a => if p a then f a else 0)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => cases hp : p a <;> simp [hp, ih]

theorem list_sum_congr {A : Type*} (xs : List A) (f g : A → ℝ)
    (h : ∀ a ∈ xs, f a = g a) : (xs.map f).sum = (xs.map g).sum :=
  congrArg List.sum (List.map_congr_left h)

theorem list_sum_comm {A B : Type*} (xs : List A) (ys : List B)
    (f : A → B → ℝ) :
    (xs.map (fun a => (ys.map (f a)).sum)).sum =
      (ys.map (fun b => (xs.map (fun a => f a b)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, List.sum_map_add]

theorem list_rat_cast_inline_MatrixMultiplication_AllFieldHistorySums {A : Type*} (xs : List A) (f : A → ℚ) :
    ((xs.map f).sum : ℝ) = (xs.map (fun a => (f a : ℝ))).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

end MatrixMultiplication.AllFieldHistory

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ParametersContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters.Contractions

open MatrixMultiplication.AllFieldCertificates.Replay

variable {α : Type}

attribute [local instance] lexOrd

def coefficientStep (xs : List Nat) : List Nat :=
  (List.range (xs.length + 2)).map fun i =>
    (xs[i]?.getD 0) + (if i > 0 then 5 * xs[i-1]?.getD 0 else 0) +
      (if i > 1 then xs[i-2]?.getD 0 else 0)

def coefficients : List Nat := (List.range 8).foldl (fun xs _ => coefficientStep xs) [1]

end MatrixMultiplication.AllFieldParameters.Contractions

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWWordDimensionParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.CWWordDimensions

open scoped BigOperators Polynomial

attribute [local instance] Classical.propDecidable

def sitePolynomial : Polynomial ℕ := 1 + Polynomial.C 5 * Polynomial.X + Polynomial.X ^ 2

def recursiveCoeff : ℕ → ℕ → ℕ
  | 0, j => if j = 0 then 1 else 0
  | n + 1, j => recursiveCoeff n j +
      5 * (if 1 ≤ j then recursiveCoeff n (j - 1) else 0) +
      (if 2 ≤ j then recursiveCoeff n (j - 2) else 0)

theorem coeff_eq_recursive (n j : ℕ) :
    (sitePolynomial ^ n).coeff j = recursiveCoeff n j := by
  induction n generalizing j with
  | zero => simp [recursiveCoeff, Polynomial.coeff_one]
  | succ n ih =>
    have hmul (p : Polynomial ℕ) : sitePolynomial * p =
        p + Polynomial.C 5 * (Polynomial.X * p) + Polynomial.X ^ 2 * p := by
      simp only [sitePolynomial, add_mul, one_mul, mul_assoc]
    have hshift := Polynomial.coeff_X_pow_mul' (sitePolynomial ^ n) 1 j
    simp only [pow_one] at hshift
    rw [pow_succ', hmul, Polynomial.coeff_add, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, hshift, Polynomial.coeff_X_pow_mul']
    simp only [ih, recursiveCoeff]

end MatrixMultiplication.CWWordDimensions

end

namespace MatrixMultiplication.CWWordDimensionParameters

open CWWordDimensions AllFieldParameters.Contractions

theorem table_eq_recursive : ∀ j : Fin 17,
    (coefficients[j.val]?.getD 0) = recursiveCoeff 8 j.val := by
  decide +kernel

theorem table_positive : ∀ j : Fin 17, 0 < (coefficients[j.val]?.getD 0) := by
  decide +kernel

end MatrixMultiplication.CWWordDimensionParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_ZeroLeafRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology

noncomputable def factorialLogRemainder (n : ℕ) : ℝ :=
  Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n)

@[simp] theorem factorialLogRemainder_zero : factorialLogRemainder 0 = 0 := by
  simp [factorialLogRemainder]

end MatrixMultiplication.Foundation





noncomputable section






namespace MatrixMultiplication.AllFieldZeroLeafRates

open MatrixMultiplication.Foundation Filter AllFieldParameters
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem multiplicity_pos (s : Fin 6) : 0 < AllFieldParameters.multiplicity s := by
  fin_cases s <;> decide

end MatrixMultiplication.AllFieldZeroLeafRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityIncidence

open MatrixMultiplication.Foundation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Counts

variable {P U Z A : Type*} [Fintype P] [DecidableEq U] [DecidableEq A]

def jointCount (w : P → U) (z : P → Z) (part : Z → A) (u : U) (a : A) : ℕ :=
  Fintype.card {i : P // w i = u ∧ part (z i) = a}

end Counts

section Groups

variable {P U Z A : Type*} [Fintype P] [DecidableEq P]
  [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A]

def designatedGroup (d : U → Prop) (u : U) : Option U :=
  if d u then some u else none

abbrev GroupPos (w : P → U) (d : U → Prop) (k : Option U) :=
  {i : P // designatedGroup d (w i) = k}

def groupProjection (w : P → U) (d : U → Prop) (k : Option U)
    (z : P → Z) (part : Z → A) : GroupPos w d k → A :=
  fun i => part (z i.val)

end Groups

section GroupEntropy

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

def groupMass (p : U → ℝ) (group : U → K) (k : K) : ℝ :=
  ∑ u, if group u = k then p u else 0

def groupLaw (p : U → ℝ) (group : U → K) (law : U → A → ℝ)
    (k : K) (a : A) : ℝ :=
  (∑ u, if group u = k then p u * law u a else 0) / groupMass p group k

end GroupEntropy

section Compatibility

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos Shape Pair Left Right : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]
variable (shapeCounts : ∀ c, Shape c → ℕ) (pairCounts : ∀ c, Pair c → ℕ)
  (leftPart : ∀ c, Pair c → Left c) (rightPart : ∀ c, Pair c → Right c)
  (designatedLeft designatedRight : ∀ c, Shape c → Prop)
  (leftLaw : ∀ c, Shape c → Left c → ℝ)
  (rightLaw : ∀ c, Shape c → Right c → ℝ) (χ : ℝ)

def wordEntropyBound (I A : Type*) [Fintype I] [Fintype A] (H : ℝ) : ℝ :=
  ((Fintype.card I : ℝ) + 1) ^ Fintype.card A *
    Real.exp ((Fintype.card I : ℝ) * H +
      ((Fintype.card A : ℝ) + 1) * (1 + Real.log (Fintype.card I + 1 : ℕ)))

end Compatibility

end MatrixMultiplication.JointCompatibilityIncidence

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_JointPopulationMixedCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulationCompatibility

open MatrixMultiplication.Foundation InheritedMasks
open JointCompatibilityIncidence
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {H : Type*}
  [Fintype H]
  [DecidableEq H]

theorem scaled_count_window {x n p χ : ℝ} (hn : 0 < n)
    (hw : |x / n - p| ≤ χ) : |x - n * p| ≤ n * χ := by
  calc
    |x - n * p| = |(x / n - p) * n| := by
      rw [sub_mul, div_mul_cancel₀ _ hn.ne', mul_comm p n]
    _ = |x / n - p| * n := by rw [abs_mul, abs_of_pos hn]
    _ ≤ χ * n := mul_le_mul_of_nonneg_right hw hn.le
    _ = n * χ := mul_comm _ _

end MatrixMultiplication.JointPopulationCompatibility






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointCompatibilityEntropyBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open MatrixMultiplication.Foundation
open MatrixMultiplication.JointCompatibilityIncidence
open scoped BigOperators

namespace MatrixMultiplication.JointCompatibilityEntropyBound

attribute [local instance] Classical.propDecidable

section ClassCounts

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (Pos A : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

def classTypeError : ℝ :=
  ∑ c, ((Fintype.card (A c) : ℝ) + 1) *
    (1 + Real.log (Fintype.card (Pos c) + 1 : ℕ))

end ClassCounts

section GroupCounts

def wordTypeError (I A : Type*) [Fintype I] [Fintype A] : ℝ :=
  ((Fintype.card A : ℝ) + 1) * (1 + Real.log (Fintype.card I + 1 : ℕ)) +
    (Fintype.card A : ℝ) * Real.log (Fintype.card I + 1 : ℕ)

end GroupCounts

end MatrixMultiplication.JointCompatibilityEntropyBound

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityScaling

open MatrixMultiplication.Foundation JointCompatibilityIncidence
open JointCompatibilityEntropyBound Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {Shape : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]

def baseSize (base : ∀ c, Shape c → ℕ) (c : C) : ℕ := ∑ a, base c a

def baseTotal (base : ∀ c, Shape c → ℕ) : ℕ := ∑ c, baseSize base c

def baseGroupSize (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (g : Σ c, Option (Shape c)) : ℕ :=
  ∑ a : {a : Shape g.1 // designatedGroup (d g.1) a = g.2}, base g.1 a.val

def baseGroupedEntropy (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (H : (Σ c, Option (Shape c)) → ℝ) : ℝ :=
  ∑ g, (baseGroupSize base d g : ℝ) * H g

def typeErrorFactor (B t : ℕ) : ℝ := 1 + Real.log (t * B + 1 : ℕ)

def classErrorCoefficient (A : C → Type*) [∀ c, Fintype (A c)] : ℝ :=
  ∑ c, ((Fintype.card (A c) : ℝ) + 1)

def groupErrorCoefficient (Shape A : C → Type*)
    [∀ c, Fintype (Shape c)] [∀ c, Fintype (A c)] : ℝ :=
  ∑ g : Σ c, Option (Shape c), (2 * (Fintype.card (A g.1) : ℝ) + 1)

end MatrixMultiplication.JointCompatibilityScaling

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_NativeLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldNativeCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators

theorem list_rat_cast_inline_MatrixMultiplication_AllFieldNativeLaws {I : Type*} (xs : List I) (f : I → ℚ) :
    ((xs.map f).sum : ℝ) = (xs.map fun i => (f i : ℝ)).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih => simp [ih]

end MatrixMultiplication.AllFieldNativeCapacity

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_ParametersHalfComplement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem normalized_singleton_law {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → ℚ) (a : A) (hp : ∑ i, p i = 1)
    (hs : ∀ i, i ≠ a → p i = 0) (i : A) : p i = if i = a then 1 else 0 := by
  have ha : p a = 1 := by
    have hsum : (∑ i, p i) = p a := by
      apply Finset.sum_eq_single a
      · intro i _ hi
        exact hs i hi
      · simp
    exact hsum.symm.trans hp
  by_cases hi : i = a
  · simp [hi, ha]
  · simp [hi, hs i hi]

end MatrixMultiplication.AllFieldParameters

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupBranchLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section






namespace MatrixMultiplication.JointConditionalCountEntropy

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {U A : Type*} [Fintype U] [Fintype A]

attribute [local instance] Classical.propDecidable

def classCounts (n : U → ℕ) (f : U → A) (a : A) (u : U) : ℕ :=
  if f u = a then n u else 0

def classSize (n : U → ℕ) (f : U → A) (a : A) : ℕ :=
  ∑ u, classCounts n f a u

end MatrixMultiplication.JointConditionalCountEntropy






end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

def exponentialCoefficients : List ℚ :=
  (List.range 17).map (fun j => 1 / (Nat.factorial j : ℚ))

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_1_14I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_2_13I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_2_13I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_3_12I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_4_11I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_4_11I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_5_10I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_6_9I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_7_8I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_2_12I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_2_12I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_3_11I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_3_11I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_4_10I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_4_10I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_5_9I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_5_9I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_6_8I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_7_7I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_7_7I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_3_10I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_3_10I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_4_9I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_4_9I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_5_8I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_5_8I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA3_6_7I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_6_7I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_4_8I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_4_8I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_5_7I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_5_7I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA4_6_6I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_6_6I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA5_5_6I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA5_5_6I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | 4 => 2
  | 5 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_1_6I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_1_6I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_1_6I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_1_6I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_1_6I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_1_6I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_1_6I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_1_6I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_1_6I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_1_6I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_2_5I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_2_5I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_2_5I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_2_5I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_2_5I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_2_5I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_2_5I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | _ => 0
def CB1_2_5I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_3_4I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_3_4I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_3_4I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_3_4I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_3_4I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_3_4I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_3_4I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 4 => 1
  | _ => 0
def CB1_3_4I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_3_4I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_3_4I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_3_4I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_3_4I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_3_4I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_3_4I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_4_3I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_4_3I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_4_3I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_4_3I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_4_3I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_4_3I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_4_3I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 4 => 1
  | _ => 0
def CB1_4_3I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_4_3I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_4_3I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_4_3I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_4_3I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_4_3I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_4_3I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_5_2I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_5_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_5_2I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_5_2I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_5_2I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_5_2I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_5_2I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_5_2I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_5_2I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_5_2I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_5_2I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_5_2I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_6_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_6_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_6_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_6_1I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB1_6_1I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_6_1I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_6_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_6_1I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB1_6_1I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_6_1I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_1_5I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_1_5I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_1_5I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_1_5I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_1_5I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_1_5I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_1_5I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_1_5I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_1_5I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_1_5I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_1_5I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_1_5I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_2_4I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_2_4I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_2_4I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_2_4I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_2_4I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_2_4I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_2_4I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_2_4I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_2_4I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_2_4I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_2_4I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_2_4I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_2_4I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_3_3I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 0 => 2
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_3_3I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_3_3I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_3_3I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_3_3I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_3_3I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_3_3I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_3_3I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_3_3I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_3_3I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_3_3I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_4_2I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_4_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_4_2I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_4_2I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_4_2I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_4_2I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_4_2I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_4_2I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_4_2I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_4_2I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_4_2I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_4_2I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_4_2I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_5_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_5_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_5_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_5_1I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB2_5_1I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_5_1I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_5_1I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB2_5_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_5_1I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB2_5_1I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB2_5_1I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB2_5_1I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_1_4I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_1_4I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_1_4I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_1_4I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_1_4I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_1_4I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_1_4I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 4 => 1
  | _ => 0
def CB3_1_4I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_1_4I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_1_4I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_1_4I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_1_4I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_1_4I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_2_3I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_2_3I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_2_3I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_2_3I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_2_3I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_2_3I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_2_3I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_2_3I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_2_3I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_2_3I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_3_2I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_3_2I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_3_2I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_3_2I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_3_2I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_3_2I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_3_2I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_4_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_4_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_4_1I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_4_1I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_4_1I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 4 => 1
  | _ => 0
def CB3_4_1I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_4_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_4_1I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_4_1I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_4_1I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_4_1I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_4_1I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_1_3I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_1_3I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB4_1_3I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB4_1_3I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB4_1_3I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 4 => 1
  | _ => 0
def CB4_1_3I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_1_3I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_1_3I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB4_1_3I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB4_1_3I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB4_1_3I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_1_3I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_2_2I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 2 => 1
  | 1 => 2
  | 0 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_2_2I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB4_2_2I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB4_2_2I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB4_2_2I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_2_2I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB4_2_2I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB4_2_2I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB4_2_2I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_2_2I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB4_3_1I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB4_3_1I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB4_3_1I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 4 => 1
  | _ => 0
def CB4_3_1I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_3_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB4_3_1I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB4_3_1I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB4_3_1I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB4_3_1I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB5_1_2I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB5_1_2I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB5_1_2I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_1_2I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_1_2I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB5_1_2I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB5_1_2I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_1_2I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB5_2_1I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB5_2_1I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB5_2_1I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB5_2_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB5_2_1I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB5_2_1I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB5_2_1I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB6_1_1I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB6_1_1I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB6_1_1I2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB6_1_1I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB6_1_1I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_JointCompatibilityRateLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityRateLimit

open MatrixMultiplication.Foundation JointCompatibilityIncidence
open JointCompatibilityEntropyBound JointCompatibilityScaling Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape Pair Left Right : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]
  [∀ c, Fintype (Left c)] [∀ c, DecidableEq (Left c)]
  [∀ c, Fintype (Right c)] [∀ c, DecidableEq (Right c)]

def totalBase (base : ∀ c, Shape c → ℕ) : ℕ := ∑ c, baseSize base c

def projectedReferenceEntropy (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (H : (Σ c, Option (Shape c)) → ℝ) : ℝ :=
  ∑ g : Σ c, Option (Shape c), (baseGroupSize base d g : ℝ) * H g

def PairWindow (base : ∀ c, Shape c → ℕ) (q : ∀ c, Pair c → ℝ)
    (Pos : C → Type*) [∀ c, Fintype (Pos c)]
    (pairCounts : ∀ c, Pair c → ℕ) (η : ℝ) : Prop :=
  ∀ c, 0 < baseSize base c → ∀ a,
    |(pairCounts c a : ℝ) / Fintype.card (Pos c) - q c a| ≤ η

def errorCoefficient (Shape Pair Left Right : C → Type*)
    [∀ c, Fintype (Shape c)] [∀ c, Fintype (Pair c)]
    [∀ c, Fintype (Left c)] [∀ c, Fintype (Right c)] : ℝ :=
  classErrorCoefficient Shape + classErrorCoefficient Pair +
    groupErrorCoefficient Shape Left + groupErrorCoefficient Shape Right

end MatrixMultiplication.JointCompatibilityRateLimit

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Extraction_GroupPairWindows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.JointCompatibilityIncidence

namespace MatrixMultiplication.JointCompatibilityControls

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

def residualBase (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop) (c : C) : ℕ :=
  ∑ u : {u : Shape c // ¬d c u}, base c u.val

def designatedBase (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop) (c : C) : ℕ :=
  ∑ u : {u : Shape c // d c u}, base c u.val

def totalCenterCount (base : ∀ c, Shape c → ℕ)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (a : A c) : ℝ :=
  ∑ u, (base c u : ℝ) * law c u a

def residualCenter (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (c : C) (a : A c) : ℝ :=
  (∑ u : {u : Shape c // ¬d c u}, (base c u.val : ℝ) * law c u.val a) /
    residualBase base d c

def groupCenter (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (law : ∀ c, Shape c → A c → ℝ) (g : Σ c, Option (Shape c)) : A g.1 → ℝ :=
  match g.2 with
  | some u => law g.1 u
  | none => residualCenter base d law g.1

end MatrixMultiplication.JointCompatibilityControls

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPairMixtureControls

open JointCompatibilityControls JointCompatibilityScaling
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A B : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
  [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]

def pairMixture (base : ∀ c, Shape c → ℕ)
    (left : ∀ c, Shape c → A c → ℝ) (right : ∀ c, Shape c → B c → ℝ)
    (c : C) (ab : A c × B c) : ℝ :=
  (∑ u, (base c u : ℝ) * left c u ab.1 * right c u ab.2) / baseSize base c

end MatrixMultiplication.JointPairMixtureControls

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_JointCompatibilityCountProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityCountProducer

open MatrixMultiplication.Foundation JointCompatibilityIncidence
open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
  {Shape A : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]
  [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

section PairMarginals

variable {Pair : C → Type*}
  [∀ c, Fintype (Pair c)] [∀ c, DecidableEq (Pair c)]

def aggregateCoefficient (base : ∀ c, Shape c → ℕ)
    (Pair : C → Type*) [∀ c, Fintype (Pair c)] : ℕ :=
  ∑ c, baseSize base c * Fintype.card (Pair c)

end PairMarginals

end MatrixMultiplication.JointCompatibilityCountProducer

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Parameters_TerminalPopulations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldTerminalPopulations

open AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ} {H : Type*} [Fintype H]
  {A : H → Type*} [∀ h, Fintype (A h)]

def law (ν : ∀ h, A h → ℚ) (x : Sigma A) : ℚ := ν x.1 x.2

end MatrixMultiplication.AllFieldTerminalPopulations

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Tensors_CWZeroGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.CWOrientedZero
open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable (F : Type*) [Field F]

def placedShape (zero selected : Fin 3) (a b : ℕ) : Fin 3 → ℕ :=
  fun s => if s = zero then 0 else if s = selected then a else b

def matched (zero : Fin 3) {E : Type*} (x y z : E) : Prop :=
  if zero = 0 then y = z else if zero = 1 then x = z else x = y

def Row (zero : Fin 3) (E : Type) : Type := if zero = 1 then E else Unit
def Middle (zero : Fin 3) (E : Type) : Type := if zero = 2 then E else Unit
def Column (zero : Fin 3) (E : Type) : Type := if zero = 0 then E else Unit
instance instFintypeRow (zero : Fin 3) (E : Type) [Fintype E] : Fintype (Row zero E) := by
  unfold Row; split_ifs <;> infer_instance
instance instFintypeMiddle (zero : Fin 3) (E : Type) [Fintype E] : Fintype (Middle zero E) := by
  unfold Middle; split_ifs <;> infer_instance
instance instFintypeColumn (zero : Fin 3) (E : Type) [Fintype E] : Fintype (Column zero E) := by
  unfold Column; split_ifs <;> infer_instance

theorem volume (zero : Fin 3) (E : Type) [Fintype E] :
    Fintype.card (Row zero E) * Fintype.card (Middle zero E) *
      Fintype.card (Column zero E) = Fintype.card E := by
  fin_cases zero
  · change Fintype.card Unit * Fintype.card Unit * Fintype.card E = Fintype.card E
    simp
  · change Fintype.card E * Fintype.card Unit * Fintype.card Unit = Fintype.card E
    simp
  · change Fintype.card Unit * Fintype.card E * Fintype.card Unit = Fintype.card E
    simp

end MatrixMultiplication.CWOrientedZero

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_FloorExponentialRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.FloorExponentialRates

open Filter
open scoped BigOperators Topology Classical

def count (rate : ℝ) (m : ℕ) : ℕ := ⌊Real.exp ((m : ℝ) * rate)⌋₊

theorem count_pos {rate : ℝ} (hr : 0 ≤ rate) (m : ℕ) : 0 < count rate m := by
  have he : (1 : ℝ) ≤ Real.exp ((m : ℝ) * rate) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hr)
  exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor (by simpa only [Nat.cast_one] using he))

end MatrixMultiplication.FloorExponentialRates

end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_Subdivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Subdivision

open MatrixMultiplication.Foundation InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Type*) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

def concatenate {X : Type*} (w : ∀ i, P i → X) : (Σ i, P i) → X :=
  fun p => w p.1 p.2

end MatrixMultiplication.Subdivision

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Entropy_GroupProjectedEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointNativeGroupedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

section FiniteGroups

variable {U K A : Type*} [Fintype U] [Fintype K] [Fintype A]

def groupMeasure (p : U → ℝ) (group : U → K) (q : U → A → ℝ)
    (k : K) (a : A) : ℝ :=
  ∑ u, if group u = k then p u * q u a else 0

def singletonResidualGroup (d : U → Prop) (weight : U → K) (u : U) : U ⊕ K :=
  if d u then Sum.inl u else Sum.inr (weight u)

end FiniteGroups

end MatrixMultiplication.JointNativeGroupedEntropy

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointGroupedEntropyEmbedding

open MatrixMultiplication.Foundation JointCompatibilityIncidence JointNativeGroupedEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {U V K L A : Type*}
  [Fintype U] [Fintype V] [Fintype K] [Fintype L] [Fintype A]

def pushforwardWeight (p : U → ℝ) (f : U → V) (v : V) : ℝ :=
  ∑ u, if f u = v then p u else 0

end MatrixMultiplication.JointGroupedEntropyEmbedding

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldNativeGroupedRates

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open JointNativeGroupedEntropy
open AllFieldNativeCapacity
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def supportSubtypeEquiv {α : Type*} (xs : List α) (f : α → α)
    (hm : ∀ x ∈ xs, f x ∈ xs) (hi : ∀ x ∈ xs, f (f x) = x) :
    Equiv.Perm {x // x ∈ xs} where
  toFun x := ⟨f x.val, hm x.val x.property⟩
  invFun x := ⟨f x.val, hm x.val x.property⟩
  left_inv x := Subtype.ext (hi x.val x.property)
  right_inv x := Subtype.ext (hi x.val x.property)

def supportIndexEquiv {α : Type*} [DecidableEq α] (xs : List α) (hn : xs.Nodup)
    (f : α → α) (hm : ∀ x ∈ xs, f x ∈ xs) (hi : ∀ x ∈ xs, f (f x) = x) :
    Equiv.Perm (Fin xs.length) :=
  ((hn.getEquiv xs).trans (supportSubtypeEquiv xs f hm hi)).trans (hn.getEquiv xs).symm

def boundedComplement (s : ℕ) (hs : s < 17) (k : Fin 17) : Fin 17 :=
  ⟨if k.val ≤ s then s - k.val else k.val, by
    split_ifs
    · exact lt_of_le_of_lt (Nat.sub_le _ _) hs
    · exact k.isLt⟩

theorem boundedComplement_involutive (s : ℕ) (hs : s < 17) :
    Function.Involutive (boundedComplement s hs) := by
  intro k
  apply Fin.ext
  dsimp only [boundedComplement]
  split_ifs <;> omega

def boundedComplementEquiv (s : ℕ) (hs : s < 17) : Equiv.Perm (Fin 17) where
  toFun := boundedComplement s hs
  invFun := boundedComplement s hs
  left_inv := boundedComplement_involutive s hs
  right_inv := boundedComplement_involutive s hs

end MatrixMultiplication.AllFieldNativeGroupedRates

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_Construction_OrderedLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

open scoped BigOperators
open MatrixMultiplication.Foundation
open MatrixMultiplication.CommonDimensions

namespace MatrixMultiplication.AllFieldStageCRegroup

attribute [local instance] Classical.propDecidable Classical.decEq

variable {H B W F : Type*}

abbrev Positions (count : H → B → Bool → ℕ) (h : H) :=
  Σ b : B, Fin (count h b false)

abbrev PairedWords (count : H → B → Bool → ℕ) (W : Type*) :=
  ∀ h, Positions count h → W × W

abbrev SplitWords (count : H → B → Bool → ℕ) (W : Type*) :=
  ∀ h b r, Fin (count h b r) → W

def unpair (count : H → B → Bool → ℕ)
    (hc : ∀ h b r, count h b r = count h b false)
    (x : PairedWords count W) : SplitWords count W :=
  fun h b r i =>
    if r then (x h ⟨b, Fin.cast (hc h b r) i⟩).2
    else (x h ⟨b, Fin.cast (hc h b r) i⟩).1

variable [Fintype H] [Fintype B] [CommSemiring F]

theorem prod_fin_cast {m n : ℕ} (e : m = n) (f : Fin n → F) :
    (∏ i : Fin m, f (Fin.cast e i)) = ∏ i : Fin n, f i := by
  subst n
  rfl

end MatrixMultiplication.AllFieldStageCRegroup

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldStageCFinish

open MatrixMultiplication.Foundation AllFieldHistory AllFieldParameters
open CWStageCProducts
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K : ℕ}
  (dilation : ℕ)

abbrev SingleWord := Fin 1 → Fin 7

end MatrixMultiplication.AllFieldStageCFinish

end
end

end MatrixAllFields

end OAI
end


