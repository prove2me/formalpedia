-- Prove2me | Definitions.Def_OAIQ247J005
-- name    : OAIQ247J005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T18:40:32.938268+00:00
-- url     : https://prove2.me/theorems/ab16fd9e-5a1d-46df-81c3-98b54bca0c49
-- title:
--   Definitions bundle OAIQ247J005 of the split of OpenAI, A quadratic bound for Jacobsthal's function (result family 21)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Erdos970.Erdos970Final.erdos_970_iterated_log`, carved from OpenAI's openai/math development (OpenAI, *A quadratic bound for Jacobsthal's function (result family 21)*, OpenAI Math Release, September 25, 2026, result family 21, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 189 declarations of OpenAI's Lean: 59 definitions, 15 instances and 115 theorems. The definitions and types are `Erdos970.Mertens.LogZetaInteg.c`, `Erdos970.Mertens.LogZetaInteg.f`, `OAI.Erdos970.WeightedTorusJets.Geometry.relativeLocalizationFractionAlgebra`, `OAI.Erdos970.WeightedTorusJets.Geometry.torusEvalOne`, `OAI.Erdos970.WeightedTorusJets.Geometry.torusIdentityPoint`, `OAI.Erdos970.WeightedTorusJets.LinearNormalization.eliminationBaseHom`, `OAI.Erdos970.WeightedTorusJets.LinearNormalization.eliminationEquiv`, `OAI.Erdos970.WeightedTorusJets.LinearNormalization.eliminationHom`, `OAI.Erdos970.WeightedTorusJets.LinearNormalization.eliminationIdeal`, `OAI.Erdos970.WeightedTorusJets.LinearNormalization.eliminationQuotientEquiv`, `OAI.Erdos970.WeightedTorusJets.LinearNormalization.linearShear`, `OAI.Erdos970.WeightedTorusJets.LinearNormalization.linearShearHom`, `OAI.Erdos970.WeightedTorusJets.Mertens.E₁`, `OAI.Erdos970.WeightedTorusJets.Mertens.E₁p`, `OAI.Erdos970.WeightedTorusJets.Mertens.E₁Λ`, `OAI.Erdos970.WeightedTorusJets.affineFractionFieldAlgEquiv`, `OAI.Erdos970.WeightedTorusJets.biquadraticBasis`, `OAI.Erdos970.WeightedTorusJets.biquadraticCoefficients`, `OAI.Erdos970.WeightedTorusJets.biquadraticDirectionBasis`, `OAI.Erdos970.WeightedTorusJets.biquadraticDirections`, `OAI.Erdos970.WeightedTorusJets.biquadraticForm`, `OAI.Erdos970.WeightedTorusJets.biquadraticLinearMap`, `OAI.Erdos970.WeightedTorusJets.biquadraticSignEquiv`, `OAI.Erdos970.WeightedTorusJets.characterField`, `OAI.Erdos970.WeightedTorusJets.coefficientSubspaceEquiv`, `OAI.Erdos970.WeightedTorusJets.conductorCompletedL`, `OAI.Erdos970.WeightedTorusJets.crtCharacterLeft`, `OAI.Erdos970.WeightedTorusJets.crtCharacterRight`, `OAI.Erdos970.WeightedTorusJets.crtUnits`, `OAI.Erdos970.WeightedTorusJets.cyclotomicDivisorField`, `OAI.Erdos970.WeightedTorusJets.dominantFunctionFieldAlgHom`, `OAI.Erdos970.WeightedTorusJets.dominantFunctionFieldHom`, `OAI.Erdos970.WeightedTorusJets.extendFiniteFamily`, `OAI.Erdos970.WeightedTorusJets.finiteGreedyPivots`, `OAI.Erdos970.WeightedTorusJets.genericNormalization`, `OAI.Erdos970.WeightedTorusJets.genericNormalizationMap`, `OAI.Erdos970.WeightedTorusJets.greedyPivots`, `OAI.Erdos970.WeightedTorusJets.homogeneousMonomialBasis`, `OAI.Erdos970.WeightedTorusJets.integerCharacter`, `OAI.Erdos970.WeightedTorusJets.macaulayColumn` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Erdos970_MertensClassical`, `Jacobsthal_Siegel_BiquadraticBasis`, `Jacobsthal_Siegel_CoefficientSubspaceEquiv`, `Jacobsthal_Siegel_ConductorCompletedL`, `Jacobsthal_Siegel_DerivationJet`, `Jacobsthal_Siegel_DominantFunctionFieldHom`, `Jacobsthal_Siegel_E`, `Jacobsthal_Siegel_GenericNormalization`, `Jacobsthal_Siegel_GreedyPivots`, `Jacobsthal_Siegel_HomogeneousDeformation`, `Jacobsthal_Siegel_IntegerCharacter`, `Jacobsthal_Siegel_InvariantJetLinearMap`, `Jacobsthal_Siegel_LaurentEvalOne`, `Jacobsthal_Siegel_LinearShearHom`, `Jacobsthal_Siegel_ParameterIdeal`, `Jacobsthal_Siegel_PolynomialLaurent`, `Jacobsthal_Siegel_PolynomialLinearCoefficients`, `Jacobsthal_Siegel_QuadraticAdjoinBasis`, `Jacobsthal_Siegel_RestrictWeightSortedEquiv`, `Jacobsthal_Siegel_SqrtPairFrobeniusDirections`, `Jacobsthal_Siegel_SqrtTwoField`, `Jacobsthal_Siegel_TorusEvalOne`, `Jacobsthal_Siegel_WeightedJetIndices`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ247J007`; the statements `OAI_Erdos970_WeightedTorusJets_Geometry_source_local_torus_rectangle_graded_length_gt_jb247`, `OAI_Erdos970_WeightedTorusJets_Geometry_uniform_rectangular_multiplicity_jb247`, `OAI.Erdos970.WeightedTorusJets.characterField_changeLevel_discr_natAbs_jb247`, `OAI.Erdos970.WeightedTorusJets.conductorCompletedL_hadamard_factorization_jb247`, `OAI.Erdos970.WeightedTorusJets.conductorCompletedL_logDeriv_hasSum_jb247`, `OAI_Erdos970_WeightedTorusJets_conductorCompletedL_zeroIndex_summable_inv_sq_jb247`, `OAI_Erdos970_WeightedTorusJets_real_zero_le_conductorCompletedL_logDeriv_jb247`, `OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247`, `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_divisibility_jb247`, `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_full_local_bounds_jb247` and `OAI.Erdos970.WeightedTorusJets.source_character_global_greedy_determinant_local_bounds_jb247`; the proofs of `Erdos970.Mertens.LogZetaInteg.log_zeta_eq_integ_aux_jb247`, `OAI.Erdos970.Erdos970Dependency.SiegelWalfisz.exists_primitive_real_zero_free_disk_jb247`, `OAI_Erdos970_WeightedTorusJets_Geometry_source_local_torus_rectangle_graded_length_gt_jb247`, `OAI.Erdos970.WeightedTorusJets.Geometry.torus_prime_residue_logarithmicForm_ne_zero_jb247`, `OAI.Erdos970.WeightedTorusJets.characterField_changeLevel_discr_natAbs_jb247`, `OAI.Erdos970.WeightedTorusJets.conductorCompletedL_hadamard_factorization_jb247`, `OAI.Erdos970.WeightedTorusJets.conductorCompletedL_logDeriv_hasSum_jb247`, `OAI_Erdos970_WeightedTorusJets_conductorCompletedL_zeroIndex_summable_inv_sq_jb247`, `OAI.Erdos970.WeightedTorusJets.good_prime_mass_of_primebias_jb247`, `OAI.Erdos970.WeightedTorusJets.source_biquadratic_arithmetic_of_field_ne_jb247`, `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_divisibility_jb247`, `OAI_Erdos970_WeightedTorusJets_source_character_global_greedy_determinant_full_local_bounds_jb247` and `OAI.Erdos970.WeightedTorusJets.source_character_global_greedy_determinant_local_bounds_jb247`.
-- source:
--   OpenAI, A quadratic bound for Jacobsthal's function (result family 21), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 21; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-quadratic-bound-for-Jacobsthals-function-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Mathlib
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic

section
-- module Solutions.OAIQ247_JB.Compat
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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ247_JB.Erdos970_MertensClassical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

namespace Erdos970

namespace Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics _root_.Topology
open _root_.ArithmeticFunction hiding log

attribute [fun_prop] measurable_from_top

section
open _root_.MeasureTheory _root_.Set

namespace LogZetaInteg

noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] lemma c_zero : c 0 = 0 := by simp [c]
@[simp] lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

end LogZetaInteg
end

end Mertens

end Erdos970
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_BiquadraticBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
namespace WeightedTorusJets

theorem finrank_sup_quadratic {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) (hK : Module.finrank F K = 2)
    (hL : Module.finrank F L = 2) (hne : K ≠ L) :
    Module.finrank F ↥(K ⊔ L) = 4 := by
  have : FiniteDimensional F K := Module.finite_of_finrank_eq_succ hK
  have : FiniteDimensional F L := Module.finite_of_finrank_eq_succ hL
  have hle : Module.finrank F ↥(K ⊔ L) ≤ 4 := by
    simpa [hK, hL] using K.finrank_sup_le L
  have hdiv : 2 ∣ Module.finrank F ↥(K ⊔ L) := by
    simpa [hK] using IntermediateField.finrank_dvd_of_le_right
      (show K ≤ K ⊔ L from le_sup_left)
  have hlt : 2 < Module.finrank F ↥(K ⊔ L) := by
    by_contra hc
    have hKeq : K = K ⊔ L := IntermediateField.eq_of_le_of_finrank_le le_sup_left
      (by omega)
    have hLK : L ≤ K := hKeq.symm ▸ le_sup_right
    have hLK_eq : L = K := IntermediateField.eq_of_le_of_finrank_le hLK (by omega)
    exact hne hLK_eq.symm
  omega

theorem span_pair_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (d : F) (ha : a ^ 2 = algebraMap F E d) :
    Submodule.span F ({1, a} : Set E) = (Algebra.adjoin F {a}).toSubmodule := by
  have heval : Polynomial.aeval a (Polynomial.X ^ 2 - Polynomial.C d) = 0 := by
    simpa using sub_eq_zero.mpr ha
  have h := Submodule.span_range_natDegree_eq_adjoin
    (Polynomial.monic_X_pow_sub_C d (by decide : 2 ≠ 0)) heval
  simpa [Finset.range_add_one, Set.pair_comm] using h

theorem span_biquadratic_monomials {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) :
    Submodule.span F (Set.range ![1, a, b, a * b]) =
      (Algebra.adjoin F ({a, b} : Set E)).toSubmodule := by
  have hsets : ({1, a} : Set E) * ({1, b} : Set E) = Set.range ![1, a, b, a * b] := by
    ext x
    simp only [Set.mem_mul, Matrix.range_cons, Matrix.range_empty, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
    aesop
  rw [← hsets, ← Submodule.span_mul_span, span_pair_sqrt a d ha,
    span_pair_sqrt b e hb, ← Algebra.adjoin_union_coe_submodule]
  simp [Set.pair_comm]

noncomputable def biquadraticBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e)
    (hgen : Algebra.adjoin F ({a, b} : Set E) = ⊤)
    (hdim : Module.finrank F E = 4) : Module.Basis (Fin 4) F E :=
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ hdim
  basisOfTopLeSpanOfCardEqFinrank ![1, a, b, a * b]
    (by rw [span_biquadratic_monomials a b d e ha hb, hgen]; rfl)
    (by simpa using hdim.symm)

@[simp]
theorem biquadraticBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e)
    (hgen : Algebra.adjoin F ({a, b} : Set E) = ⊤)
    (hdim : Module.finrank F E = 4) (i : Fin 4) :
    biquadraticBasis a b d e ha hb hgen hdim i = ![1, a, b, a * b] i := by
  simp [biquadraticBasis]

theorem finrank_adjoin_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (d : F) (ha : a ^ 2 = algebraMap F E d) (hd : ¬ IsSquare d) :
    Module.finrank F (IntermediateField.adjoin F {a}) = 2 := by
  have hai : IsIntegral F a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_algebraMap)
  have : FiniteDimensional F (IntermediateField.adjoin F {a}) :=
    IntermediateField.adjoin.finiteDimensional hai
  have hpos := Module.finrank_pos (R := F) (M := IntermediateField.adjoin F {a})
  have hne : Module.finrank F (IntermediateField.adjoin F {a}) ≠ 1 := by
    intro hone
    have hamem := IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hone
    obtain ⟨r, hr⟩ := (IntermediateField.mem_bot).mp hamem
    apply hd
    refine ⟨r, ?_⟩
    apply (algebraMap F E).injective
    simpa [map_mul, hr, sq] using ha.symm
  have hle : Module.finrank F (IntermediateField.adjoin F {a}) ≤ 2 := by
    rw [← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hai.isAlgebraic]
    change Module.finrank F (Algebra.adjoin F {a}).toSubmodule ≤ 2
    rw [← span_pair_sqrt a d ha]
    have h := finrank_range_le_card (R := F) ![(1 : E), a]
    change Module.finrank F (Submodule.span F (Set.range ![(1 : E), a])) ≤ 2 at h
    rwa [Matrix.range_cons_cons_empty] at h
  omega

theorem adjoin_pair_generators {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) :
    let K := IntermediateField.adjoin F ({a, b} : Set E)
    let a' : K := ⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩
    let b' : K := ⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩
    Algebra.adjoin F ({a', b'} : Set K) = ⊤ := by
  dsimp only
  let K := IntermediateField.adjoin F ({a, b} : Set E)
  let a' : K := ⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩
  let b' : K := ⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩
  have hai : IsIntegral F a' := IsIntegral.of_pow (by decide : 0 < 2)
    (by have h : a' ^ 2 = algebraMap F K d := Subtype.ext ha
        rw [h]; exact isIntegral_algebraMap)
  have hbi : IsIntegral F b' := IsIntegral.of_pow (by decide : 0 < 2)
    (by have h : b' ^ 2 = algebraMap F K e := Subtype.ext hb
        rw [h]; exact isIntegral_algebraMap)
  apply Algebra.adjoin_eq_top_of_intermediateField
    (by intro x hx; rcases hx with rfl | rfl
        · exact hai.isAlgebraic
        · exact hbi.isAlgebraic)
  apply IntermediateField.map_injective K.val
  simp only [IntermediateField.adjoin_map, Set.image_pair, IntermediateField.val_mk]
  ext x
  simp [IntermediateField.mem_map, K]

theorem finrank_adjoin_pair_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) :
    Module.finrank F (IntermediateField.adjoin F ({a, b} : Set E)) = 4 := by
  rw [← Set.singleton_union, IntermediateField.adjoin_union]
  exact finrank_sup_quadratic _ _ (finrank_adjoin_sqrt a d ha hd)
    (finrank_adjoin_sqrt b e hb he) hne

noncomputable def sqrtPairBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) :
    Module.Basis (Fin 4) F (IntermediateField.adjoin F ({a, b} : Set E)) :=
  let a' := (⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩ :
    IntermediateField.adjoin F ({a, b} : Set E))
  let b' := (⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩ :
    IntermediateField.adjoin F ({a, b} : Set E))
  biquadraticBasis a' b' d e (Subtype.ext ha) (Subtype.ext hb)
    (adjoin_pair_generators a b d e ha hb)
    (finrank_adjoin_pair_sqrt a b d e ha hb hd he hne)

@[simp]
theorem coe_sqrtPairBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) (i : Fin 4) :
    (sqrtPairBasis a b d e ha hb hd he hne i : E) = ![1, a, b, a * b] i := by
  fin_cases i <;> simp [sqrtPairBasis]



open Module

variable {K : Type*} [Field K] [Algebra ℚ K]

noncomputable def biquadraticLinearMap (v : Basis (Fin 4) ℚ K) (a' b' : K) : K →ₗ[ℚ] K :=
  v.constr ℚ ![1, a', b', a' * b']

lemma biquadraticLinearMap_basis (v : Basis (Fin 4) ℚ K) (a' b' : K) (i : Fin 4) :
    biquadraticLinearMap v a' b' (v i) = ![1, a', b', a' * b'] i :=
  v.constr_basis ℚ _ i

lemma biquadraticLinearMap_mul (v : Basis (Fin 4) ℚ K) (a b a' b' : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (ha' : a' * a' = algebraMap ℚ K d) (hb' : b' * b' = algebraMap ℚ K e) :
    ∀ x y, biquadraticLinearMap v a' b' (x * y) =
      biquadraticLinearMap v a' b' x * biquadraticLinearMap v a' b' y := by
  let f := biquadraticLinearMap v a' b'
  have hf (i : Fin 4) : f (![1, a, b, a * b] i) = ![1, a', b', a' * b'] i := by
    rw [← hv i]
    exact biquadraticLinearMap_basis v a' b' i
  have hf1 : f 1 = 1 := hf 0
  have hfa : f a = a' := hf 1
  have hfb : f b = b' := hf 2
  have hfab : f (a * b) = a' * b' := hf 3
  have hfc (c : ℚ) (x : K) : f ((algebraMap ℚ K c) * x) = (algebraMap ℚ K c) * f x := by
    simpa only [Algebra.smul_def] using f.map_smul c x
  have hfq (c : ℚ) : f (algebraMap ℚ K c) = algebraMap ℚ K c := by simpa [hf1] using hfc c 1
  have h1 : a * (a * b) = (algebraMap ℚ K d) * b := by rw [← mul_assoc, ha]
  have h2 : b * (a * b) = (algebraMap ℚ K e) * a := by rw [mul_left_comm, hb, mul_comm]
  have h3 : (a * b) * (a * b) = (algebraMap ℚ K (d * e)) := by
    rw [mul_mul_mul_comm, ha, hb, map_mul]
  have h1' : a' * (a' * b') = (algebraMap ℚ K d) * b' := by rw [← mul_assoc, ha']
  have h2' : b' * (a' * b') = (algebraMap ℚ K e) * a' := by rw [mul_left_comm, hb', mul_comm]
  have h3' : (a' * b') * (a' * b') = (algebraMap ℚ K (d * e)) := by
    rw [mul_mul_mul_comm, ha', hb', map_mul]
  apply (LinearMap.map_mul_iff f).mpr
  apply v.ext
  intro i
  apply v.ext
  intro j
  change f (v i * v j) = f (v i) * f (v j)
  rw [hv i, hv j]
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals simp_all [mul_comm]

noncomputable def biquadraticSignEquiv (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t : Bool) : K ≃ₐ[ℚ] K := by
  let a' := if s then -a else a
  let b' := if t then -b else b
  let f := biquadraticLinearMap v a' b'
  have hf (i : Fin 4) : f (![1, a, b, a * b] i) = ![1, a', b', a' * b'] i := by
    rw [← hv i]
    exact biquadraticLinearMap_basis v a' b' i
  have hf1 : f 1 = 1 := hf 0
  have hfa : f a = a' := hf 1
  have hfb : f b = b' := hf 2
  have hfab : f (a * b) = a' * b' := hf 3
  have hcomp : f.comp f = LinearMap.id := by
    apply v.ext
    intro i
    change f (f (v i)) = v i
    rw [hv i]
    cases s <;> cases t <;> fin_cases i <;> simp_all [a', b']
  have hinv : Function.Involutive f := fun x => LinearMap.congr_fun hcomp x
  refine AlgEquiv.ofLinearEquiv (LinearEquiv.ofInvolutive f hinv) hf1 ?_
  apply biquadraticLinearMap_mul v a b a' b' d e hv ha hb
  · cases s <;> simpa [a'] using ha
  · cases t <;> simpa [b'] using hb

end WeightedTorusJets

open scoped NumberField

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_HomogeneousDeformation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section

open scoped BigOperators

namespace WeightedTorusJets

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

noncomputable def macaulayColumn (d n : ℕ) (G : σ → MvPolynomial σ R)
    (hG : ∀ i, (G i).IsHomogeneous d)
    (b : σ × {b : σ →₀ ℕ // b.degree + d = n}) : homogeneousSubmodule σ R n :=
  ⟨monomial b.2.1 1 * G b.1, by
    change (monomial b.2.1 (1 : R) * G b.1).IsHomogeneous n
    simpa only [b.2.2] using
      (isHomogeneous_monomial (d := b.2.1) (1 : R) rfl).mul (hG b.1)⟩

noncomputable def macaulayMap (d n : ℕ) (G : σ → MvPolynomial σ R)
    (hG : ∀ i, (G i).IsHomogeneous d) :
    ((σ × {b : σ →₀ ℕ // b.degree + d = n}) →₀ R) →ₗ[R]
      homogeneousSubmodule σ R n :=
  Finsupp.linearCombination R (macaulayColumn d n G hG)

noncomputable def macaulayMatrix (d n : ℕ) (G : σ → MvPolynomial σ R) :
    Matrix {a : σ →₀ ℕ // a.degree = n}
      (σ × {b : σ →₀ ℕ // b.degree + d = n}) R :=
  fun a b => (monomial b.2.1 1 * G b.1).coeff a.1

end WeightedTorusJets

open Module

namespace WeightedTorusJets

@[instance_reducible] noncomputable def monomialDegreeFintype (σ : Type*) [Finite σ] (n : ℕ) :
    Fintype {m : σ →₀ ℕ // m.degree = n} :=
  (Finsupp.finite_of_degree_eq n).fintype

@[instance_reducible] noncomputable def monomialSourceFintype (σ : Type*) [Finite σ] (n d : ℕ) :
    Fintype {m : σ →₀ ℕ // m.degree + d = n} :=
  ((Finsupp.finite_of_degree_le n).subset (fun m hm => by
    change m.degree + d = n at hm
    change m.degree ≤ n
    omega)).fintype

noncomputable def homogeneousMonomialBasis (σ R : Type*) [CommSemiring R] (n : ℕ) :
    Basis {m : σ →₀ ℕ // m.degree = n} R (MvPolynomial.homogeneousSubmodule σ R n) :=
  (MvPolynomial.basisRestrictSupport R {m : σ →₀ ℕ | m.degree = n}).map
    (LinearEquiv.ofEq _ _
      (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := σ) (R := R) n).symm)

end WeightedTorusJets

open MvPolynomial

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_CoefficientSubspaceEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
namespace WeightedTorusJets

variable {K A M ι : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower K A M] [Fintype ι]

noncomputable def coefficientSubspaceEquiv (C : Submodule K A) (P : Submodule K M)
    (v : ι → M) (hv : LinearIndependent A v)
    (hmem : ∀ c : ι → C, ∑ i, (c i : A) • v i ∈ P)
    (hrep : ∀ y ∈ P, ∃ c : ι → C, ∑ i, (c i : A) • v i = y) :
    (ι → C) ≃ₗ[K] P := by
  let f : (ι → C) →ₗ[K] M :=
    ((Fintype.linearCombination A v).restrictScalars K).comp
      (LinearMap.pi fun i => C.subtype.comp (LinearMap.proj i))
  refine LinearEquiv.ofBijective (f.codRestrict P hmem) ⟨?_, ?_⟩
  · intro c d hcd
    have heq : ∑ i, (c i : A) • v i = ∑ i, (d i : A) • v i :=
      congrArg Subtype.val hcd
    funext i
    exact Subtype.ext (hv.eq_coords_of_eq heq i)
  · intro y
    obtain ⟨c, hc⟩ := hrep y y.property
    exact ⟨c, Subtype.ext hc⟩

@[simp]
theorem coefficientSubspaceEquiv_apply (C : Submodule K A) (P : Submodule K M)
    (v : ι → M) (hv : LinearIndependent A v)
    (hmem : ∀ c : ι → C, ∑ i, (c i : A) • v i ∈ P)
    (hrep : ∀ y ∈ P, ∃ c : ι → C, ∑ i, (c i : A) • v i = y) (c : ι → C) :
    (coefficientSubspaceEquiv C P v hv hmem hrep c : M) = ∑ i, (c i : A) • v i :=
  rfl

end WeightedTorusJets

open scoped BigOperators DirectSum

open scoped BigOperators

end

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ConductorCompletedL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section
open _root_.Filter _root_.Set _root_.MeasureTheory
open scoped Topology
open _root_.Filter _root_.Set _root_.Asymptotics
namespace WeightedTorusJets

open _root_.Complex DirichletCharacter

variable {q : ℕ} [NeZero q]

noncomputable def conductorCompletedL (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s / 2) * completedLFunction χ s

end WeightedTorusJets

end
end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LinearShearHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section

namespace WeightedTorusJets.LinearNormalization

open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ}

noncomputable def linearShearHom (c : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  aeval (Fin.cases (X 0) (fun i => X i.succ + C (c i) * X 0))

@[simp] theorem linearShearHom_X_succ (c : Fin n → K) (i : Fin n) :
    linearShearHom c (X i.succ) = X i.succ + C (c i) * X 0 := by
  simp [linearShearHom]

theorem linearShearHom_comp_neg (c : Fin n → K) :
    (linearShearHom c).comp (linearShearHom (-c)) = AlgHom.id K _ := by
  ext i
  cases i using Fin.cases <;> simp [map_add, map_mul, linearShearHom]

noncomputable def linearShear (c : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (linearShearHom c) (linearShearHom (-c))
    (linearShearHom_comp_neg c) (by simpa using linearShearHom_comp_neg (-c))

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal _root_.Polynomial RingHom
variable {K : Type*} [Field K] {n : ℕ}

noncomputable def eliminationEquiv (c : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  (linearShear c).trans (finSuccEquiv K n)

noncomputable def eliminationIdeal (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    Ideal (Polynomial (MvPolynomial (Fin n) K)) := I.map (eliminationEquiv c)

noncomputable def eliminationQuotientEquiv (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    (Polynomial (MvPolynomial (Fin n) K) ⧸ eliminationIdeal c I) ≃ₐ[K]
      MvPolynomial (Fin (n + 1)) K ⧸ I :=
  Ideal.quotientEquivAlg _ I (eliminationEquiv c).symm (by
    change I = Ideal.map (eliminationEquiv c).symm.toRingEquiv.toRingHom
      (Ideal.map (eliminationEquiv c).toRingEquiv.toRingHom I)
    rw [Ideal.map_map]
    have hc : (eliminationEquiv c).symm.toRingEquiv.toRingHom.comp
        (eliminationEquiv c).toRingEquiv.toRingHom = RingHom.id _ :=
      (eliminationEquiv c).toRingEquiv.symm_toRingHom_comp_toRingHom
    rw [hc, Ideal.map_id])

noncomputable def eliminationBaseHom (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    MvPolynomial (Fin n) K →ₐ[MvPolynomial (Fin n) K]
      Polynomial (MvPolynomial (Fin n) K) ⧸ eliminationIdeal c I :=
  (Ideal.Quotient.mkₐ _ _).comp (Algebra.ofId _ _)

noncomputable def eliminationHom (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K ⧸ I :=
  (eliminationQuotientEquiv c I).toAlgHom.comp
    ((eliminationBaseHom c I).restrictScalars K)

end WeightedTorusJets.LinearNormalization

namespace WeightedTorusJets.LinearNormalization
open MvPolynomial Ideal RingHom
variable {K : Type*} [Field K] {n : ℕ}

@[simp] theorem linearShear_apply_neg (c : Fin n → K)
    (f : MvPolynomial (Fin (n + 1)) K) :
    linearShear c (linearShear (-c) f) = f := by
  exact congrArg (fun h : MvPolynomial (Fin (n + 1)) K →ₐ[K]
    MvPolynomial (Fin (n + 1)) K => h f) (linearShearHom_comp_neg c)

@[simp] theorem eliminationQuotientEquiv_mk (c : Fin n → K)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (p : Polynomial (MvPolynomial (Fin n) K)) :
    eliminationQuotientEquiv c I (Ideal.Quotient.mk (eliminationIdeal c I) p) =
      Ideal.Quotient.mk I ((eliminationEquiv c).symm p) := by
  simp only [eliminationQuotientEquiv, Ideal.quotientEquivAlg_mk]

end WeightedTorusJets.LinearNormalization

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DominantFunctionFieldHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay

noncomputable section

open Module

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

local instance scheme_top_nonempty (Z : Scheme) [Nonempty Z] : Nonempty (⊤ : Z.Opens) :=
  ⟨⟨Classical.choice inferInstance, Set.mem_univ _⟩⟩

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem genericPoint_eq_of_isDominant (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have h : IsGenericPoint (f (genericPoint X)) Set.univ := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec X).image f.continuous
  exact h.eq (genericPoint_spec Y)

noncomputable def dominantFunctionFieldHom (f : X ⟶ Y) [IsDominant f] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isDominant f).symm)).hom ≫
    f.stalkMap (genericPoint X)

theorem germToFunctionField_dominantFunctionFieldHom (f : X ⟶ Y) [IsDominant f] :
    Y.germToFunctionField ⊤ ≫ dominantFunctionFieldHom f =
      f.appTop ≫ X.germToFunctionField ⊤ := by
  calc
    _ = Y.presheaf.germ ⊤ (f (genericPoint X)) (Set.mem_univ _) ≫
        f.stalkMap (genericPoint X) := by
      rw [dominantFunctionFieldHom, ← Category.assoc]
      congr 1
      exact Y.presheaf.germ_stalkSpecializes _
        (specializes_of_eq (genericPoint_eq_of_isDominant f))
    _ = _ := f.germ_stalkMap ⊤ (genericPoint X) (Set.mem_univ _)

theorem isDominant_fromSpecStalk_genericPoint (Z : Scheme.{u}) [IsIntegral Z] :
    IsDominant (Z.fromSpecStalk (genericPoint Z)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure Z]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr
    ⟨IsLocalRing.closedPoint Z.functionField, Z.fromSpecStalk_closedPoint⟩

end WeightedTorusJets

open CategoryTheory _root_.AlgebraicGeometry

open IsLocalRing

open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory

open AlgebraicGeometry TopologicalSpace CategoryTheory

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GenericNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay
noncomputable section
open Module
open CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
namespace WeightedTorusJets

universe u

variable (Y : Scheme.{u}) [IsIntegral Y] [QuasiSeparatedSpace Y]

noncomputable def genericNormalization : Scheme.{u} :=
  (Y.fromSpecStalk (genericPoint Y)).normalization

noncomputable def genericNormalizationMap : genericNormalization Y ⟶ Y :=
  (Y.fromSpecStalk (genericPoint Y)).fromNormalization

instance genericNormalization_isIntegral : IsIntegral (genericNormalization Y) := by
  dsimp only [genericNormalization]
  infer_instance

instance genericNormalizationMap_isDominant : IsDominant (genericNormalizationMap Y) := by
  apply (IsDominant.comp_iff (Y.fromSpecStalk (genericPoint Y)).toNormalization
    (Y.fromSpecStalk (genericPoint Y)).fromNormalization).mp
  simpa only [Scheme.Hom.toNormalization_fromNormalization] using
    isDominant_fromSpecStalk_genericPoint Y

end WeightedTorusJets

namespace WeightedTorusJets

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

instance dominantFunctionFieldHom_isIso (f : X ⟶ Y) [IsDominant f]
    [IsOpenImmersion f] : IsIso (dominantFunctionFieldHom f) := by
  unfold dominantFunctionFieldHom
  infer_instance

noncomputable def openImmersionFunctionFieldEquiv (f : X ⟶ Y) [IsDominant f]
    [IsOpenImmersion f] : Y.functionField ≃+* X.functionField :=
  (asIso (dominantFunctionFieldHom f)).commRingCatIsoToRingEquiv

end WeightedTorusJets

namespace WeightedTorusJets

universe u

noncomputable def schemeBaseToStalk {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) : R →+* X.presheaf.stalk x :=
  ((StructureSheaf.toStalk R (f x)) ≫ f.stalkMap x).hom

noncomputable abbrev schemeBaseStalkAlgebra {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) : Algebra R (X.presheaf.stalk x) :=
  (schemeBaseToStalk f x).toAlgebra

theorem schemeBaseToStalk_eq_global_germ {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    schemeBaseToStalk f x =
      (X.presheaf.germ ⊤ x (by simp)).hom.comp
        (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom) := by
  change (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f x) (by simp)) ≫ f.stalkMap x).hom = _
  rw [Category.assoc, f.germ_stalkMap]
  rfl

end WeightedTorusJets

namespace WeightedTorusJets

universe u

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

noncomputable def dominantFunctionFieldAlgHom (f : X ⟶ Y) [IsDominant f]
    (g : Y ⟶ Spec (CommRingCat.of k)) :
    let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
    let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
    Y.functionField →ₐ[k] X.functionField := by
  let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
  let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
  refine { (dominantFunctionFieldHom f).hom with commutes' := ?_ }
  intro c
  change dominantFunctionFieldHom f (schemeBaseToStalk g (genericPoint Y) c) =
    schemeBaseToStalk (f ≫ g) (genericPoint X) c
  rw [schemeBaseToStalk_eq_global_germ, schemeBaseToStalk_eq_global_germ]
  have hn := congrArg
    (fun h : Γ(Y, ⊤) ⟶ X.functionField ↦
      h (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom c))
    (germToFunctionField_dominantFunctionFieldHom f)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.comp_apply] using hn

end WeightedTorusJets

namespace WeightedTorusJets

universe u

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

noncomputable def openImmersionFunctionFieldAlgEquiv (f : X ⟶ Y) [IsDominant f]
    [IsOpenImmersion f] (g : Y ⟶ Spec (CommRingCat.of k)) :
    let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
    let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
    Y.functionField ≃ₐ[k] X.functionField := by
  let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
  let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
  let e := openImmersionFunctionFieldEquiv f
  exact { e with
    commutes' := (dominantFunctionFieldAlgHom f g).commutes }

noncomputable def normalizationFunctionFieldAlgHom
    (f : X ⟶ Y) [IsDominant f] [IsOpenImmersion f]
    (g : Y ⟶ Spec (CommRingCat.of k)) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
    let : Algebra k (genericNormalization Y).functionField :=
      schemeBaseStalkAlgebra (genericNormalizationMap Y ≫ g)
        (genericPoint (genericNormalization Y))
    X.functionField →ₐ[k] (genericNormalization Y).functionField := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra (f ≫ g) (genericPoint X)
  let : Algebra k (genericNormalization Y).functionField :=
    schemeBaseStalkAlgebra (genericNormalizationMap Y ≫ g)
      (genericPoint (genericNormalization Y))
  let : Algebra k Y.functionField := schemeBaseStalkAlgebra g (genericPoint Y)
  exact (dominantFunctionFieldAlgHom (genericNormalizationMap Y) g).comp
    (openImmersionFunctionFieldAlgEquiv f g).symm.toAlgHom

end WeightedTorusJets

namespace WeightedTorusJets

universe u

noncomputable instance affineFunctionFieldAlgebra (A : Type u) [CommRing A] [IsDomain A] :
    Algebra A (Spec (CommRingCat.of A)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of A)

theorem affineFunctionField_isScalarTower (k A : Type u) [CommRing k] [CommRing A]
    [IsDomain A] [Algebra k A] :
    let : Algebra k (Spec (CommRingCat.of A)).functionField :=
      schemeBaseStalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (genericPoint (Spec (CommRingCat.of A)))
    IsScalarTower k A (Spec (CommRingCat.of A)).functionField := by
  let : Algebra k (Spec (CommRingCat.of A)).functionField :=
    schemeBaseStalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (genericPoint (Spec (CommRingCat.of A)))
  apply IsScalarTower.of_algebraMap_eq'
  change schemeBaseToStalk (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (genericPoint (Spec (CommRingCat.of A))) = _
  rw [schemeBaseToStalk_eq_global_germ, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

noncomputable def affineFractionFieldAlgEquiv (k A : Type u) [CommRing k] [CommRing A]
    [IsDomain A] [Algebra k A] :
    let : Algebra k (Spec (CommRingCat.of A)).functionField :=
      schemeBaseStalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
        (genericPoint (Spec (CommRingCat.of A)))
    FractionRing A ≃ₐ[k] (Spec (CommRingCat.of A)).functionField := by
  let : Algebra k (Spec (CommRingCat.of A)).functionField :=
    schemeBaseStalkAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (genericPoint (Spec (CommRingCat.of A)))
  have : IsScalarTower k A (Spec (CommRingCat.of A)).functionField :=
    affineFunctionField_isScalarTower k A
  have : IsFractionRing A (Spec (CommRingCat.of A)).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of A)
  exact (FractionRing.algEquiv A (Spec (CommRingCat.of A)).functionField).restrictScalars k

end WeightedTorusJets

open CategoryTheory _root_.AlgebraicGeometry

open MvPolynomial HomogeneousLocalization

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

variable (k ι : Type u) [CommRing k]

noncomputable def polynomialDegreeZeroEquiv :
    k ≃ₐ[k] MvPolynomial.homogeneousSubmodule ι k 0 := by
  apply AlgEquiv.ofBijective (Algebra.ofId k (MvPolynomial.homogeneousSubmodule ι k 0))
  constructor
  · intro a b h
    apply MvPolynomial.C_injective
    exact congrArg Subtype.val h
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    change MvPolynomial.C (p.coeff 0) = p
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous ι).mpr hp)).symm

end WeightedTorusJets

namespace WeightedTorusJets

universe u

instance schemeImage_isSeparated {X Y : Scheme.{u}} (f : X ⟶ Y) [Y.IsSeparated] :
    f.image.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← CategoryTheory.Limits.terminal.comp_from f.imageι]
  infer_instance

end WeightedTorusJets

open _root_.Polynomial IsLocalRing TensorProduct

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ParameterIdeal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay
noncomputable section
open Module
open CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry
open _root_.Polynomial IsLocalRing TensorProduct
namespace WeightedTorusJets

abbrev parameterIdeal (k : Type*) [Field k] : Ideal k[X] :=
  RingHom.ker (Polynomial.evalRingHom (0 : k))

instance parameterIdeal_isPrime (k : Type*) [Field k] : (parameterIdeal k).IsPrime :=
  RingHom.ker_isPrime _

abbrev parameterRing (k : Type*) [Field k] := Localization.AtPrime (parameterIdeal k)

end WeightedTorusJets

open TensorProduct IsLocalRing

open scoped TensorProduct

open scoped BigOperators

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_TorusEvalOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section

open scoped BigOperators

namespace WeightedTorusJets.Geometry

noncomputable def torusEvalOne {K : Type*} [CommSemiring K] :
    Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) →+* K :=
  IsLocalization.Away.lift
    (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))
    (g := MvPolynomial.eval (fun _ ↦ (1 : K))) (by simp [map_prod])

@[simp] theorem torusEvalOne_algebraMap {K : Type*} [CommSemiring K]
    (F : MvPolynomial (Fin 4) K) :
    torusEvalOne (algebraMap (MvPolynomial (Fin 4) K)
      (Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))) F) =
        MvPolynomial.eval (fun _ ↦ 1) F := by
  simp [torusEvalOne]

noncomputable def torusIdentityPoint {K : Type*} [Field K] :
    PrimeSpectrum
      (Localization.Away (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K))) :=
  ⟨RingHom.ker torusEvalOne, RingHom.ker_isPrime _⟩



end WeightedTorusJets.Geometry

open scoped BigOperators

end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DerivationJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open scoped BigOperators

open scoped BigOperators

noncomputable section

namespace WeightedTorusJets.Geometry

open MvPolynomial

open MvPolynomial

theorem rectangularIdeal_le_ker_constantCoeff
    {σ K : Type*} [CommRing K] (k : σ → ℕ) (hk : ∀ i, k i ≠ 0) :
    Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ k i) ≤
      RingHom.ker (constantCoeff : MvPolynomial σ K →+* K) := by
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  change constantCoeff ((X i : MvPolynomial σ K) ^ k i) = 0
  rw [map_pow, constantCoeff_X, zero_pow (hk i)]

end WeightedTorusJets.Geometry

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_E
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section AnalyticAssemblyScope
open scoped BigOperators Topology
section

/-
Generated attribution header: the source file did not contain a copyright header.
The Mertens estimates in the following namespace are adapted from PrimeNumberTheoremAnd.IEANTN.Mertens.
Source: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/IEANTN/Mertens.lean
License: Apache License 2.0.

This code has been modified.
-/

namespace WeightedTorusJets.Mertens

open _root_.Real _root_.Finset _root_.Filter _root_.Asymptotics Topology
open _root_.ArithmeticFunction hiding log

noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

end WeightedTorusJets.Mertens

end

end AnalyticAssemblyScope
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GreedyPivots
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators

open scoped BigOperators

namespace WeightedTorusJets



open Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

noncomputable def greedyPivots
    {V : Type u_1} [AddCommGroup V] (K : Type u_2) [DivisionRing K] (v : ℕ → V)
    [Module K V] : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => by
      classical
      exact if v n ∈ span K (v '' (greedyPivots K v n : Set ℕ))
        then greedyPivots K v n else insert n (greedyPivots K v n)

end WeightedTorusJets

namespace WeightedTorusJets

def extendFiniteFamily {α : Type*} {n : ℕ} (f : Fin n → α) (fallback : α) (i : ℕ) : α :=
  if hi : i < n then f ⟨i, hi⟩ else fallback

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_IntegerCharacter
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace WeightedTorusJets

noncomputable def integerCharacter {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) : DirichletCharacter ℤ q := by
  let v : ZMod q → ℤ := fun a ↦ ⌊(χ a).re⌋
  have hv (a : ZMod q) : (v a : ℂ) = χ a := by
    rcases hquad a with h | h | h <;> norm_num [v, h]
  exact
    { toFun := v
      map_one' := by
        apply Int.cast_injective (α := ℂ)
        rw [hv, map_one, Int.cast_one]
      map_mul' := fun a b ↦ by
        apply Int.cast_injective (α := ℂ)
        rw [Int.cast_mul, hv, hv, hv, map_mul]
      map_nonunit' := fun a ha ↦ by
        apply Int.cast_injective (α := ℂ)
        rw [hv, MulChar.map_nonunit χ ha, Int.cast_zero] }

@[simp]
theorem integerCharacter_cast {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (a : ZMod q) : (integerCharacter χ hquad a : ℂ) = χ a := by
  change (⌊(χ a).re⌋ : ℂ) = χ a
  rcases hquad a with h | h | h <;> norm_num [h]



open NumberField IsCyclotomicExtension.Rat

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension.Rat

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] [IsAbelianGalois ℚ K]
    (R : Type*) [CommRing R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

noncomputable def characterField (χ : DirichletCharacter R n) : IntermediateField ℚ K :=
  (intermediateFieldEquivSubgroupChar n K R).symm (Subgroup.zpowers χ)

end WeightedTorusJets

namespace WeightedTorusJets

open NumberField IsCyclotomicExtension

noncomputable def cyclotomicDivisorField (n m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {m} ℚ L] :
    IntermediateField ℚ L :=
  IntermediateField.adjoin ℚ {zeta m ℚ L ^ (m / n)}

end WeightedTorusJets

open scoped Pointwise

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialLinearCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
noncomputable section
noncomputable section
namespace WeightedTorusJets.Geometry
open MvPolynomial

theorem rectangularIdeal_le_vars_square {σ K : Type*} [CommRing K]
    (k : σ → ℕ) (hk : ∀ i, 2 ≤ k i) :
    Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ k i) ≤ idealOfVars σ K ^ 2 := by
  rw [Ideal.span_le, Set.range_subset_iff]
  intro i
  have hi : (X i : MvPolynomial σ K) ∈ idealOfVars σ K := Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.pow_le_pow_right (hk i) (Ideal.pow_mem_pow hi (k i))

end WeightedTorusJets.Geometry

end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialLaurent
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section SamePrimeDimensionPrerequisites

namespace WeightedTorusJets.Geometry



variable {B A : Type*} [CommRing B] [CommRing A] [IsDomain A]
  [Algebra B A] [FaithfulSMul B A]

theorem relative_denominators_le_nonZeroDivisors :
    Algebra.algebraMapSubmonoid A (nonZeroDivisors B) ≤ nonZeroDivisors A :=
  map_le_nonZeroDivisors_of_injective (algebraMap B A)
    (FaithfulSMul.algebraMap_injective B A) le_rfl

noncomputable abbrev relativeLocalizationFractionAlgebra :
    Algebra (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)))
      (FractionRing A) :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) (nonZeroDivisors A)
    relative_denominators_le_nonZeroDivisors

attribute [local instance] relativeLocalizationFractionAlgebra

theorem relativeLocalizationFraction_scalarTower :
    IsScalarTower A
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)))
      (FractionRing A) :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _
    (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) (nonZeroDivisors A)
    relative_denominators_le_nonZeroDivisors

attribute [local instance] relativeLocalizationFraction_scalarTower

attribute [local instance] FractionRing.liftAlgebra

end WeightedTorusJets.Geometry

end SamePrimeDimensionPrerequisites

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_WeightedJetIndices
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
namespace WeightedTorusJets

def weightedJetIndices (H B : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 3 => Finset.range (B + 1))).filter
    (fun α => α 0 + H * α 1 + H * α 2 ≤ B)

noncomputable def finiteGreedyPivots (K : Type*) [DivisionRing K]
    {α V : Type*} [AddCommGroup V] [Module K V] (s : Finset α) (R : α → V)
    (e : Fin s.card ≃ s) (fallback : α) : Finset α := by
  classical
  let a := extendFiniteFamily (fun i => (e i : α)) fallback
  exact (greedyPivots K (R ∘ a) s.card).image a

end WeightedTorusJets

open Module
open scoped BigOperators

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_InvariantJetLinearMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open scoped BigOperators

namespace WeightedTorusJets

variable {K : Type*} [Field K]

def biquadraticDirections (a b : K) : Fin 3 → Fin 4 → K :=
  ![![1, a, b, a * b], ![1, -a, b, -(a * b)], ![1, -a, -b, a * b]]

def biquadraticCoefficients (a b : K) : Fin 4 → K :=
  ![1, a⁻¹, -b⁻¹, -(a * b)⁻¹]

def biquadraticForm (a b : K) : (Fin 4 → K) →ₗ[K] K :=
  dotProductBilin K K (biquadraticCoefficients a b)

theorem biquadraticForm_apply (a b : K) (v : Fin 4 → K) :
    biquadraticForm a b v = v 0 + a⁻¹ * v 1 - b⁻¹ * v 2 - (a * b)⁻¹ * v 3 := by
  simp [biquadraticForm, biquadraticCoefficients, dotProductBilin, dotProduct,
    Fin.sum_univ_succ, sub_eq_add_neg, add_assoc]

theorem biquadraticForm_direction {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (i : Fin 3) : biquadraticForm a b (biquadraticDirections a b i) = 0 := by
  fin_cases i <;> simp [biquadraticForm_apply, biquadraticDirections, ha, hb, mul_assoc]

theorem biquadraticDirections_linearIndependent [CharZero K] {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent K (biquadraticDirections a b) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_succ, biquadraticDirections] at h0 h1 h2
  have hc0 : c 0 = 0 := by
    apply (mul_eq_zero.mp (show 2 * a * c 0 = 0 by linear_combination a * h0 + h1)).resolve_left
    exact mul_ne_zero two_ne_zero ha
  have hc2 : c 2 = 0 := by
    apply (mul_eq_zero.mp (show 2 * b * c 2 = 0 by linear_combination b * h0 - h2)).resolve_left
    exact mul_ne_zero two_ne_zero hb
  have hc1 : c 1 = 0 := by linear_combination h0 - hc0 - hc2
  fin_cases i <;> assumption

theorem finrank_ker_biquadraticForm (a b : K) :
    Module.finrank K (LinearMap.ker (biquadraticForm a b)) = 3 := by
  have hs : Function.Surjective (biquadraticForm a b) := fun y =>
    ⟨![y, 0, 0, 0], by simp [biquadraticForm_apply]⟩
  have h := (biquadraticForm a b).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simp only [finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  exact Nat.add_left_cancel h

theorem span_biquadraticDirections_eq_ker [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Submodule.span K (Set.range (biquadraticDirections a b)) =
      LinearMap.ker (biquadraticForm a b) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact biquadraticForm_direction ha hb i
  · rw [finrank_span_eq_card (biquadraticDirections_linearIndependent ha hb),
      finrank_ker_biquadraticForm]
    rfl

noncomputable def biquadraticDirectionBasis [CharZero K] {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.Basis (Fin 3) K (LinearMap.ker (biquadraticForm a b)) :=
  (Module.Basis.span (biquadraticDirections_linearIndependent ha hb)).map
    (LinearEquiv.ofEq _ _ (span_biquadraticDirections_eq_ker ha hb))

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LaurentEvalOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace WeightedTorusJets.Geometry



open _root_.AlgebraicGeometry

variable {R : Type*} [CommRing R]

noncomputable instance spec_stalk_presheaf_algebra (p : PrimeSpectrum R) :
    Algebra R ((structurePresheafInCommRingCat R).stalk p) :=
  StructureSheaf.stalkAlgebra R p

theorem spec_stalk_isLocalRing (p : PrimeSpectrum R) :
    IsLocalRing ((Spec.structureSheaf R).presheaf.stalk p) :=
  letI : Algebra R ((structurePresheafInCommRingCat R).stalk p) := StructureSheaf.stalkAlgebra R p
  (StructureSheaf.stalkIso R p).toRingEquiv.isLocalRing

attribute [local instance] spec_stalk_isLocalRing

end WeightedTorusJets.Geometry



end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SqrtPairFrobeniusDirections
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField

open scoped NumberField

namespace WeightedTorusJets



open NumberField

theorem canonicalCyclotomicLevelNeZero (q : ℕ) [NeZero q] : NeZero (8 * q) :=
  ⟨Nat.mul_ne_zero (by decide) (NeZero.ne q)⟩
attribute [local instance] canonicalCyclotomicLevelNeZero

theorem canonicalCyclotomicExtension (n : ℕ) [NeZero n] :
    IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) := by
  let : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩
  convert CyclotomicField.isCyclotomicExtension n ℚ using 1
  all_goals try with_reducible_and_instances rfl
  exact Subsingleton.elim _ _
attribute [local instance] canonicalCyclotomicExtension

theorem canonicalCyclotomicNumberField (n : ℕ) [NeZero n] :
    NumberField (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.numberField {n} ℚ (CyclotomicField n ℚ)
attribute [local instance] canonicalCyclotomicNumberField

theorem canonicalCyclotomicAbelian (n : ℕ) [NeZero n] :
    IsAbelianGalois ℚ (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.isAbelianGalois {n} ℚ (CyclotomicField n ℚ)

attribute [local instance] canonicalCyclotomicAbelian



open NumberField IsCyclotomicExtension.Rat

end WeightedTorusJets

open scoped NumberField

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_QuadraticAdjoinBasis
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField

namespace WeightedTorusJets



noncomputable def quadraticAdjoinBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (ha : IsIntegral F a)
    (hdim : Module.finrank F (IntermediateField.adjoin F {a}) = 2) :
    Module.Basis (Fin 2) F (IntermediateField.adjoin F {a}) :=
  let pb := IntermediateField.adjoin.powerBasis ha
  pb.basis.reindex (finCongr (pb.finrank.symm.trans hdim))

@[simp]
theorem quadraticAdjoinBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (ha : IsIntegral F a)
    (hdim : Module.finrank F (IntermediateField.adjoin F {a}) = 2) (i : Fin 2) :
    quadraticAdjoinBasis a ha hdim i = ![1, IntermediateField.AdjoinSimple.gen F a] i := by
  fin_cases i <;>
    simp [quadraticAdjoinBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]



open NumberField IsCyclotomicExtension IsCyclotomicExtension.Rat

end WeightedTorusJets

namespace WeightedTorusJets

noncomputable def crtUnits {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

@[simp]
theorem crtUnits_fst {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    (crtUnits h u).1 = ZMod.unitsMap (Nat.dvd_mul_right m n) u := by
  apply Units.ext
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((RingHom.fst (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m))) (u : ZMod (m * n))

@[simp]
theorem crtUnits_snd {m n : ℕ} (h : m.Coprime n) (u : (ZMod (m * n))ˣ) :
    (crtUnits h u).2 = ZMod.unitsMap (Nat.dvd_mul_left n m) u := by
  apply Units.ext
  exact DFunLike.congr_fun (RingHom.ext_zmod
    ((RingHom.snd (ZMod m) (ZMod n)).comp (ZMod.chineseRemainder h).toRingHom)
    (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n))) (u : ZMod (m * n))

noncomputable def crtCharacterLeft {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) : DirichletCharacter R m :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    ((crtUnits h).symm.toMonoidHom.comp (MonoidHom.inl _ _)))

noncomputable def crtCharacterRight {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) : DirichletCharacter R n :=
  MulChar.ofUnitHom (χ.toUnitHom.comp
    ((crtUnits h).symm.toMonoidHom.comp (MonoidHom.inr _ _)))

@[simp]
theorem crtCharacterLeft_apply_unit {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) (u : (ZMod m)ˣ) :
    crtCharacterLeft h χ u = χ ((crtUnits h).symm (u, 1)) := by
  simp [crtCharacterLeft]

@[simp]
theorem crtCharacterRight_apply_unit {m n : ℕ} {R : Type*} [CommRing R]
    (h : m.Coprime n) (χ : DirichletCharacter R (m * n)) (u : (ZMod n)ˣ) :
    crtCharacterRight h χ u = χ ((crtUnits h).symm (1, u)) := by
  simp [crtCharacterRight]

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_SqrtTwoField
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField

namespace WeightedTorusJets

open IsCyclotomicExtension IsCyclotomicExtension.Rat

noncomputable def sourceSqrtTwoField (q : ℕ) [NeZero (8 * q)]
    (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {8 * q} ℚ L] :
    IntermediateField ℚ L :=
  let ζ := zeta (8 * q) ℚ L ^ ((8 * q) / 8)
  IntermediateField.adjoin ℚ ({ζ - ζ ^ 3} : Set L)

end WeightedTorusJets

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_RestrictWeightSortedEquiv
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
open scoped BigOperators
open scoped Pointwise
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped NumberField
open scoped BigOperators
open scoped BigOperators
open Module
open scoped BigOperators

open scoped BigOperators
open Module

namespace WeightedTorusJets



theorem weight_sorted_equiv_mem_iff_lt_card {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) (i : ℕ) :
    e i ∈ s ↔ i < s.card := by
  classical
  let t := s.map e.symm.toEmbedding
  have htmem : ∀ j, j ∈ t ↔ e j ∈ s := fun j => Finset.mem_map_equiv
  have htcard : t.card = s.card := Finset.card_map _
  have hsub : t ⊆ Finset.range s.card := by
    intro j hj
    have hlow : Finset.range (j + 1) ⊆ t := by
      intro k hk
      apply (htmem k).mpr
      apply (hs _).mpr
      exact (he (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).trans
        ((hs _).mp ((htmem j).mp hj))
    have hcard := Finset.card_le_card hlow
    rw [Finset.card_range, htcard] at hcard
    exact Finset.mem_range.mpr (Nat.lt_of_succ_le hcard)
  have ht : t = Finset.range s.card :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, htcard])
  rw [← htmem, ht, Finset.mem_range]

noncomputable def restrictWeightSortedEquiv {α : Type*}
    (s : Finset α) (w : α → ℕ) (B : ℕ) (hs : ∀ a, a ∈ s ↔ w a ≤ B)
    (e : ℕ ≃ α) (he : Monotone (fun i => w (e i))) : Fin s.card ≃ s where
  toFun i := ⟨e i, (weight_sorted_equiv_mem_iff_lt_card s w B hs e he i).mpr i.isLt⟩
  invFun a := ⟨e.symm a, (weight_sorted_equiv_mem_iff_lt_card s w B hs e he (e.symm a)).mp
    (by rw [e.apply_symm_apply]; exact a.property)⟩
  left_inv i := Fin.ext (e.symm_apply_apply i)
  right_inv a := Subtype.ext (e.apply_symm_apply a)



open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField canonicalCyclotomicAbelian

end WeightedTorusJets

open scoped BigOperators
open InnerProductSpace

end

end Erdos970

end OAI
end


