-- Prove2me | Definitions.Def_Q235MM001
-- name    : Q235MM001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:21:33.893043+00:00
-- url     : https://prove2.me/theorems/d3b262de-906c-47bc-a9b9-f16f8a3098cc
-- title:
--   Definitions bundle Q235MM001 of the split of OpenAI, Complex Matrix Multiplication Below 2.258 and Rectangular Bounds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixMultiplication.complex_alpha_gt_93_div_200` and `OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250`, carved from OpenAI's openai/math development (OpenAI, *Complex Matrix Multiplication Below 2.258 and Rectangular Bounds*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 133 declarations of OpenAI's Lean: 73 definitions, 3 inductive types or structures, 8 instances and 49 theorems. The definitions and types are `OAI.MatrixMultiplication.CompletionEntropyAlgebra.binaryEntropy`, `OAI.MatrixMultiplication.CompletionEntropyAlgebra.conditionalMixEntropy`, `OAI.MatrixMultiplication.CompletionExecution.Coordinate`, `OAI.MatrixMultiplication.CompletionExecution.Position`, `OAI.MatrixMultiplication.CompletionFiniteRealization.blocks`, `OAI.MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program.powPast`, `OAI.MatrixMultiplication.ComplexCertificates.curveG`, `OAI.MatrixMultiplication.ComplexCertificates.curveH`, `OAI.MatrixMultiplication.ComplexCertificates.curveU`, `OAI.MatrixMultiplication.ComplexCertificates.curveV`, `OAI.MatrixMultiplication.ComplexCertificates.curveZ`, `OAI.MatrixMultiplication.ComplexCertificates.reduceCurveHi`, `OAI.MatrixMultiplication.ComplexCertificates.reduceCurveLo`, `OAI.MatrixMultiplication.ComplexCertificates.reduceExpHi48`, `OAI.MatrixMultiplication.ComplexCertificates.reduceExpLo288`, `OAI.MatrixMultiplication.ComplexCertificates.reduceExpLo48`, `OAI.MatrixMultiplication.ComplexCertificates.reduceNineSevenths`, `OAI.MatrixMultiplication.ComplexCertificates.reduceNineteen`, `OAI.MatrixMultiplication.ComplexCertificates.reduceThree`, `OAI.MatrixMultiplication.ComplexCertificates.reduceTwo`, `OAI.MatrixMultiplication.ComplexCertificates.reduceZ288Lo`, `OAI.MatrixMultiplication.ComplexCertificates.reduceZ48Hi`, `OAI.MatrixMultiplication.ComplexCertificates.reduceZ48Lo`, `OAI.MatrixMultiplication.DualCompletionLaws.gibbsWeight`, `OAI.MatrixMultiplication.DualExponentBound.fixedAspect`, `OAI.MatrixMultiplication.DualProgramIndependence.slotCut`, `OAI.MatrixMultiplication.DualUniformProducts.supportWordEquiv`, `OAI.MatrixMultiplication.DualWitness.State`, `OAI.MatrixMultiplication.DualWitness.aspect`, `OAI.MatrixMultiplication.DualWitness.delta24`, `OAI.MatrixMultiplication.DualWitness.delta96`, `OAI.MatrixMultiplication.DualWitness.hiddenRate`, `OAI.MatrixMultiplication.DualWitness.initial`, `OAI.MatrixMultiplication.DualWitness.massA`, `OAI.MatrixMultiplication.DualWitness.massC`, `OAI.MatrixMultiplication.DualWitness.minus`, `OAI.MatrixMultiplication.DualWitness.normalizedHidden`, `OAI.MatrixMultiplication.DualWitness.plusA`, `OAI.MatrixMultiplication.DualWitness.plusC`, `OAI.MatrixMultiplication.DualWitness.rho24` and 36 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixMultiplication_Completion_Conditioning`, `MatrixMultiplication_Completion_EntropyAlgebra`, `MatrixMultiplication_Completion_Execution`, `MatrixMultiplication_Completion_FiniteRealization`, `MatrixMultiplication_Completion_Labels`, `MatrixMultiplication_Completion_RecursiveCompletion`, `MatrixMultiplication_Duality_CompletionIndependence`, `MatrixMultiplication_Duality_CompletionLaws`, `MatrixMultiplication_Duality_ExponentConsumer`, `MatrixMultiplication_Duality_UniformProducts`, `MatrixMultiplication_Duality_WitnessArithmetic`, `MatrixMultiplication_Duality_WitnessRecurrence`, `MatrixMultiplication_Entropy_ComplexConditionalTypeCounting`, `MatrixMultiplication_Entropy_ComplexEntropyContinuity`, `MatrixMultiplication_Entropy_ComplexFiniteEntropy`, `MatrixMultiplication_Entropy_ComplexHierarchySeparationRates`, `MatrixMultiplication_Entropy_ComplexSeparationAsymptotics`, `MatrixMultiplication_Entropy_ComplexTypeEntropy`, `MatrixMultiplication_Numerical_ComplexCertificates`, `MatrixMultiplication_Numerical_ComplexCertificatesLog`, `MatrixMultiplication_Numerical_ComplexRationalLogCertificate`, `MatrixMultiplication_Separation_ComplexRationalTypes`, `MatrixMultiplication_Tensor_ComplexBatchCeiling`, `MatrixMultiplication_Tensor_ComplexFactorialLogBounds`, `MatrixMultiplication_Tensor_ComplexLocalMaps`, `MatrixMultiplication_Tensor_ComplexTensorSymmetrization`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `Q235MM002`.
-- source:
--   OpenAI, Complex Matrix Multiplication Below 2.258 and Rectangular Bounds, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026/Complex-Matrix-Multiplication-Below-2.258-and-Rectangular-Bounds-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/LinearAlgebra at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Semicontinuity.Basic
import Std

section
-- module Solutions.Q235_MM.Compat
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
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexFiniteEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

def entropyTerm (p : ℝ) : ℝ := -p * Real.log p

def finiteEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ := ∑ a, entropyTerm (p a)

@[simp] theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]

theorem entropyTerm_mul (p q : ℝ) :
    entropyTerm (p * q) = q * entropyTerm p + p * entropyTerm q := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [entropyTerm, Real.log_mul hp hq]
  unfold entropyTerm
  ring

theorem finiteEntropy_chain {A B : Type*} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : A → B → ℝ) (hq : ∀ a, ∑ b, q a b = 1) :
    finiteEntropy (fun ab : A × B => p ab.1 * q ab.1 ab.2) =
      finiteEntropy p + ∑ a, p a * finiteEntropy (q a) := by
  simp only [finiteEntropy, Fintype.sum_prod_type, entropyTerm_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]

end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexEntropyContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open scoped Topology
open Filter

namespace MatrixMultiplication.Foundation

@[simp] theorem entropyTerm_one : entropyTerm 1 = 0 := by simp [entropyTerm]

@[fun_prop] theorem continuous_entropyTerm : Continuous entropyTerm :=
  Real.continuous_negMulLog

@[fun_prop] theorem continuous_finiteEntropy {A : Type*} [Fintype A] :
    Continuous (finiteEntropy : (A → ℝ) → ℝ) := by
  unfold finiteEntropy
  exact continuous_finsetSum _ fun value _ =>
    continuous_entropyTerm.comp (continuous_apply value)

end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Conditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {A X : Type*} [Fintype A] [Fintype X]

theorem sum_subtype_indicator (P : A → Prop) (f : A → ℝ) :
    (∑ a : {a // P a}, f a.val) = ∑ a, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

end MatrixMultiplication.CompletionLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_EntropyAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionEntropyAlgebra

open MatrixMultiplication.Foundation

def binaryEntropy (a : ℝ) : ℝ := entropyTerm a + entropyTerm (1 - a)

def conditionalMixEntropy (a : ℝ) (m : ℕ) (Hc Ho : ℝ) : ℝ :=
  ((m : ℝ) * (binaryEntropy a + a * Hc + (1 - a) * Ho) -
    binaryEntropy (a ^ m) - a ^ m * ((m : ℝ) * Hc)) / (1 - a ^ m)

end MatrixMultiplication.CompletionEntropyAlgebra

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexSeparationAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.Separation

open Filter

theorem scale_error_bound {n ε : ℝ} (hn : 2 ≤ n) (hε : 0 ≤ ε)
    (hlarge : 72 ≤ ε * n) : 10 * n + 15 ≤ ε * (n - 1) ^ 2 := by
  have hsq : n ^ 2 ≤ 4 * (n - 1) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hε
  have hlarge' := mul_le_mul_of_nonneg_right hlarge (by linarith : 0 ≤ n)
  nlinarith

theorem log_nat_prod {I : Type*} (s : Finset I) (a : I → ℕ)
    (ha : ∀ i ∈ s, 0 < a i) :
    Real.log ((∏ i ∈ s, a i : ℕ) : ℝ) = ∑ i ∈ s, Real.log (a i : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod (s := s) (f := fun i => (a i : ℝ)) fun i hi =>
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha i hi))

theorem tendsto_log_nat_prod_div_nat {I : Type*} (s : Finset I)
    {K : I → ℕ → ℕ} {H : I → ℝ}
    (hK : ∀ i ∈ s, ∀ N, 0 < K i N)
    (hpop : ∀ i ∈ s,
      Tendsto (fun N => Real.log (K i N : ℝ) / (N : ℝ)) atTop (nhds (H i))) :
    Tendsto (fun N => Real.log ((∏ i ∈ s, K i N : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (∑ i ∈ s, H i)) := by
  have hsum := tendsto_finsetSum s hpop
  apply hsum.congr
  intro N
  rw [log_nat_prod s (fun i => K i N) (fun i hi => hK i hi N)]
  simp only [div_eq_mul_inv, Finset.sum_mul]

end MatrixMultiplication.Foundation.Separation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexRationalTypes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

structure RationalLaw (A : Type*) [Fintype A] where
  mass : A → ℚ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexFactorialLogBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped Topology

noncomputable def factorialLogRemainder (n : ℕ) : ℝ :=
  Real.log (Nat.factorial n : ℝ) - ((n : ℝ) * Real.log n - n)

@[simp] theorem factorialLogRemainder_zero : factorialLogRemainder 0 = 0 := by
  simp [factorialLogRemainder]

theorem factorialLogRemainder_stirling (n : ℕ) :
    factorialLogRemainder n =
      Real.log (Stirling.stirlingSeq n) + (1 / 2 : ℝ) * Real.log (2 * n) := by
  cases n with
  | zero => simp
  | succ n =>
    have h := Stirling.log_stirlingSeq_formula (n + 1)
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _), Real.log_exp] at h
    unfold factorialLogRemainder
    linarith

theorem tendsto_factorialLogRemainder_div :
    Tendsto (fun n : ℕ => factorialLogRemainder n / (n : ℝ)) atTop (𝓝 0) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hstirling :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
        atTop (𝓝 0) :=
    (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).div_atTop hnat
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hconstant : Tendsto (fun n : ℕ => Real.log 2 / (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have hsum : Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * (Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using hstirling.add ((hconstant.add hlog).const_mul (1 / 2 : ℝ))
  apply hsum.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
  rw [factorialLogRemainder_stirling,
    Real.log_mul (by norm_num) (Nat.cast_ne_zero.mpr hn)]
  ring

theorem tendsto_factorialLogRemainder_mul_div (c : ℕ) :
    Tendsto (fun t : ℕ => factorialLogRemainder (t * c) / (t : ℝ))
      atTop (𝓝 0) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hmul : Tendsto (fun t : ℕ => t * c) atTop atTop :=
    tendsto_id.atTop_mul_const' (Nat.pos_of_ne_zero hc)
  have hscaled : Tendsto
      (fun t : ℕ => factorialLogRemainder (t * c) / (t * c : ℕ) * (c : ℝ))
      atTop (𝓝 0) := by
    simpa using (tendsto_factorialLogRemainder_div.comp hmul).mul_const (c : ℝ)
  apply hscaled.congr
  intro t
  by_cases ht : t = 0
  · simp [ht]
  rw [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr hc, Nat.cast_ne_zero.mpr ht]

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexTypeEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

variable {A : Type*} [Fintype A]

theorem log_multinomial (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      Real.log (Nat.factorial (∑ a, counts a) : ℝ) -
        ∑ a, Real.log (Nat.factorial (counts a) : ℝ) := by
  have hspec :
      (∏ a, (Nat.factorial (counts a) : ℝ)) *
          (Nat.multinomial Finset.univ counts : ℝ) =
        (Nat.factorial (∑ a, counts a) : ℝ) := by
    exact_mod_cast Nat.multinomial_spec Finset.univ counts
  have hprod : (∏ a, (Nat.factorial (counts a) : ℝ)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => by positivity)
  have hmulti : (Nat.multinomial Finset.univ counts : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ counts))
  have hlog := congrArg Real.log hspec
  rw [Real.log_mul hprod hmulti,
    Real.log_prod (s := Finset.univ) (f := fun a => (Nat.factorial (counts a) : ℝ))
      (fun a _ => by positivity)] at hlog
  linarith

theorem entropyTerm_div_scalar (x y : ℝ) :
    entropyTerm (x / y) = entropyTerm x / y + (x / y) * Real.log y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [entropyTerm, Real.log_div hx hy]
  unfold entropyTerm
  ring

theorem finiteEntropy_nat_normalize (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) =
      Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) /
          (∑ a, counts a : ℕ) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  unfold finiteEntropy
  simp only [entropyTerm_div_scalar]
  simp only [entropyTerm, neg_mul,
    Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_neg_distrib]
  rw [← Nat.cast_sum, div_self hD']
  ring

theorem log_multinomial_eq_main_add_remainder (counts : A → ℕ) :
    Real.log (Nat.multinomial Finset.univ counts : ℝ) =
      (∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
        (∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (∑ a, counts a) -
        ∑ a, factorialLogRemainder (counts a) := by
  rw [log_multinomial]
  unfold factorialLogRemainder
  simp only [Finset.sum_sub_distrib, ← Nat.cast_sum]
  ring

theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) =
      (x * Real.log x) * y + x * (y * Real.log y) := by
  calc
    (x * y) * Real.log (x * y) = -entropyTerm (x * y) := by
      simp [entropyTerm]
    _ = -(y * entropyTerm x + x * entropyTerm y) := by
      rw [entropyTerm_mul]
    _ = (x * Real.log x) * y + x * (y * Real.log y) := by
      unfold entropyTerm
      ring

theorem log_multinomial_mul_eq (counts : A → ℕ) (t : ℕ) :
    Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) =
      (t : ℝ) *
          ((∑ a, counts a : ℕ) * Real.log (∑ a, counts a : ℕ) -
            ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ)) +
        factorialLogRemainder (t * ∑ a, counts a) -
        ∑ a, factorialLogRemainder (t * counts a) := by
  have hsum : (∑ a, t * counts a) = t * ∑ a, counts a :=
    (Finset.mul_sum Finset.univ counts t).symm
  have hlogs :
      (∑ a, ((t : ℝ) * counts a) * Real.log ((t : ℝ) * counts a)) =
        ((t : ℝ) * Real.log t) * (∑ a, counts a : ℕ) +
          (t : ℝ) * ∑ a, (counts a : ℝ) * Real.log (counts a : ℝ) := by
    simp only [mul_log_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Nat.cast_sum]
  rw [log_multinomial_eq_main_add_remainder, hsum]
  simp only [Nat.cast_mul]
  rw [mul_log_mul, hlogs]
  ring

theorem tendsto_log_multinomial_mul (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun a => t * counts a) : ℝ) /
          ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD)
  have hsum :
      Tendsto (fun t : ℕ => ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ))
        atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ
      (fun a _ => tendsto_factorialLogRemainder_mul_div (counts a))
  have herror : Tendsto
      (fun t : ℕ =>
        (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
          ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
            (∑ a, counts a : ℕ)) atTop (𝓝 0) := by
    simpa using ((tendsto_factorialLogRemainder_mul_div (∑ a, counts a)).sub
      hsum).div_const (∑ a, counts a : ℕ)
  have hlimit : Tendsto
      (fun t : ℕ =>
        finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) +
          (factorialLogRemainder (t * ∑ a, counts a) / (t : ℝ) -
            ∑ a, factorialLogRemainder (t * counts a) / (t : ℝ)) /
              (∑ a, counts a : ℕ))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  apply hlimit.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  rw [log_multinomial_mul_eq, finiteEntropy_nat_normalize counts hD,
    ← Finset.sum_div]
  have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
  field_simp [ht', hD']
  ring

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexConditionalTypeCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A B I : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

omit [DecidableEq A] [DecidableEq B] in
theorem multinomial_prod_counts (counts : A × B → ℕ) :
    Nat.multinomial Finset.univ counts =
      Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
        ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b)) := by
  apply Nat.mul_left_cancel (Nat.prod_factorial_pos Finset.univ counts)
  rw [Nat.multinomial_spec]
  symm
  calc
    (∏ ab, (counts ab).factorial) *
        (Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) =
        ((∏ a, ∏ b, (counts (a, b)).factorial) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Fintype.prod_prod_type]
      ac_rfl
    _ = (∏ a, ((∏ b, (counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun b => counts (a, b)))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ a, (∑ b, counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact Nat.multinomial_spec Finset.univ (fun b => counts (a, b))
    _ = (∑ a, ∑ b, counts (a, b)).factorial :=
      Nat.multinomial_spec Finset.univ (fun a => ∑ b, counts (a, b))
    _ = (∑ ab, counts ab).factorial := by rw [Fintype.sum_prod_type]

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexLocalMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation
namespace LocalMaps

open scoped BigOperators

variable {K X Y Z A B C A' B' C' : Type*}
variable [CommSemiring K] [Fintype A] [Fintype B] [Fintype C]

def fiberMatrix [DecidableEq X] (M : X → A' → A → K) :
    (X × A') → (X × A) → K :=
  fun output input => if output.1 = input.1 then M output.1 output.2 input.2 else 0

end LocalMaps
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexHierarchySeparationRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open Filter
open scoped BigOperators Topology

namespace HierarchySeparationRates

universe u v w

def populationEntropyRate {B : Type*} [Fintype B] (counts : B → ℕ) : ℝ :=
  (∑ b, counts b : ℕ) *
    finiteEntropy (fun b => (counts b : ℝ) / (∑ b, counts b : ℕ))

theorem tendsto_log_multinomial_mul_div_repetition {B : Type*} [Fintype B]
    (counts : B → ℕ) :
    Tendsto
      (fun t : ℕ =>
        Real.log (Nat.multinomial Finset.univ (fun b => t * counts b) : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts)) := by
  by_cases hD : 0 < ∑ b, counts b
  · have hD' : ((∑ b, counts b : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
    have h := (tendsto_log_multinomial_mul counts hD).const_mul
      ((∑ b, counts b : ℕ) : ℝ)
    apply h.congr
    intro t
    by_cases ht : t = 0
    · simp [ht]
    have ht' : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht
    change ((∑ b, counts b : ℕ) : ℝ) *
        (Real.log (Nat.multinomial Finset.univ (fun b => t * counts b) : ℝ) /
          ((t : ℝ) * (∑ b, counts b : ℕ))) = _
    field_simp [hD', ht']
  · have hz : (∑ b, counts b) = 0 := Nat.eq_zero_of_not_pos hD
    have hc (b : B) : counts b = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc
        counts b ≤ ∑ c, counts c :=
          Finset.single_le_sum (fun c _ => Nat.zero_le _) (Finset.mem_univ b)
        _ = 0 := hz
    simp only [populationEntropyRate, hz, Nat.cast_zero, zero_mul]
    simp [Nat.multinomial, hc]

theorem populationEntropyRate_nonneg {B : Type*} [Fintype B] (counts : B → ℕ) :
    0 ≤ populationEntropyRate counts := by
  apply ge_of_tendsto' (tendsto_log_multinomial_mul_div_repetition counts)
  intro t
  apply div_nonneg _ (Nat.cast_nonneg t)
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ (fun b => t * counts b)))

section FinitePools

variable {I : Type u} [Fintype I] {Alphabet : I → Type v}
  [∀ i, Fintype (Alphabet i)]

def poolTypeCount (counts : ∀ i, Alphabet i → ℕ) (i : I) (t : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (fun b => t * counts i b)

def poolEntropyTotal (counts : ∀ i, Alphabet i → ℕ) : ℝ :=
  ∑ i, populationEntropyRate (counts i)

def pairingProduct (counts : ∀ i, Alphabet i → ℕ) (t : ℕ) : ℕ :=
  ∏ i, poolTypeCount counts i t

omit [Fintype I] in
theorem poolTypeCount_pos (counts : ∀ i, Alphabet i → ℕ) (i : I) (t : ℕ) :
    0 < poolTypeCount counts i t := Nat.multinomial_pos _ _

omit [Fintype I] in
theorem tendsto_log_poolTypeCount_div (counts : ∀ i, Alphabet i → ℕ) (i : I) :
    Tendsto (fun t : ℕ => Real.log (poolTypeCount counts i t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate (counts i))) :=
  tendsto_log_multinomial_mul_div_repetition (counts i)

theorem tendsto_log_pairingProduct_div (counts : ∀ i, Alphabet i → ℕ) :
    Tendsto (fun t : ℕ => Real.log (pairingProduct counts t : ℝ) / (t : ℝ))
      atTop (𝓝 (poolEntropyTotal counts)) := by
  exact Separation.tendsto_log_nat_prod_div_nat Finset.univ
    (fun i _ t => poolTypeCount_pos counts i t)
    (fun i _ => tendsto_log_poolTypeCount_div counts i)

end FinitePools

end HierarchySeparationRates
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexTensorSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

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

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Execution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionExecution

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

variable {A X Y Z : Type} [Fintype A]

abbrev Position (counts : A → ℕ) (t : ℕ) := Fin (t * ∑ a, counts a)
abbrev Coordinate (U : Type) (counts : A → ℕ) (t : ℕ) := Position counts t → U

theorem position_card (counts : A → ℕ) (t : ℕ) :
    Fintype.card (Position counts t) = ∑ a, t * counts a := by
  simp [Position, Finset.mul_sum]

end MatrixMultiplication.CompletionExecution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_RecursiveCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RecursiveCompletion

variable {X Y Z : Type*}

def diagonalMap {K U : Type*} [Zero K] [DecidableEq U] (f : U → K) : U → U → K :=
  fun output input => if input = output then f output else 0

def flagPolynomial (p : Prop) : Polynomial ℂ := if p then Polynomial.X else 1

end RecursiveCompletion
end MatrixMultiplication

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexBatchCeiling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

def batchCount (R k : ℕ) : ℕ := (R + k - 1) / k

@[simp] theorem batchCount_zero (k : ℕ) : batchCount 0 k = 0 := by
  unfold batchCount
  by_cases hk : k = 0
  · simp [hk]
  · apply Nat.div_eq_of_lt
    omega

def batchRank (k r : ℕ) : ℕ → ℕ
  | 0 => 1
  | t + 1 => batchCount (batchRank k r t) k * r

@[simp] theorem batchRank_zero (k r : ℕ) : batchRank k r 0 = 1 := rfl

@[simp] theorem batchRank_succ (k r t : ℕ) :
    batchRank k r (t + 1) = batchCount (batchRank k r t) k * r := rfl

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_FiniteRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionFiniteRealization

open MatrixMultiplication.Foundation RecursiveCompletion
open scoped BigOperators Classical

open CompletionExecution

variable {A X Y Z : Type} [Fintype A]
variable (counts : A → ℕ)
  (t : ℕ)

def blocks : ℕ := t * ∑ a, counts a

end MatrixMultiplication.CompletionFiniteRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Labels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v w z

variable {A : Type u}
  {Context : Type z}
  {Code : Type w}
  {depth : ℕ}

def powPast (d n : ℕ) (j : Fin (n % d)) : Fin n :=
  ⟨(n / d) * d + j.val, by
    calc
      (n / d) * d + j.val < (n / d) * d + n % d :=
        Nat.add_lt_add_left j.isLt _
      _ = n := by
        simpa only [Nat.mul_comm] using Nat.div_add_mod n d⟩

end MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_UniformProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualUniformProducts

open MatrixMultiplication.Foundation CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A X Y : I → Type*}
variable [∀ i, Fintype (A i)] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

def supportWordEquiv (P : ∀ i, X i → Prop) :
    {x : ∀ i, X i // ∀ i, P i (x i)} ≃ ∀ i, {x : X i // P i x} where
  toFun x i := ⟨x.val i, x.property i⟩
  invFun x := ⟨fun i => (x i).val, fun i => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MatrixMultiplication.DualUniformProducts

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_CompletionIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u w

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws
open TopologicalFlatten
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

def slotCut (depth k : ℕ) (i j : Fin m) : ℕ :=
  if j.val < i.val then depth else if j = i then k else 0

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

structure State where
  rho : ℝ
  factors : ℕ
  hB : ℝ
  hA : ℝ
  hC : ℝ

def initial : State := ⟨1 / 2, 1, 0, 0, 0⟩

def minus (m : ℕ) (s : State) : State :=
  let rho' := s.rho ^ m
  { rho := rho'
    factors := m * s.factors
    hB := m * s.hB
    hA := m * ((s.rho - rho') / (1 - rho') * s.hB +
      (1 - s.rho) / (1 - rho') * s.hA)
    hC := m * ((s.rho - rho') / (1 - rho') * s.hB +
      (1 - s.rho) / (1 - rho') * s.hC) }

def plusA (m : ℕ) (s : State) : State :=
  let rho' := 1 - (1 - s.rho) ^ m
  { rho := rho'
    factors := m * s.factors
    hB := m * (s.rho / rho' * s.hB + (rho' - s.rho) / rho' * s.hA)
    hA := m * s.hA
    hC := Real.log ((Real.exp s.hA + Real.exp s.hC) ^ m - Real.exp (m * s.hA)) }

def plusC (m : ℕ) (s : State) : State :=
  let rho' := 1 - (1 - s.rho) ^ m
  { rho := rho'
    factors := m * s.factors
    hB := m * (s.rho / rho' * s.hB + (rho' - s.rho) / rho' * s.hC)
    hA := Real.log ((Real.exp s.hC + Real.exp s.hA) ^ m - Real.exp (m * s.hC))
    hC := m * s.hC }

def state2 : State := minus 2 initial
def state4 : State := plusA 2 state2
def state8 : State := plusC 2 state4
def state24 : State := minus 3 state8
def state48 : State := plusC 2 state24
def state96 : State := minus 2 state48
def state288 : State := plusA 3 state96

def normalizedHidden (s : State) : ℝ :=
  (s.rho * s.hB + (1 - s.rho) * max s.hA s.hC) / s.factors

def rho8 : ℝ := 1 - (3 / 4 : ℝ) ^ 4
def rho24 : ℝ := rho8 ^ 3
def delta24 : ℝ := 3 * (1 - rho8) / (1 - rho24) * Real.log (9 / 7 : ℝ)
def z48 : ℝ := Real.log ((1 + Real.exp (-delta24)) ^ 2 - 1)
def rho48 : ℝ := 1 - (1 - rho24) ^ 2
def rho96 : ℝ := rho48 ^ 2
def delta96 : ℝ := 2 * z48 / (1 + rho48)
def rho288 : ℝ := 1 - (1 - rho96) ^ 3
def z288 : ℝ := Real.log ((1 + Real.exp (-delta96)) ^ 3 - 1)
def hiddenRate : ℝ := 9 / 64 * Real.log 3 +
  (1 - rho48) / 48 * z48 + (1 - rho288) / 288 * z288
def aspect : ℝ := 2 * hiddenRate / Real.log 2

theorem state8_rho : state8.rho = rho8 := by
  norm_num [state8, state4, state2, initial, minus, plusA, plusC, rho8]

theorem state24_rho : state24.rho = rho24 := by
  simp only [state24, minus, rho24, state8_rho]

theorem state48_rho : state48.rho = rho48 := by
  simp only [state48, plusC, rho48, state24_rho]

theorem state96_rho : state96.rho = rho96 := by
  simp only [state96, minus, rho96, state48_rho]

theorem state288_rho : state288.rho = rho288 := by
  simp only [state288, plusA, rho288, state96_rho]

theorem rho8_range : 0 < rho8 ∧ rho8 < 1 := by norm_num [rho8]
theorem rho24_range : 0 < rho24 ∧ rho24 < 1 := by norm_num [rho24, rho8]
theorem rho48_range : 0 < rho48 ∧ rho48 < 1 := by norm_num [rho48, rho24, rho8]
theorem rho96_range : 0 < rho96 ∧ rho96 < 1 := by norm_num [rho96, rho48, rho24, rho8]
theorem rho288_range : 0 < rho288 ∧ rho288 < 1 := by
  norm_num [rho288, rho96, rho48, rho24, rho8]

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_CompletionLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualCompletionLaws

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

def gibbsWeight (a b : ℝ) : ℝ := Real.exp a / (Real.exp a + Real.exp b)

theorem gibbsWeight_nonneg (a b : ℝ) : 0 ≤ gibbsWeight a b :=
  div_nonneg (Real.exp_pos a).le (add_pos (Real.exp_pos a) (Real.exp_pos b)).le

theorem gibbsWeight_lt_one (a b : ℝ) : gibbsWeight a b < 1 := by
  apply (div_lt_one (add_pos (Real.exp_pos a) (Real.exp_pos b))).mpr
  linarith [Real.exp_pos b]

end MatrixMultiplication.DualCompletionLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_ComplexRationalLogCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.Foundation.RationalLogCertificate

open scoped BigOperators

noncomputable def sumPower (t : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / (i + 1)

def rationalSumPower (t : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, t ^ (i + 1) / (i + 1)

noncomputable def realApprox (n : ℕ) (x : ℝ) : ℝ :=
  sumPower ((x - 1) / (x + 1)) n - sumPower (-((x - 1) / (x + 1))) n

def rationalApprox (n : ℕ) (x : ℚ) : ℚ :=
  rationalSumPower ((x - 1) / (x + 1)) n -
    rationalSumPower (-((x - 1) / (x + 1))) n

@[simp] theorem rationalSumPower_cast (t : ℚ) (n : ℕ) :
    (rationalSumPower t n : ℝ) = sumPower (t : ℝ) n := by
  simp [rationalSumPower, sumPower]

@[simp] theorem rationalApprox_cast (n : ℕ) (x : ℚ) :
    (rationalApprox n x : ℝ) = realApprox n (x : ℝ) := by
  simp [rationalApprox, realApprox]

structure ReducedArgument (x : ℚ) where
  exponent : ℤ
  mantissa : ℚ
  lower : 1 ≤ mantissa
  upper : mantissa ≤ 2
  value : x = mantissa * (2 : ℚ) ^ exponent

def reducedApprox {x : ℚ} (d : ReducedArgument x) : ℚ :=
  rationalApprox 80 d.mantissa + (d.exponent : ℚ) * rationalApprox 80 2

end MatrixMultiplication.Foundation.RationalLogCertificate

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_ComplexCertificatesLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.ComplexCertificates

open MatrixMultiplication.Foundation.RationalLogCertificate

def reduceTwo : ReducedArgument (2 : ℚ) where
  exponent := 0
  mantissa := 2
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceThree : ReducedArgument (3 : ℚ) where
  exponent := 1
  mantissa := 3 / 2
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceNineteen : ReducedArgument (19 : ℚ) where
  exponent := 4
  mantissa := 19 / 16
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceCurveLo : ReducedArgument (246439 / 5000 : ℚ) where
  exponent := 5
  mantissa := 246439 / 160000
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceCurveHi : ReducedArgument (49289 / 1000 : ℚ) where
  exponent := 5
  mantissa := 49289 / 32000
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceNineSevenths : ReducedArgument (9 / 7 : ℚ) where
  exponent := 0
  mantissa := 9 / 7
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceExpLo48 : ReducedArgument (701 / 1000 : ℚ) where
  exponent := -1
  mantissa := 701 / 500
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceExpHi48 : ReducedArgument (707 / 1000 : ℚ) where
  exponent := -1
  mantissa := 707 / 500
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceExpLo288 : ReducedArgument (169 / 400 : ℚ) where
  exponent := -2
  mantissa := 169 / 100
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceZ48Lo : ReducedArgument (((1 + 701 / 1000) ^ 2 - 1) : ℚ) where
  exponent := 0
  mantissa := (1 + 701 / 1000) ^ 2 - 1
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceZ48Hi : ReducedArgument (((1 + 707 / 1000) ^ 2 - 1) : ℚ) where
  exponent := 0
  mantissa := (1 + 707 / 1000) ^ 2 - 1
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

def reduceZ288Lo : ReducedArgument (((1 + 169 / 400) ^ 3 - 1) : ℚ) where
  exponent := 0
  mantissa := (1 + 169 / 400) ^ 3 - 1
  lower := by norm_num
  upper := by norm_num
  value := by norm_num

end MatrixMultiplication.ComplexCertificates

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_ExponentConsumer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualExponentBound

open Filter
open scoped Topology

def fixedAspect : ℝ := 4651 / 10000

end MatrixMultiplication.DualExponentBound

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

def massA (s : State) : ℝ := s.rho * s.hB + (1 - s.rho) * s.hA
def massC (s : State) : ℝ := s.rho * s.hB + (1 - s.rho) * s.hC

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Numerical_ComplexCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

noncomputable section

namespace MatrixMultiplication.ComplexCertificates

def curveU : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 3)
def curveV : ℝ := (19 : ℝ) ^ ((2 : ℝ) / 3)
def curveZ : ℝ := 8 + 12 * curveU + 6 * curveU ^ 2 + curveV
def curveG : ℝ :=
  (12 * curveU * (1 + curveU) * Real.log 2 + curveV * Real.log 19) / curveZ
def curveH : ℝ := Real.log curveZ - (2 / 3 : ℝ) * curveG

end MatrixMultiplication.ComplexCertificates

end

end OAI
end


