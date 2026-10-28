-- Prove2me | Definitions.Def_OAIQ44C001
-- name    : OAIQ44C001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:01:54.72326+00:00
-- url     : https://prove2.me/theorems/e59bddef-470b-495e-9619-fde60046982c
-- title:
--   Definitions bundle OAIQ44C001 of the split of OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StandardMapEntropy.main_components`, carved from OpenAI's openai/math development (OpenAI, *Positive Metric Entropy for the Standard Map at Large Parameters*, OpenAI Math Release, September 23, 2026, result family 146, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 83 declarations of OpenAI's Lean: 58 definitions, 1 inductive type or structure, 4 instances and 20 theorems. The definitions and types are `OAI.StandardMapEntropy.PlaneLyapunov.Growth`, `OAI.StandardMapEntropy.PlaneLyapunov.tailConstant`, `OAI.StandardMapEntropy.TreeLine`, `OAI.StandardMapEntropy.boundaryChain`, `OAI.StandardMapEntropy.bridgeAreaScale`, `OAI.StandardMapEntropy.bridgeGridCell`, `OAI.StandardMapEntropy.bridgeGridHi`, `OAI.StandardMapEntropy.bridgeGridLo`, `OAI.StandardMapEntropy.bridgeLocalConstant`, `OAI.StandardMapEntropy.bridgeMiddle`, `OAI.StandardMapEntropy.bridgeRealConstant`, `OAI.StandardMapEntropy.bridgeRowLength`, `OAI.StandardMapEntropy.capBase`, `OAI.StandardMapEntropy.capPrimitive`, `OAI.StandardMapEntropy.capSlope`, `OAI.StandardMapEntropy.coefficientPolynomial`, `OAI.StandardMapEntropy.coefficientScale`, `OAI.StandardMapEntropy.complexCell`, `OAI.StandardMapEntropy.derivativeVariationBound`, `OAI.StandardMapEntropy.dirichletMatrix`, `OAI.StandardMapEntropy.drawdown`, `OAI.StandardMapEntropy.entropyCap`, `OAI.StandardMapEntropy.erealOrderIso`, `OAI.StandardMapEntropy.fastBridgeConstant`, `OAI.StandardMapEntropy.finTotal`, `OAI.StandardMapEntropy.fineErrorRate`, `OAI.StandardMapEntropy.fineLinearRate`, `OAI.StandardMapEntropy.fineScale`, `OAI.StandardMapEntropy.forcingBudget`, `OAI.StandardMapEntropy.gridIntIndex`, `OAI.StandardMapEntropy.gridIntLabel`, `OAI.StandardMapEntropy.inverseFourthMajorant`, `OAI.StandardMapEntropy.inverseJet₁`, `OAI.StandardMapEntropy.inverseJet₂`, `OAI.StandardMapEntropy.inverseJet₃`, `OAI.StandardMapEntropy.inverseJet₄`, `OAI.StandardMapEntropy.liftGridCover`, `OAI.StandardMapEntropy.lineB`, `OAI.StandardMapEntropy.matrixChain`, `OAI.StandardMapEntropy.matrixEntryCLM` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/StandardMap, in whole or in part: `StandardMap_BridgeRealBound`, `StandardMap_EndpointCovariance`, `StandardMap_Entropy_FineCharts`, `StandardMap_Entropy_LiftGrid`, `StandardMap_Entropy_PhysicalVolume`, `StandardMap_FastBridge`, `StandardMap_GraphJacobians`, `StandardMap_GridBridge`, `StandardMap_LocalScarcity`, `StandardMap_Lyapunov_Definitions`, `StandardMap_Lyapunov_DerivativeGrowth`, `StandardMap_Lyapunov_PlaneLyapunov`, `StandardMap_MiddleCount`, `StandardMap_MiddlePrefixBridge`, `StandardMap_SmoothCap`, `StandardMap_Stable_LocalStable`, `StandardMap_Stable_SmoothRemainder`, `StandardMap_TreeLine`, `StandardMap_WeightedCompact`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ44C002`; the statement `OAI.StandardMapEntropy.BridgeGrid.scale_bound_q44`; the proofs of `OAI.HyperbolicCoding.actual_fixed_window_rate_copy_q44`, `OAI.HyperbolicCoding.block_recoding_small_cost_q44`, `OAI.HyperbolicCoding.fixed_decoder_arbitrary_tests_q44`, `OAI.HyperbolicCoding.goodIIDStage_initial_q44` and `OAI.HyperbolicCoding.goodIIDStage_next_q44`.
-- source:
--   OpenAI, Positive Metric Entropy for the Standard Map at Large Parameters, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 146; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/StandardMap at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ44_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h

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
-- module Solutions.OAIQ44_CM.StandardMap_LocalScarcity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

noncomputable def drawdown (z : ℕ → ℝ) (c : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max 0 (drawdown z c n + c + z n - z (n + 1))

noncomputable def forcingBudget (M : ℝ) (F : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => M * forcingBudget M F n + |F (n + 1)|

noncomputable def phiSecond (k x : ℝ) : ℝ := -(2 * Real.pi) ^ 2 * k * Real.sin (2 * Real.pi * x)

noncomputable def phiThird (k x : ℝ) : ℝ := -(2 * Real.pi) ^ 3 * k * Real.cos (2 * Real.pi * x)
noncomputable def phiFourth (k x : ℝ) : ℝ := (2 * Real.pi) ^ 4 * k * Real.sin (2 * Real.pi * x)
noncomputable def phiFifth (k x : ℝ) : ℝ := (2 * Real.pi) ^ 5 * k * Real.cos (2 * Real.pi * x)

section InverseChains
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]

def inverseJet₁ (G B₁ : R) : R := -(G * B₁ * G)
def inverseJet₂ (G B₁ B₂ : R) : R :=
  2 * G * B₁ * G * B₁ * G - G * B₂ * G

def inverseJet₃ (G B₁ B₂ B₃ : R) : R :=
  -(6 * G * B₁ * G * B₁ * G * B₁ * G) +
  3 * G * B₂ * G * B₁ * G + 3 * G * B₁ * G * B₂ * G - G * B₃ * G

def inverseJet₄ (G B₁ B₂ B₃ B₄ : R) : R :=
  24 * G * B₁ * G * B₁ * G * B₁ * G * B₁ * G -
  12 * G * B₂ * G * B₁ * G * B₁ * G -
  12 * G * B₁ * G * B₂ * G * B₁ * G -
  12 * G * B₁ * G * B₁ * G * B₂ * G +
  6 * G * B₂ * G * B₂ * G + 4 * G * B₃ * G * B₁ * G +
  4 * G * B₁ * G * B₃ * G - G * B₄ * G

end InverseChains

noncomputable def dirichletMatrix (v : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun a b => (if a = b then v (a.val + 1) else 0) -
    (if a.val = b.val + 1 then 1 else 0) - (if b.val = a.val + 1 then 1 else 0)

open scoped Matrix.Norms.Operator

noncomputable def matrixEntryCLM (n : ℕ) (a b : Fin n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (show Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ from {
    toFun := fun A => A a b
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }).toContinuousLinearMap

noncomputable def rescaledDiagonal (v : ℝ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ)
    (k q₀ θ L ξ : ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun a : Fin n => v k q₀ θ L ξ (a.val + 1))

def finTotal {n : ℕ} (f : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then f ⟨i, h⟩ else 0
@[simp] lemma finTotal_coe {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : finTotal f i.val = f i := by
  simp [finTotal, i.isLt]

noncomputable def boundaryChain {n : ℕ} (U : Fin n → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (s : ℕ) (v : Fin (s + 1) → Fin n → ℝ)
    (a : Fin (s + 1) → Fin n) : ℝ :=
  U (a 0) * (∏ i, v i (a i)) *
    (∏ i : Fin s, G (a i.castSucc) (a i.succ)) * U (a (Fin.last s))

noncomputable def matrixChain {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) :
    (s : ℕ) → (Fin (s + 1) → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  | 0, v => G * Matrix.diagonal (v 0) * G
  | s + 1, v => G * Matrix.diagonal (v 0) * matrixChain G s (fun i => v i.succ)

noncomputable def matrixPath {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ) (v : Fin (s + 1) → Fin n → ℝ) (a : Fin (s + 1) → Fin n)
    (row col : Fin n) : ℝ :=
  G row (a 0) * (∏ i, v i (a i)) *
    (∏ i : Fin s, G (a i.castSucc) (a i.succ)) * G (a (Fin.last s)) col

noncomputable def inverseFourthMajorant (A : ℝ) : ℝ :=
  24 * (8 * A) ^ 4 + 36 * (8 * A) ^ 3 + 14 * (8 * A) ^ 2 + 8 * A

noncomputable def scalarReciprocalJet (i : ℕ) (d : ℕ → ℝ) : ℝ := match i with
  | 0 => (d 0)⁻¹
  | 1 => inverseJet₁ (d 0)⁻¹ (d 1)
  | 2 => inverseJet₂ (d 0)⁻¹ (d 1) (d 2)
  | 3 => inverseJet₃ (d 0)⁻¹ (d 1) (d 2) (d 3)
  | _ => inverseJet₄ (d 0)⁻¹ (d 1) (d 2) (d 3) (d 4)

noncomputable def scalarProductJet (i : ℕ) (n d : ℕ → ℝ) : ℝ := match i with
  | 0 => n 0 * d 0
  | 1 => n 1 * d 0 + n 0 * d 1
  | 2 => n 2 * d 0 + 2 * n 1 * d 1 + n 0 * d 2
  | 3 => n 3 * d 0 + 3 * n 2 * d 1 + 3 * n 1 * d 2 + n 0 * d 3
  | _ => n 4 * d 0 + 4 * n 3 * d 1 + 6 * n 2 * d 2 + 4 * n 1 * d 3 + n 0 * d 4

noncomputable def oppositeLimitDifference (p : Polynomial ℝ) (A B C β z b : ℝ) (h : ℝ) : ℝ :=
  p.eval h * b ^ 2 * (Real.cos (2 * Real.pi * (z + b * h))) ^ 2 -
    (2 / b * (2 * A * h + B) * Real.cos (2 * Real.pi * (z + b * h)) -
      2 * Real.pi * (A * h ^ 2 + B * h + C) * Real.sin (2 * Real.pi * (z + b * h)) - 4 * β)

noncomputable def taylorPolynomialAtZero (f : ℝ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (iteratedDeriv i f 0 / (i.factorial : ℝ))

open Filter
open scoped Topology

noncomputable def coefficientPolynomial {d : ℕ} (c : Fin d → ℝ) : Polynomial ℝ :=
  ∑ i : Fin d, Polynomial.monomial i.val (c i)

open Metric

noncomputable def scaledTaylorPolynomial (f : ℝ → ℝ) (a : ℝ) : Polynomial ℝ :=
  (taylorPolynomialAtZero f 3).comp (Polynomial.C a * Polynomial.X)

section

noncomputable def slowDenominatorModel (Q E : ℝ → ℝ) (K r h : ℝ) : ℝ :=
  (deriv Q h / r) ^ 2 * (Real.cos (2 * Real.pi * Q h) + (2 - E h) / K)

end

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StandardMapEntropy

noncomputable def coefficientScale {ι : Type*} (a b c d : ι → ℝ) (n : ι) : ℝ :=
  max (max |a n| |b n|) (max |c n| (d n))

noncomputable def phaseReciprocal (Q E : ℝ → ℝ) (d x : ℝ) : ℝ :=
  1 / ((deriv Q x) ^ 2 * (Real.cos (2 * Real.pi * Q x) + (2 - E x) * d))

end StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GraphJacobians
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
noncomputable def planeDual (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ
noncomputable def planeMatrix (a b c d : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (planeDual a b).prod (planeDual c d)
@[simp] lemma planeDual_apply (a b : ℝ) (z : ℝ × ℝ) : planeDual a b z=a*z.1+b*z.2 := rfl
@[simp] lemma planeMatrix_apply (a b c d : ℝ) (z : ℝ × ℝ) :
    planeMatrix a b c d z=(a*z.1+b*z.2,c*z.1+d*z.2) := rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_SmoothCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Interval Topology
namespace StandardMapEntropy
noncomputable def capSlope (u : ℝ) : ℝ := 1-Real.smoothTransition (10000*u-1)
noncomputable def capPrimitive (u : ℝ) : ℝ := ∫ t in (0:ℝ)..u,capSlope t
noncomputable def capBase : ℝ := capPrimitive (1/5000)
noncomputable def entropyCap (α u : ℝ) : ℝ :=
  α*capPrimitive u+(1-α*capBase)*Real.smoothTransition (10000*u-2)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_TreeLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
structure TreeLine (d : ℝ → ℝ → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y=d y x
  triangle : ∀ x y z, d x z ≤ d x y+d y z
  unit : ∀ x y, d x y ≤ |y-x|
  tree : ∀ v x y z,
    min (d v x+d v y-d x y) (d v y+d v z-d y z) ≤ d v x+d v z-d x z
noncomputable def lineB (d : ℝ → ℝ → ℝ) (v x y : ℝ) : ℝ := d v x+d v y-d x y
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddleCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy

def bridgeMiddle (N : ℕ) : Finset ℕ := Finset.Icc (N/3+1) (2*N/3)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_GridBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def bridgeGridLo (i : Fin 32) : ℝ := (i:ℝ)/32
noncomputable def bridgeGridHi (i : Fin 32) : ℝ := ((i:ℝ)+1)/32
noncomputable def bridgeGridCell (i : Fin 32) : Set ℝ := Icc (bridgeGridLo i) (bridgeGridHi i)
noncomputable def bridgeAreaScale : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp (-1152*Real.pi))*(1/32)) *
    (ENNReal.ofReal (Real.exp (-1152*Real.pi)*(3/4))*(1/32))
noncomputable def bridgeLocalConstant : ℝ≥0∞ := ENNReal.ofReal (Real.exp (1152*Real.pi))*256
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_MiddlePrefixBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
def bridgeRowLength (B : ℕ) (b : Bool) : ℕ := if b then B else B-1
noncomputable def middleBridgeConstant : ℝ≥0∞ := 4096*bridgeLocalConstant/bridgeAreaScale
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_FastBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def fastBridgeConstant : ℝ≥0∞ := 5*middleBridgeConstant
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_BridgeRealBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def bridgeRealConstant : ℝ := fastBridgeConstant.toReal
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_WeightedCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def realWeight {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_EndpointCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
noncomputable def erealOrderIso (e : ℝ ≃o ℝ) : EReal ≃o EReal := e.withTopCongr.withBotCongr
@[simp] lemma erealOrderIso_coe (e : ℝ ≃o ℝ) (r : ℝ) : erealOrderIso e (r:EReal)=(e r:ℝ) := rfl
@[simp] lemma erealOrderIso_top (e : ℝ ≃o ℝ) : erealOrderIso e ⊤=⊤ := rfl
@[simp] lemma erealOrderIso_bot (e : ℝ ≃o ℝ) : erealOrderIso e ⊥=⊥ := rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_Definitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def standardLift (k : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re+z.im+k*Real.sin (2*Real.pi*z.re), z.im+k*Real.sin (2*Real.pi*z.re)⟩
noncomputable def standardInverseLift (k : ℝ) (z : ℂ) : ℂ :=
  ⟨z.re-z.im, z.im-k*Real.sin (2*Real.pi*(z.re-z.im))⟩

end StandardMapEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_DerivativeGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

@[simp] lemma complexPair_re (p : ℝ × ℝ) : (Complex.equivRealProdCLM.symm p).re = p.1 := rfl
@[simp] lemma complexPair_im (p : ℝ × ℝ) : (Complex.equivRealProdCLM.symm p).im = p.2 := rfl

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Lyapunov_PlaneLyapunov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace PlaneLyapunov

variable (A : ℕ → ℂ →L[ℝ] ℂ)

def Growth (v : ℂ) (l : ℝ) : Prop :=
  v ≠ 0 ∧ Tendsto (fun n : ℕ => Real.log ‖A n v‖ / (n : ℝ)) atTop (𝓝 l)

noncomputable def tailConstant (M α : ℝ) : ℝ :=
  M * Real.exp (-α) / (1-Real.exp (-2*α))

end PlaneLyapunov
end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_SmoothRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable def derivativeVariationBound (k : ℝ) : ℝ := 8*Real.pi^2*|k|
lemma derivativeVariationBound_nonneg (k : ℝ) : 0≤derivativeVariationBound k := by
  unfold derivativeVariationBound
  positivity

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

variable {ℓ δ : ℝ≥0}

lemma bound_of_max_contraction {d c K : ℝ} (hc : 0≤ c) (hK : K<1)
    (h : d≤ max c (K*d)) : d≤ c := by
  by_contra hh
  have hd : 0< d := hc.trans_lt (lt_of_not_ge hh)
  have hlt : max c (K*d)< d := max_lt (lt_of_not_ge hh) (by nlinarith)
  exact (not_lt_of_ge h) hlt

end StandardMapEntropy.NonlinearStable

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_LiftGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

noncomputable def gridIntIndex (Q : ℕ) (hQ : 0<Q) (i : ℤ) : Fin Q :=
  ⟨(i%(Q : ℤ)).toNat,by
    have h0 := Int.emod_nonneg i (show (Q : ℤ)≠0 by omega)
    have h1 := Int.emod_lt_of_pos i (show (0 : ℤ)<Q by omega)
    omega⟩

noncomputable def gridIntLabel (Q : ℕ) (hQ : 0<Q) (v : ℤ×ℤ) : Fin (Q*Q+1) :=
  (finProdFinEquiv (gridIntIndex Q hQ v.1,gridIntIndex Q hQ v.2)).castSucc
noncomputable def liftGridCover (Q : ℕ) (hQ : 0<Q) (c : ℂ) (M : ℕ) : Finset (Fin (Q*Q+1)) :=
  ((Finset.Icc (⌊(Q : ℝ)*c.re⌋-(M : ℤ)-1) (⌊(Q : ℝ)*c.re⌋+(M : ℤ)+1)).product
    (Finset.Icc (⌊(Q : ℝ)*c.im⌋-(M : ℤ)-1) (⌊(Q : ℝ)*c.im⌋+(M : ℤ)+1))).image (gridIntLabel Q hQ)

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Stable_LocalStable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

lemma slow_radius_ratio {a b ε : ℝ} (_ha : 0<a) (hb : 0<b)
    (hab : Real.exp (-ε)*a≤b) : a/b≤Real.exp ε := by
  apply (div_le_iff₀ hb).mpr
  have hh := mul_le_mul_of_nonneg_left hab (Real.exp_pos ε).le
  have he : Real.exp ε*Real.exp (-ε)=1 := by rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  simpa only [←mul_assoc,he,one_mul] using hh

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_FineCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable def fineScale (k ε δ : ℝ) : ℝ := δ/(8*(1+derivativeVariationBound k)*Real.exp (2*ε))
lemma fineScale_pos (k ε : ℝ) {δ : ℝ} (hδ : 0<δ) : 0<fineScale k ε δ := by
  unfold fineScale
  exact div_pos hδ (mul_pos (mul_pos (by norm_num) (by linarith [derivativeVariationBound_nonneg k])) (Real.exp_pos _))

end StandardMapEntropy

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open NonlinearStable

noncomputable def fineLinearRate (χ ε : ℝ) : ℝ≥0 := ⟨Real.exp (-χ+ε),(Real.exp_pos _).le⟩
noncomputable def fineErrorRate (δ : ℝ) (hδ : 0<δ) : ℝ≥0 := ⟨δ,hδ.le⟩

end StandardMapEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ44_CM.StandardMap_Entropy_PhysicalVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

def complexCell : Set ℂ := {z | z.re∈Ico (0 : ℝ) 1 ∧ z.im∈Ico (0 : ℝ) 1}

end StandardMapEntropy

end
end

end OAI
end


