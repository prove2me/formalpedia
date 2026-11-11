-- Prove2me | Definitions.Def_Q235MM000
-- name    : Q235MM000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:23:41.14996+00:00
-- url     : https://prove2.me/theorems/74470768-b4c1-4abd-9417-50523118f091
-- title:
--   Definitions bundle Q235MM000 of the split of OpenAI, Complex Matrix Multiplication Below 2.258 and Rectangular Bounds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixMultiplication.complex_alpha_gt_93_div_200` and `OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250`, carved from OpenAI's openai/math development (OpenAI, *Complex Matrix Multiplication Below 2.258 and Rectangular Bounds*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 756 declarations of OpenAI's Lean: 354 definitions, 20 inductive types or structures, 4 instances and 378 theorems. The definitions and types are `OAI.MatrixMultiplication.Arithmetic.Expression`, `OAI.MatrixMultiplication.Arithmetic.Expression.Compiled`, `OAI.MatrixMultiplication.Arithmetic.Expression.CompiledFamily`, `OAI.MatrixMultiplication.Arithmetic.Expression.compile`, `OAI.MatrixMultiplication.Arithmetic.Expression.compileFamily`, `OAI.MatrixMultiplication.Arithmetic.Expression.compileFinFamily`, `OAI.MatrixMultiplication.Arithmetic.Expression.cost`, `OAI.MatrixMultiplication.Arithmetic.Expression.eval`, `OAI.MatrixMultiplication.Arithmetic.Expression.sumFin`, `OAI.MatrixMultiplication.Arithmetic.Gate.mapInput`, `OAI.MatrixMultiplication.Arithmetic.Gate.mapRegister`, `OAI.MatrixMultiplication.Arithmetic.Gate.mapSource`, `OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm.pad`, `OAI.MatrixMultiplication.Arithmetic.Program.Substituted`, `OAI.MatrixMultiplication.Arithmetic.Program.Substituted.step`, `OAI.MatrixMultiplication.Arithmetic.Program.append`, `OAI.MatrixMultiplication.Arithmetic.Program.mapInput`, `OAI.MatrixMultiplication.Arithmetic.Program.mapSource`, `OAI.MatrixMultiplication.Arithmetic.Program.newIndex`, `OAI.MatrixMultiplication.Arithmetic.Program.oldIndex`, `OAI.MatrixMultiplication.Arithmetic.Program.registerCost`, `OAI.MatrixMultiplication.Arithmetic.Program.substitute`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.compose`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.copies`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.cost`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.eval`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.expressions`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.mapInputs`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.ofMatrix`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.Family.parallel`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.LinearExpression.linear`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.LinearExpression.sumFin`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.algorithm`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.inputExpressions`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.inputFamily`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.join`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.leftBlock`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.outputExpressions`, `OAI.MatrixMultiplication.Arithmetic.RecursiveBlock.outputFamily` and 334 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixMultiplication_Arithmetic_Complexity`, `MatrixMultiplication_Arithmetic_LowerBound`, `MatrixMultiplication_Arithmetic_NaiveAlgorithm`, `MatrixMultiplication_Arithmetic_Padding`, `MatrixMultiplication_Arithmetic_ProgramComposition`, `MatrixMultiplication_Arithmetic_Programs`, `MatrixMultiplication_Arithmetic_RecursiveBlockPrograms`, `MatrixMultiplication_Completion_Labels`, `MatrixMultiplication_Completion_RecursiveCompletion`, `MatrixMultiplication_ComplexBounds_CW75ReorderedExecution`, `MatrixMultiplication_ComplexBounds_CW75ReorderedGeometricValues`, `MatrixMultiplication_ComplexBounds_CW75ReorderedWords`, `MatrixMultiplication_CoppersmithWinograd_ComplexCW75InitialExecution`, `MatrixMultiplication_CoppersmithWinograd_ComplexCW75LabelHierarchy`, `MatrixMultiplication_CoppersmithWinograd_ComplexCW75Primitive`, `MatrixMultiplication_CoppersmithWinograd_ComplexCWBoundary`, `MatrixMultiplication_CoppersmithWinograd_ComplexCWOriginalWords`, `MatrixMultiplication_CoppersmithWinograd_ComplexCWPrimitiveDegeneration`, `MatrixMultiplication_CoppersmithWinograd_ComplexCoppersmithWinograd`, `MatrixMultiplication_Entropy_BaseConditionalReaders`, `MatrixMultiplication_Entropy_ComplexConditionalHierarchyStage`, `MatrixMultiplication_Entropy_ComplexConditionalPrefixWords`, `MatrixMultiplication_Entropy_ComplexConditionalTypeCounting`, `MatrixMultiplication_Entropy_ComplexFiniteEntropy`, `MatrixMultiplication_Entropy_ComplexHierarchyEntropy`, `MatrixMultiplication_Entropy_ComplexHierarchySeparationRates`, `MatrixMultiplication_Entropy_ComplexOrientedConditionalHierarchyStage`, `MatrixMultiplication_Entropy_ComplexSeparationAsymptotics`, `MatrixMultiplication_Entropy_ConditionalLabels`, `MatrixMultiplication_Polynomial_ComplexConstantPolynomialKernel`, `MatrixMultiplication_Polynomial_ComplexPolynomialApproximation`, `MatrixMultiplication_Polynomial_ComplexPolynomialControlledKernel`, `MatrixMultiplication_Polynomial_ComplexPolynomialDegenerationComposition`, `MatrixMultiplication_Polynomial_ComplexPolynomialExecutionReindex`, `MatrixMultiplication_Polynomial_ComplexPolynomialKernelExecution`, `MatrixMultiplication_Polynomial_ComplexPolynomialLocalConstruction`, `MatrixMultiplication_Polynomial_ComplexPolynomialRestriction`, `MatrixMultiplication_Polynomial_ComplexPolynomialWitnessProduct`, `MatrixMultiplication_Polynomial_ComplexPrefixSeparationPolynomialStage`, `MatrixMultiplication_Polynomial_ExpressionFamily`, `MatrixMultiplication_Rectangular_Growth`, `MatrixMultiplication_Separation_ComplexAuxiliarySeparation`, `MatrixMultiplication_Separation_ComplexBalancedSeparation`, `MatrixMultiplication_Separation_ComplexHierarchyTypeCounting`, `MatrixMultiplication_Separation_ComplexInitialTargetExecution`, `MatrixMultiplication_Separation_ComplexLabelHierarchySeparation`, `MatrixMultiplication_Separation_ComplexModularSeparation`, `MatrixMultiplication_Separation_ComplexPrefixSeparationOrientations`, `MatrixMultiplication_Separation_ComplexSeparation`, `MatrixMultiplication_Separation_ComplexSeparationCounting`, `MatrixMultiplication_Separation_ComplexStageHierarchyResources`, `MatrixMultiplication_Separation_ComplexTypeCounting`, `MatrixMultiplication_Tensor_BaseTensorBudgets`, `MatrixMultiplication_Tensor_BaseTensors`, `MatrixMultiplication_Tensor_ComplexElementary`, `MatrixMultiplication_Tensor_ComplexExecutionPairingBudget`, `MatrixMultiplication_Tensor_ComplexGeometricStageCoordinates`, `MatrixMultiplication_Tensor_ComplexGroupTensor`, `MatrixMultiplication_Tensor_ComplexInitialTargetKernel`, `MatrixMultiplication_Tensor_ComplexLocalMaps`, `MatrixMultiplication_Tensor_ComplexMatrixTensor`, `MatrixMultiplication_Tensor_ComplexTensor`, `MatrixMultiplication_Tensor_ComplexTensorRestrictionComposition`, `MatrixMultiplication_Tensor_ComplexTensorSymmetrization`, `MatrixMultiplication_Tensor_ComplexWitness`.
--
--   **Imports.** It imports the published bundle `Def_MatrixMultiplication`.
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Definitions.Def_MatrixMultiplication

section
-- module Solutions.Q235_MM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
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
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation

abbrev Tensor (K X Y Z : Type*) := X → Y → Z → K

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def rankOne (a : X → K) (b : Y → K) (c : Z → K) : Tensor K X Y Z :=
  fun x y z => a x * b y * c z

def RankAtMost (T : Tensor K X Y Z) (r : ℕ) : Prop :=
  ∃ (a : Fin r → X → K) (b : Fin r → Y → K) (c : Fin r → Z → K),
    T = fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z

def restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x' y' z' => ∑ x, ∑ y, ∑ z,
    A x' x * B y' y * C z' z * T x y z

def product {U V W : Type*} (T : Tensor K X Y Z) (S : Tensor K U V W) :
    Tensor K (X × U) (Y × V) (Z × W) :=
  fun x y z => T x.1 y.1 z.1 * S x.2 y.2 z.2

def directSum {ι : Type*} [DecidableEq ι] (T : ι → Tensor K X Y Z) :
    Tensor K (ι × X) (ι × Y) (ι × Z) :=
  fun x y z => if x.1 = y.1 ∧ x.1 = z.1 then T x.1 x.2 y.2 z.2 else 0

def power (T : Tensor K X Y Z) (n : ℕ) :
    Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
  fun x y z => ∏ i, T (x i) (y i) (z i)

@[simp] theorem directSum_matching {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) (i : ι) (x : X) (y : Y) (z : Z) :
    directSum T (i, x) (i, y) (i, z) = T i x y z := by
  simp [directSum]

@[simp] theorem rankAtMost_zero : RankAtMost (0 : Tensor K X Y Z) 0 := by
  refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
  funext x y z
  simp

theorem rankOne_rankAtMost (a : X → K) (b : Y → K) (c : Z → K) :
    RankAtMost (rankOne a b c) 1 := by
  refine ⟨fun _ => a, fun _ => b, fun _ => c, ?_⟩
  funext x y z
  simp

theorem RankAtMost.map {L : Type*} [CommSemiring L]
    (f : K →+* L) {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (fun x y z => f (T x y z)) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x => f (a i x), fun i y => f (b i y), fun i z => f (c i z), ?_⟩
  funext x y z
  simp [rankOne]

theorem rankAtMost_sum_rankOne {ι : Type*} [Fintype ι]
    (a : ι → X → K) (b : ι → Y → K) (c : ι → Z → K) :
    RankAtMost (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (Fintype.card ι) := by
  classical
  refine ⟨fun i => a ((Fintype.equivFin ι).symm i),
    fun i => b ((Fintype.equivFin ι).symm i),
    fun i => c ((Fintype.equivFin ι).symm i), ?_⟩
  funext x y z
  exact ((Fintype.equivFin ι).symm.sum_comp
    (fun i => rankOne (a i) (b i) (c i) x y z)).symm

theorem RankAtMost.product {U V W : Type*}
    {T : Tensor K X Y Z} {S : Tensor K U V W} {r s : ℕ}
    (hT : RankAtMost T r) (hS : RankAtMost S s) :
    RankAtMost (Tensor.product T S) (r * s) := by
  rcases hT with ⟨a, b, c, rfl⟩
  rcases hS with ⟨d, e, f, rfl⟩
  let aa : (Fin r × Fin s) → (X × U) → K := fun i x => a i.1 x.1 * d i.2 x.2
  let bb : (Fin r × Fin s) → (Y × V) → K := fun i y => b i.1 y.1 * e i.2 y.2
  let cc : (Fin r × Fin s) → (Z × W) → K := fun i z => c i.1 z.1 * f i.2 z.2
  have heq : Tensor.product
      (fun x y z => ∑ i, rankOne (a i) (b i) (c i) x y z)
      (fun u v w => ∑ j, rankOne (d j) (e j) (f j) u v w) =
      fun x y z => ∑ i, rankOne (aa i) (bb i) (cc i) x y z := by
    funext x y z
    simp only [Tensor.product, Fintype.sum_prod_type, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [rankOne, aa, bb, cc]
    ring
  rw [heq]
  simpa only [Fintype.card_prod, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_rankOne (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (a : X → K) (b : Y → K) (c : Z → K) :
    restrict A B C (rankOne a b c) =
      rankOne (fun x' => ∑ x, A x' x * a x)
        (fun y' => ∑ y, B y' y * b y)
        (fun z' => ∑ z, C z' z * c z) := by
  funext x' y' z'
  simp only [restrict, rankOne]
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem restrict_sum {ι : Type*} [Fintype ι]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : ι → Tensor K X Y Z) :
    restrict A B C (fun x y z => ∑ i, T i x y z) =
      fun x' y' z' => ∑ i, restrict A B C (T i) x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  calc
    (∑ x, ∑ y, ∑ z, ∑ i, A x' x * B y' y * C z' z * T i x y z) =
        ∑ x, ∑ y, ∑ i, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x, ∑ i, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T i x y z :=
      Finset.sum_comm

theorem RankAtMost.restrict {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) : RankAtMost (Tensor.restrict A B C T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨fun i x' => ∑ x, A x' x * a i x,
    fun i y' => ∑ y, B y' y * b i y,
    fun i z' => ∑ z, C z' z * c i z, ?_⟩
  rw [restrict_sum]
  funext x' y' z'
  apply Finset.sum_congr rfl
  intro i hi
  exact congrFun (congrFun (congrFun (restrict_rankOne A B C (a i) (b i) (c i)) x') y') z'

end Algebra

section Pullback
variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def pullback (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z)
    (T : Tensor K X Y Z) : Tensor K X' Y' Z' :=
  fun x y z => T (fx x) (fy y) (fz z)

theorem RankAtMost.pullback {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    RankAtMost (pullback fx fy fz T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  exact ⟨fun i x => a i (fx x), fun i y => b i (fy y),
    fun i z => c i (fz z), rfl⟩

end Pullback

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_Complexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

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

@[simp] theorem innerSize_zero (n : ℕ) : innerSize n 0 = 1 := by
  simp [innerSize]

@[simp] theorem innerSize_one (n : ℕ) : innerSize n 1 = n := by
  simp [innerSize]

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_LowerBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

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

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_Programs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

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

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ExpressionFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

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

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_NaiveAlgorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

variable {F : Type*} [Field F]

namespace Expression

variable {Input : Type*}

def sumFin : {n : ℕ} → (Fin n → Expression F Input) → Expression F Input
  | 0, _ => .constant 0
  | n + 1, f => .add (f 0) (sumFin (fun i : Fin n => f i.succ))

end Expression

def naiveEntry {a b c : ℕ} (i : Fin a) (k : Fin c) : Expression F (MatrixInput a b c) :=
  Expression.sumFin fun j : Fin b =>
    .mul (.input (.inl (i, j))) (.input (.inr (j, k)))

def naiveAlgorithm (a b c : ℕ) : MatrixAlgorithm F a b c :=
  let p := Expression.compileFamily (fun ik : Fin a × Fin c => naiveEntry (b := b) ik.1 ik.2)
  { registers := p.registers
    program := p.program
    output := fun i k => p.output (i, k) }

end MatrixMultiplication.Arithmetic

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_ProgramComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

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

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_Padding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

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

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexMatrixTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {K A B C D E F : Type*} [CommSemiring K]

def matrixCoefficients (A B C : Type*) [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    Tensor K (A × B) (B × C) (C × A) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

theorem matrixCoefficients_product [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq D] [DecidableEq E] [DecidableEq F]
    (x : (A × D) × (B × E)) (y : (B × E) × (C × F)) (z : (C × F) × (A × D)) :
    product (matrixCoefficients (K := K) A B C) (matrixCoefficients D E F)
      ((x.1.1, x.2.1), (x.1.2, x.2.2))
      ((y.1.1, y.2.1), (y.1.2, y.2.2))
      ((z.1.1, z.2.1), (z.1.2, z.2.2)) =
      matrixCoefficients (A × D) (B × E) (C × F) x y z := by
  simp only [product, matrixCoefficients, Prod.ext_iff]
  split_ifs <;> simp_all

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Arithmetic_RecursiveBlockPrograms
attribute [-simp] _root_.OAI.MatrixMultiplication.Arithmetic.MatrixAlgorithm.pad_cost_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Division-free arithmetic programs over a field and their operation counts. -/

noncomputable section

open scoped BigOperators

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

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

variable {F X Y Z : Type*} [Field F]

structure PolynomialApproximation (T : Tensor F X Y Z) (r d D : ℕ) where
  polynomial : Tensor (Polynomial F) X Y Z
  rank_bound : RankAtMost polynomial r
  vanishes : ∀ x y z k, k < d → (polynomial x y z).coeff k = 0
  leading : ∀ x y z, (polynomial x y z).coeff d = T x y z
  degree_bound : ∀ x y z, (polynomial x y z).degree ≤ D

namespace PolynomialApproximation

variable {T : Tensor F X Y Z} {r d D : ℕ}

def normalized (A : PolynomialApproximation T r d D) :
    Tensor (Polynomial F) X Y Z :=
  fun x y z => Classical.choose (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem polynomial_eq (A : PolynomialApproximation T r d D) (x : X) (y : Y) (z : Z) :
    A.polynomial x y z = Polynomial.X ^ d * A.normalized x y z :=
  Classical.choose_spec (Polynomial.X_pow_dvd_iff.mpr (A.vanishes x y z))

theorem normalized_constant (A : PolynomialApproximation T r d D)
    (x : X) (y : Y) (z : Z) : (A.normalized x y z).coeff 0 = T x y z := by
  have h := A.leading x y z
  rw [A.polynomial_eq] at h
  simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self] using h

end PolynomialApproximation

end Tensor
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

def cyclic (T : Tensor K X Y Z) : Tensor K Y Z X :=
  fun y z x => T x y z

theorem RankAtMost.cyclic {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) : RankAtMost (Tensor.cyclic T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, c, a, ?_⟩
  funext y z x
  simp only [Tensor.cyclic, rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialDegenerationComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section ScalarRestriction

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]
variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restrict_scalar_mul (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (P : Tensor K X Y Z) (s : K) :
    restrict A B C (fun x y z => s * P x y z) =
      fun x' y' z' => s * restrict A B C P x' y' z' := by
  funext x' y' z'
  simp only [restrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem cyclic_restrict (A : X' → X → K) (B : Y' → Y → K)
    (C : Z' → Z → K) (P : Tensor K X Y Z) :
    cyclic (restrict A B C P) = restrict B C A (cyclic P) := by
  funext y' z' x'
  simp only [cyclic, restrict]
  calc
    (∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * P x y z) =
        ∑ y, ∑ x, ∑ z, A x' x * B y' y * C z' z * P x y z :=
      Finset.sum_comm
    _ = ∑ y, ∑ z, ∑ x, A x' x * B y' y * C z' z * P x y z := by
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro x hx
      ring

end ScalarRestriction

section PolynomialCoefficients

variable {F : Type*} [Field F]

theorem coeff_mul_expand_eq_constant (M p : Polynomial F) (a : F)
    (hp : p.coeff 0 = a) (k j : ℕ) (hj : j ≤ k) :
    (M * Polynomial.expand F (k + 1) p).coeff j =
      (M * Polynomial.C a).coeff j := by
  have hdiv : Polynomial.X ∣ p - Polynomial.C a :=
    Polynomial.X_dvd_iff.mpr (by simp only [Polynomial.coeff_sub,
      Polynomial.coeff_C_zero, hp, sub_self])
  rcases hdiv with ⟨q, hq⟩
  have hpq : p = Polynomial.C a + Polynomial.X * q := by
    rw [← hq]
    ring
  have hexpand : Polynomial.expand F (k + 1) p =
      Polynomial.C a + Polynomial.X ^ (k + 1) *
        Polynomial.expand F (k + 1) q := by
    rw [hpq, map_add, map_mul, Polynomial.expand_C, Polynomial.expand_X]
  have hmul : M * Polynomial.expand F (k + 1) p =
      M * Polynomial.C a + Polynomial.X ^ (k + 1) *
        (M * Polynomial.expand F (k + 1) q) := by
    rw [hexpand]
    ring
  rw [hmul, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    ite_eq_right (by omega), add_zero]

end PolynomialCoefficients

section PolynomialLocalMaps

variable {F X Y Z X' Y' Z' : Type*} [Field F]
variable [Fintype X] [Fintype Y] [Fintype Z]

structure PolynomialRestrictionDegeneration
    (T : Tensor F X Y Z) (U : Tensor F X' Y' Z') (k Lx Ly Lz : ℕ) where
  leftMap : X' → X → Polynomial F
  middleMap : Y' → Y → Polynomial F
  rightMap : Z' → Z → Polynomial F
  left_degree : ∀ x' x, (leftMap x' x).degree ≤ Lx
  middle_degree : ∀ y' y, (middleMap y' y).degree ≤ Ly
  right_degree : ∀ z' z, (rightMap z' z).degree ≤ Lz
  vanishes : ∀ x' y' z' j, j < k →
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff j = 0
  leading : ∀ x' y' z',
    (restrict leftMap middleMap rightMap
      (fun x y z => Polynomial.C (T x y z)) x' y' z').coeff k = U x' y' z'

namespace PolynomialRestrictionDegeneration

variable {T : Tensor F X Y Z} {U : Tensor F X' Y' Z'}
variable {k Lx Ly Lz r d D : ℕ}

def cyclic (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    PolynomialRestrictionDegeneration (Tensor.cyclic T) (Tensor.cyclic U) k Ly Lz Lx where
  leftMap := L.middleMap
  middleMap := L.rightMap
  rightMap := L.leftMap
  left_degree := L.middle_degree
  middle_degree := L.right_degree
  right_degree := L.left_degree
  vanishes := by
    intro y' z' x' j hj
    change (restrict L.middleMap L.rightMap L.leftMap
      (Tensor.cyclic (fun x y z => Polynomial.C (T x y z))) y' z' x').coeff j = 0
    rw [← cyclic_restrict]
    exact L.vanishes x' y' z' j hj
  leading := by
    intro y' z' x'
    change (restrict L.middleMap L.rightMap L.leftMap
      (Tensor.cyclic (fun x y z => Polynomial.C (T x y z))) y' z' x').coeff k =
        Tensor.cyclic U y' z' x'
    rw [← cyclic_restrict]
    exact L.leading x' y' z'

def basePolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap (fun x y z => Polynomial.C (T x y z))

def compositionPolynomial (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) : Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap
    (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z))

def normalizedComposition (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) : Tensor (Polynomial F) X' Y' Z' :=
  restrict L.leftMap L.middleMap L.rightMap
    (fun x y z => Polynomial.expand F (k + 1) (W.normalized x y z))

theorem compositionPolynomial_eq
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (x' : X') (y' : Y') (z' : Z') :
    L.compositionPolynomial W x' y' z' =
      Polynomial.X ^ (d * (k + 1)) * L.normalizedComposition W x' y' z' := by
  have hpoint : (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z)) =
      fun x y z => Polynomial.X ^ (d * (k + 1)) *
        Polynomial.expand F (k + 1) (W.normalized x y z) := by
    funext x y z
    rw [W.polynomial_eq, map_mul, map_pow, Polynomial.expand_X]
    simp only [← pow_mul, Nat.mul_comm]
  unfold compositionPolynomial normalizedComposition
  rw [hpoint, restrict_scalar_mul]

theorem normalizedComposition_coeff
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (j : ℕ) (hj : j ≤ k)
    (x' : X') (y' : Y') (z' : Z') :
    (L.normalizedComposition W x' y' z').coeff j =
      (L.basePolynomial x' y' z').coeff j := by
  simp only [normalizedComposition, basePolynomial, restrict, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  exact coeff_mul_expand_eq_constant
    (L.leftMap x' x * L.middleMap y' y * L.rightMap z' z)
    (W.normalized x y z) (T x y z) (W.normalized_constant x y z) k j hj

theorem compositionPolynomial_rank
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    RankAtMost (L.compositionPolynomial W) r :=
  (W.rank_bound.map (Polynomial.expand F (k + 1)).toRingHom).restrict
    L.leftMap L.middleMap L.rightMap

theorem compositionPolynomial_degree
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) (x' : X') (y' : Y') (z' : Z') :
    (L.compositionPolynomial W x' y' z').degree ≤ D * (k + 1) + Lx + Ly + Lz := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold compositionPolynomial restrict
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y hy
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro z hz
  have hA := Polynomial.natDegree_le_of_degree_le (L.left_degree x' x)
  have hB := Polynomial.natDegree_le_of_degree_le (L.middle_degree y' y)
  have hC := Polynomial.natDegree_le_of_degree_le (L.right_degree z' z)
  have hP : (Polynomial.expand F (k + 1) (W.polynomial x y z)).natDegree ≤
      D * (k + 1) := by
    rw [Polynomial.natDegree_expand]
    exact Nat.mul_le_mul_right (k + 1)
      (Polynomial.natDegree_le_of_degree_le (W.degree_bound x y z))
  have hprod := Polynomial.natDegree_mul_le_of_le
    (Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_mul_le_of_le hA hB) hC) hP
  change (L.leftMap x' x * L.middleMap y' y * L.rightMap z' z *
    Polynomial.expand F (k + 1) (W.polynomial x y z)).natDegree ≤
      D * (k + 1) + Lx + Ly + Lz
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprod

def compose (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    PolynomialApproximation U r (d * (k + 1) + k) (D * (k + 1) + Lx + Ly + Lz) where
  polynomial := L.compositionPolynomial W
  rank_bound := L.compositionPolynomial_rank W
  vanishes := by
    intro x' y' z' j hj
    rw [L.compositionPolynomial_eq W, Polynomial.coeff_X_pow_mul']
    split_ifs with hdj
    · have hjk : j - d * (k + 1) < k := by omega
      rw [L.normalizedComposition_coeff W _ (Nat.le_of_lt hjk)]
      exact L.vanishes x' y' z' _ hjk
    · rfl
  leading := by
    intro x' y' z'
    rw [L.compositionPolynomial_eq W, Polynomial.coeff_X_pow_mul']
    simp only [Nat.le_add_right, ite_true, if_true, Nat.add_sub_cancel_left]
    rw [L.normalizedComposition_coeff W k le_rfl]
    exact L.leading x' y' z'
  degree_bound := L.compositionPolynomial_degree W

@[simp] theorem compose_polynomial
    (L : PolynomialRestrictionDegeneration T U k Lx Ly Lz)
    (W : PolynomialApproximation T r d D) :
    (L.compose W).polynomial = restrict L.leftMap L.middleMap L.rightMap
      (fun x y z => Polynomial.expand F (k + 1) (W.polynomial x y z)) := rfl

end PolynomialRestrictionDegeneration

end PolynomialLocalMaps

end Tensor
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialRestriction
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section ConstantRestriction

variable {F X Y Z X' Y' Z' : Type*} [CommSemiring F]
variable [Fintype X] [Fintype Y] [Fintype Z]

def restrictPolynomial (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) :
    Tensor (Polynomial F) X' Y' Z' :=
  restrict (fun x' x => Polynomial.C (A x' x))
    (fun y' y => Polynomial.C (B y' y))
    (fun z' z => Polynomial.C (C z' z)) P

@[simp] theorem restrictPolynomial_coeff (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) (k : ℕ)
    (x' : X') (y' : Y') (z' : Z') :
    (restrictPolynomial A B C P x' y' z').coeff k =
      restrict A B C (fun x y z => (P x y z).coeff k) x' y' z' := by
  simp only [restrictPolynomial, restrict, Polynomial.finsetSum_coeff,
    mul_assoc, Polynomial.coeff_C_mul]

theorem RankAtMost.restrictPolynomial {P : Tensor (Polynomial F) X Y Z} {r : ℕ}
    (hP : RankAtMost P r) (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) : RankAtMost (restrictPolynomial A B C P) r :=
  hP.restrict (fun x' x => Polynomial.C (A x' x))
    (fun y' y => Polynomial.C (B y' y))
    (fun z' z => Polynomial.C (C z' z))

theorem restrictPolynomial_degree_le (A : X' → X → F) (B : Y' → Y → F)
    (C : Z' → Z → F) (P : Tensor (Polynomial F) X Y Z) (D : ℕ)
    (hdegree : ∀ x y z, (P x y z).degree ≤ D)
    (x' : X') (y' : Y') (z' : Z') :
    (restrictPolynomial A B C P x' y' z').degree ≤ D := by
  apply (Polynomial.degree_le_iff_coeff_zero _ _).2
  intro k hk
  rw [restrictPolynomial_coeff]
  have hzero (x : X) (y : Y) (z : Z) : (P x y z).coeff k = 0 :=
    (Polynomial.degree_le_iff_coeff_zero _ _).1 (hdegree x y z) k hk
  simp only [restrict, hzero, mul_zero, Finset.sum_const_zero]

end ConstantRestriction

namespace PolynomialApproximation

variable {F X Y Z X' Y' Z' : Type*} [Field F]

def ofRankAtMost (T : Tensor F X Y Z) (r : ℕ) (hT : RankAtMost T r) :
    PolynomialApproximation T r 0 0 where
  polynomial := fun x y z => Polynomial.C (T x y z)
  rank_bound := hT.map Polynomial.C
  vanishes := by
    intro x y z k hk
    exact (Nat.not_lt_zero k hk).elim
  leading := by
    intro x y z
    exact Polynomial.coeff_C_zero
  degree_bound := by
    intro x y z
    simpa only [Nat.cast_zero] using (Polynomial.degree_C_le (a := T x y z))

@[simp] theorem ofRankAtMost_polynomial (T : Tensor F X Y Z) (r : ℕ)
    (hT : RankAtMost T r) :
    (ofRankAtMost T r hT).polynomial = (fun x y z => Polynomial.C (T x y z)) := rfl

variable [Fintype X] [Fintype Y] [Fintype Z]
variable {T : Tensor F X Y Z} {r d D : ℕ}

def restrict (W : PolynomialApproximation T r d D)
    (A : X' → X → F) (B : Y' → Y → F) (C : Z' → Z → F) :
    PolynomialApproximation (Tensor.restrict A B C T) r d D where
  polynomial := restrictPolynomial A B C W.polynomial
  rank_bound := W.rank_bound.restrictPolynomial A B C
  vanishes := by
    intro x' y' z' k hk
    rw [restrictPolynomial_coeff]
    have hzero (x : X) (y : Y) (z : Z) : (W.polynomial x y z).coeff k = 0 :=
      W.vanishes x y z k hk
    simp only [Tensor.restrict, hzero, mul_zero, Finset.sum_const_zero]
  leading := by
    intro x' y' z'
    rw [restrictPolynomial_coeff]
    simp only [W.leading]
  degree_bound := restrictPolynomial_degree_le A B C W.polynomial D W.degree_bound

@[simp] theorem restrict_polynomial (W : PolynomialApproximation T r d D)
    (A : X' → X → F) (B : Y' → Y → F) (C : Z' → Z → F) :
    (W.restrict A B C).polynomial = restrictPolynomial A B C W.polynomial := rfl

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialWitnessProduct
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation
namespace Tensor
namespace PolynomialApproximation

variable {F X Y Z U V W X' Y' Z' : Type*} [Field F]
variable {T : Tensor F X Y Z} {S : Tensor F U V W}
variable {r s d e D E : ℕ}

theorem product_polynomial_eq (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) (x : X × U) (y : Y × V) (z : Z × W) :
    Tensor.product A.polynomial B.polynomial x y z =
      Polynomial.X ^ (d + e) * Tensor.product A.normalized B.normalized x y z := by
  dsimp only [Tensor.product]
  rw [A.polynomial_eq, B.polynomial_eq, pow_add]
  ring

def product (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) :
    PolynomialApproximation (Tensor.product T S) (r * s) (d + e) (D + E) where
  polynomial := Tensor.product A.polynomial B.polynomial
  rank_bound := A.rank_bound.product B.rank_bound
  vanishes := by
    intro x y z k hk
    rw [A.product_polynomial_eq B]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false, if_false]
  leading := by
    intro x y z
    rw [A.product_polynomial_eq B]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self,
      Tensor.product, Polynomial.mul_coeff_zero, A.normalized_constant, B.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    exact Polynomial.natDegree_mul_le_of_le
      (Polynomial.natDegree_le_of_degree_le (A.degree_bound x.1 y.1 z.1))
      (Polynomial.natDegree_le_of_degree_le (B.degree_bound x.2 y.2 z.2))

@[simp] theorem product_polynomial (A : PolynomialApproximation T r d D)
    (B : PolynomialApproximation S s e E) :
    (A.product B).polynomial = Tensor.product A.polynomial B.polynomial := rfl

def pullback (A : PolynomialApproximation T r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    PolynomialApproximation (Tensor.pullback fx fy fz T) r d D where
  polynomial := Tensor.pullback fx fy fz A.polynomial
  rank_bound := A.rank_bound.pullback fx fy fz
  vanishes := fun x y z k hk => A.vanishes (fx x) (fy y) (fz z) k hk
  leading := fun x y z => A.leading (fx x) (fy y) (fz z)
  degree_bound := fun x y z => A.degree_bound (fx x) (fy y) (fz z)

@[simp] theorem pullback_polynomial (A : PolynomialApproximation T r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    (A.pullback fx fy fz).polynomial = Tensor.pullback fx fy fz A.polynomial := rfl

def cyclic (A : PolynomialApproximation T r d D) :
    PolynomialApproximation (Tensor.cyclic T) r d D where
  polynomial := Tensor.cyclic A.polynomial
  rank_bound := A.rank_bound.cyclic
  vanishes := fun y z x k hk => A.vanishes x y z k hk
  leading := fun y z x => A.leading x y z
  degree_bound := fun y z x => A.degree_bound x y z

@[simp] theorem cyclic_polynomial (A : PolynomialApproximation T r d D) :
    A.cyclic.polynomial = Tensor.cyclic A.polynomial := rfl

end PolynomialApproximation
end Tensor
end MatrixMultiplication.Foundation

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

inductive Color where
  | B | A | C
  deriving DecidableEq

structure FlaggedTensor (X Y Z : Type*) where
  tensor : Tensor ℂ X Y Z
  flagB : X → Prop
  flagA : Z → Prop
  flagC : Y → Prop
  one_hot : ∀ x y z, tensor x y z ≠ 0 →
    (if flagB x then 1 else 0) + (if flagA z then 1 else 0) +
      (if flagC y then 1 else 0) = (1 : ℕ)

namespace RecursiveCompletion

def raisedFlag {I : Type*} (center color : Color) (p : I → Prop) : Prop :=
  if center = color then ∀ i, p i else ∃ i, p i

variable {X Y Z : Type*}

def flagB (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (x : Fin m → X) : Prop := raisedFlag center .B (fun i => S.flagB (x i))

def flagA (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (z : Fin m → Z) : Prop := raisedFlag center .A (fun i => S.flagA (z i))

def flagC (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (y : Fin m → Y) : Prop := raisedFlag center .C (fun i => S.flagC (y i))

def weight (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z) : ℕ :=
  (if flagB S center m x then 1 else 0) +
    (if flagA S center m z then 1 else 0) +
    (if flagC S center m y then 1 else 0)

def complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    FlaggedTensor (Fin m → X) (Fin m → Y) (Fin m → Z) where
  tensor x y z := if weight S center m x y z = 1 then
    Tensor.power S.tensor m x y z else 0
  flagB := flagB S center m
  flagA := flagA S center m
  flagC := flagC S center m
  one_hot := by
    intro x y z hs
    by_cases hw : weight S center m x y z = 1
    · exact hw
    · simp [hw] at hs

@[simp] theorem complete_tensor (S : FlaggedTensor X Y Z) (center : Color)
    (m : ℕ) (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z) :
    (complete S center m).tensor x y z =
      if weight S center m x y z = 1 then Tensor.power S.tensor m x y z else 0 := rfl

end RecursiveCompletion
end MatrixMultiplication

end

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

structure FiniteLaw (A : Type*) [Fintype A] where
  mass : A → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B := by
  classical
  exact
    { mass := fun b => ∑ a, if f a = b then p.mass a else 0
      nonneg := fun b => Finset.sum_nonneg fun a _ => by
        split_ifs
        · exact p.nonneg a
        · exact le_rfl
      total := by
        rw [Finset.sum_comm]
        simpa using p.total }

@[simp] theorem map_mass [DecidableEq B] (p : FiniteLaw A) (f : A → B) (b : B) :
    (p.map f).mass b = ∑ a, if f a = b then p.mass a else 0 := by
  classical
  dsimp only [map]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp only [h, ite_true, if_true, ite_false, if_false]

def joint (p : FiniteLaw A) (q : A → FiniteLaw B) : FiniteLaw (A × B) where
  mass ab := p.mass ab.1 * (q ab.1).mass ab.2
  nonneg ab := mul_nonneg (p.nonneg ab.1) ((q ab.1).nonneg ab.2)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, (q _).total, p.total]

end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexHierarchyEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

noncomputable section

def LabelRecord (Label : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => LabelRecord Label n × Label n

instance labelRecordFintype (Label : ℕ → Type u) [∀ n, Fintype (Label n)] :
    (n : ℕ) → Fintype (LabelRecord Label n)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | n + 1 => by
      letI := labelRecordFintype Label n
      change Fintype (LabelRecord Label n × Label n)
      infer_instance

def labelRecordOf {A : Type v} {Label : ℕ → Type u}
    (labels : ∀ n, A → Label n) : (n : ℕ) → A → LabelRecord Label n
  | 0, _ => PUnit.unit
  | n + 1, a => (labelRecordOf labels n a, labels n a)

structure FiniteLabelHierarchy (Label : ℕ → Type u) [∀ n, Fintype (Label n)]
    (depth : ℕ) where
  conditional : ∀ n, n < depth → LabelRecord Label n → FiniteLaw (Label n)

namespace FiniteLabelHierarchy

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)] {depth : ℕ}

def prefixLaw (h : FiniteLabelHierarchy Label depth) :
    (n : ℕ) → n ≤ depth → FiniteLaw (LabelRecord Label n)
  | 0, _ =>
      { mass := fun _ => 1
        nonneg := fun _ => zero_le_one
        total := by
          classical
          refine Finset.sum_eq_single_of_mem (PUnit.unit : LabelRecord Label 0)
            (Finset.mem_univ _) ?_
          intro r _ hr
          cases r
          exact (hr rfl).elim }
  | n + 1, hn =>
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn))

@[simp] theorem prefixLaw_zero_mass (h : FiniteLabelHierarchy Label depth)
    (hn : 0 ≤ depth) (r : LabelRecord Label 0) :
    (h.prefixLaw 0 hn).mass r = 1 := rfl

@[simp] theorem prefixLaw_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    h.prefixLaw (n + 1) hn =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).joint
        (h.conditional n (Nat.lt_of_succ_le hn)) := rfl

@[simp] theorem prefixLaw_succ_mass (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) (r : LabelRecord Label n) (s : Label n) :
    (h.prefixLaw (n + 1) hn).mass (r, s) =
      (h.prefixLaw n (Nat.le_of_succ_le hn)).mass r *
        (h.conditional n (Nat.lt_of_succ_le hn) r).mass s := rfl

end FiniteLabelHierarchy

end
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexSeparationCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation.Separation

abbrev Grid (d Q : ℕ) := Fin d → Fin Q

def gridSquaredNorm {d Q : ℕ} (x : Grid d Q) : ℕ := ∑ i, (x i : ℕ) ^ 2

def gridDot {d Q : ℕ} (t u : Grid d Q) : ℕ := ∑ i, (t i : ℕ) * (u i : ℕ)

theorem gridSquaredNorm_le {d Q : ℕ} (x : Grid d Q) : gridSquaredNorm x ≤ d * Q ^ 2 := by
  calc
    gridSquaredNorm x ≤ ∑ _i : Fin d, Q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.pow_le_pow_left (Nat.le_of_lt (x i).isLt) 2
    _ = d * Q ^ 2 := by simp

theorem gridDot_le {d Q : ℕ} (t u : Grid d Q) : gridDot t u ≤ d * Q ^ 2 := by
  calc
    gridDot t u ≤ ∑ _i : Fin d, Q ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [pow_two] using
        Nat.mul_le_mul (Nat.le_of_lt (t i).isLt) (Nat.le_of_lt (u i).isLt)
    _ = d * Q ^ 2 := by simp

def normColor {d Q : ℕ} (x : Grid d Q) : Fin (d * Q ^ 2 + 1) :=
  ⟨gridSquaredNorm x, Nat.lt_succ_of_le (gridSquaredNorm_le x)⟩

def dotColor {d Q : ℕ} (t u : Grid d Q) : Fin (d * Q ^ 2 + 1) :=
  ⟨gridDot t u, Nat.lt_succ_of_le (gridDot_le t u)⟩

theorem two_stage_pigeonhole {A : Type*} [Fintype A] [DecidableEq A]
    {M K m : ℕ} (hM : 0 < M) (f : A → Fin M) (g : A → A → Fin M)
    (hK : M * K ≤ Fintype.card A) (hm : M * m ≤ Fintype.card A) :
    ∃ tags : Finset A, tags.card = K ∧
      (∃ radius : Fin M, ∀ t ∈ tags, f t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset A, slice.card = m ∧
        ∃ level : Fin M, ∀ u ∈ slice, g t u = level := by
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨radius, hr⟩ := Fintype.exists_le_card_fiber_of_mul_le_card f
    (by simpa only [Fintype.card_fin] using hK)
  obtain ⟨tags, htags, hcard⟩ := Finset.exists_subset_card_eq hr
  refine ⟨tags, hcard, ⟨radius, ?_⟩, ?_⟩
  · intro t ht
    exact (Finset.mem_filter.mp (htags ht)).2
  · intro t ht
    obtain ⟨level, hl⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (g t)
      (by simpa only [Fintype.card_fin] using hm)
    obtain ⟨slice, hslice, hsize⟩ := Finset.exists_subset_card_eq hl
    refine ⟨slice, hsize, level, ?_⟩
    intro u hu
    exact (Finset.mem_filter.mp (hslice hu)).2

theorem grid_tags_slices {d Q K m : ℕ}
    (hK : (d * Q ^ 2 + 1) * K ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d) :
    ∃ tags : Finset (Grid d Q), tags.card = K ∧
      (∃ radius : Fin (d * Q ^ 2 + 1), ∀ t ∈ tags, normColor t = radius) ∧
      ∀ t ∈ tags, ∃ slice : Finset (Grid d Q), slice.card = m ∧
        ∃ level : Fin (d * Q ^ 2 + 1), ∀ u ∈ slice, dotColor t u = level := by
  exact two_stage_pigeonhole (Nat.succ_pos _) normColor dotColor
    (by simpa only [Grid, Fintype.card_fun, Fintype.card_fin] using hK)
    (by simpa only [Grid, Fintype.card_fun, Fintype.card_fin] using hm)

end MatrixMultiplication.Foundation.Separation

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

theorem scale_exists (K : ℕ) : ∃ n : ℕ, K ≤ 2 ^ (n ^ 2) := by
  refine ⟨K + 1, ?_⟩
  have hK : K < 2 ^ K := Nat.lt_pow_self (by decide : 1 < 2)
  exact hK.le.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

noncomputable def gridScale (K : ℕ) : ℕ := Nat.find (scale_exists K)

theorem population_le_scale (K : ℕ) : K ≤ 2 ^ ((gridScale K) ^ 2) :=
  Nat.find_spec (scale_exists K)

def gridDimension (K : ℕ) : ℕ := gridScale K + 4

def gridWidth (K : ℕ) : ℕ := 2 ^ (gridScale K + 2)

def gridGroupOrder (K : ℕ) : ℕ := (4 * gridWidth K) ^ gridDimension K

theorem gridWidth_ge_two (K : ℕ) : 2 ≤ gridWidth K := by
  simpa only [gridWidth, pow_one] using
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ gridScale K + 2))

theorem dimension_le_power (n : ℕ) : n + 4 ≤ 2 ^ (n + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 2 ^ (n + 2 + 1) = 2 ^ (n + 2) * 2 := pow_succ _ _
    have he : n + 1 + 2 = n + 2 + 1 := by omega
    rw [he, hp]
    omega

theorem grid_population_bound (K : ℕ) :
    (gridDimension K * gridWidth K ^ 2 + 1) * K ≤
      gridWidth K ^ gridDimension K := by
  let n := gridScale K
  have hd : n + 4 ≤ 2 ^ (n + 2) := dimension_le_power n
  have hq : 0 < 2 ^ (n + 2) := by positivity
  have hcolorpos : 0 < (n + 4) * (2 ^ (n + 2)) ^ 2 := by positivity
  have hcolor : (n + 4) * (2 ^ (n + 2)) ^ 2 + 1 ≤ 2 ^ (3 * n + 7) := by
    calc
      (n + 4) * (2 ^ (n + 2)) ^ 2 + 1 ≤
          2 * ((n + 4) * (2 ^ (n + 2)) ^ 2) := by nlinarith
      _ ≤ 2 * (2 ^ (n + 2) * (2 ^ (n + 2)) ^ 2) := by gcongr
      _ = 2 ^ (3 * n + 7) := by
        rw [← pow_mul, ← pow_add, ← pow_succ']
        congr 1
        omega
  calc
    (gridDimension K * gridWidth K ^ 2 + 1) * K ≤
        2 ^ (3 * n + 7) * 2 ^ (n ^ 2) :=
      Nat.mul_le_mul hcolor (population_le_scale K)
    _ = 2 ^ (3 * n + 7 + n ^ 2) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((n + 2) * (n + 4)) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    _ = gridWidth K ^ gridDimension K := by
      simp only [gridWidth, gridDimension, n, pow_mul]

theorem gridGroupOrder_eq (K : ℕ) :
    gridGroupOrder K = 2 ^ ((gridScale K + 4) ^ 2) := by
  unfold gridGroupOrder gridWidth gridDimension
  have hb : 4 * 2 ^ (gridScale K + 2) = 2 ^ (gridScale K + 4) := by
    calc
      4 * 2 ^ (gridScale K + 2) = 2 ^ 2 * 2 ^ (gridScale K + 2) := by norm_num
      _ = 2 ^ (2 + (gridScale K + 2)) := (pow_add _ _ _).symm
      _ = 2 ^ (gridScale K + 4) := by congr 1; omega
  rw [hb, ← pow_mul, pow_two]

theorem population_le_gridGroupOrder (K : ℕ) : K ≤ gridGroupOrder K := by
  rw [gridGroupOrder_eq]
  exact (population_le_scale K).trans
    (Nat.pow_le_pow_right (by decide)
      (Nat.pow_le_pow_left (Nat.le_add_right (gridScale K) 4) 2))

end MatrixMultiplication.Foundation.Separation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation.Separation

theorem grid_modular_collision (Q c t u v : ℤ)
    (hc : 0 ≤ c ∧ c < Q) (ht : 0 ≤ t ∧ t < Q)
    (hu : 0 ≤ u ∧ u < Q) (hv : 0 ≤ v ∧ v < Q)
    (hmod : Int.ModEq (4 * Q) c (t + u - v)) : c = t + u - v := by
  have hdvd : 4 * Q ∣ t + u - v - c := hmod.dvd
  have hz : t + u - v - c = 0 := by
    rcases le_total 0 (t + u - v - c) with h | h
    · exact Int.eq_zero_of_dvd_of_nonneg_of_lt h (by omega) hdvd
    · have hn : -(t + u - v - c) = 0 :=
        Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) (Int.dvd_neg.mpr hdvd)
      omega
  omega

variable {ι : Type*} [Fintype ι]

def squaredNorm (t : ι → ℝ) : ℝ := ∑ i, (t i) ^ 2

def dot (t u : ι → ℝ) : ℝ := ∑ i, t i * u i

theorem squaredNorm_displacement (t u v : ι → ℝ) :
    squaredNorm (fun i => t i + u i - v i) =
      squaredNorm t + 2 * (dot t u - dot t v) +
        squaredNorm (fun i => u i - v i) := by
  calc
    squaredNorm (fun i => t i + u i - v i) =
        ∑ i, ((t i) ^ 2 + 2 * (t i * u i - t i * v i) +
          (u i - v i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [squaredNorm, dot, Finset.sum_add_distrib,
        mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]

theorem sphere_slice_collision (t c u v : ι → ℝ)
    (hsphere : squaredNorm c = squaredNorm t)
    (hslice : dot t u = dot t v)
    (hcollision : ∀ i, c i = t i + u i - v i) : u = v ∧ c = t := by
  have hc : c = fun i => t i + u i - v i := funext hcollision
  have hzero : squaredNorm (fun i => u i - v i) = 0 := by
    have hid := squaredNorm_displacement t u v
    rw [← hc, hsphere, hslice] at hid
    linarith
  have huv : u = v := by
    funext i
    have hle : (u i - v i) ^ 2 ≤ squaredNorm (fun j => u j - v j) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (u j - v j)) (Finset.mem_univ i)
    rw [hzero] at hle
    nlinarith [sq_nonneg (u i - v i)]
  refine ⟨huv, ?_⟩
  funext i
  rw [hcollision, huv]
  ring

end MatrixMultiplication.Foundation.Separation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexModularSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation.Separation

abbrev AuxiliaryGroup (d Q : ℕ) := Fin d → ZMod (4 * Q)

def gridToGroup {d Q : ℕ} (x : Grid d Q) : AuxiliaryGroup d Q :=
  fun i => (x i : ℕ)

def gridToReal {d Q : ℕ} (x : Grid d Q) : Fin d → ℝ :=
  fun i => (x i : ℕ)

theorem gridToReal_injective {d Q : ℕ} :
    Function.Injective (gridToReal : Grid d Q → Fin d → ℝ) := by
  intro x y h
  funext i
  apply Fin.ext
  have hi := congrFun h i
  change ((x i : ℕ) : ℝ) = ((y i : ℕ) : ℝ) at hi
  exact_mod_cast hi

theorem squaredNorm_gridToReal {d Q : ℕ} (x : Grid d Q) :
    squaredNorm (gridToReal x) = (gridSquaredNorm x : ℝ) := by
  simp [squaredNorm, gridToReal, gridSquaredNorm, Nat.cast_sum]

theorem dot_gridToReal {d Q : ℕ} (x y : Grid d Q) :
    dot (gridToReal x) (gridToReal y) = (gridDot x y : ℝ) := by
  simp [dot, gridToReal, gridDot, Nat.cast_sum]

theorem grid_group_collision_lift {d Q : ℕ} (t c u v : Grid d Q)
    (h : gridToGroup u + (gridToGroup t - gridToGroup v) = gridToGroup c) :
    ∀ i, ((c i : ℕ) : ℤ) =
      ((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ) := by
  intro i
  have hcast : (((c i : ℕ) : ℤ) : ZMod (4 * Q)) =
      ((((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) :
        ZMod (4 * Q)) := by
    simpa [gridToGroup, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (congrFun h i).symm
  have hmod : Int.ModEq (4 * (Q : ℤ)) ((c i : ℕ) : ℤ)
      (((t i : ℕ) : ℤ) + ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (ZMod.intCast_eq_intCast_iff _ _ (4 * Q)).mp
        (by simpa only [Int.cast_add, Int.cast_sub] using hcast)
  have hbound (x : Fin Q) : 0 ≤ ((x : ℕ) : ℤ) ∧ ((x : ℕ) : ℤ) < (Q : ℤ) := by
    refine ⟨Int.natCast_nonneg _, ?_⟩
    exact_mod_cast x.isLt
  exact grid_modular_collision (Q : ℤ) _ _ _ _
    (hbound (c i)) (hbound (t i)) (hbound (u i)) (hbound (v i)) hmod

theorem grid_sphere_slice_collision {d Q : ℕ} (t c u v : Grid d Q)
    (hsphere : gridSquaredNorm c = gridSquaredNorm t)
    (hslice : gridDot t u = gridDot t v) :
    gridToGroup u + (gridToGroup t - gridToGroup v) = gridToGroup c ↔
      u = v ∧ c = t := by
  constructor
  · intro h
    have hnorm : squaredNorm (gridToReal c) = squaredNorm (gridToReal t) := by
      simp only [squaredNorm_gridToReal, hsphere]
    have hdot : dot (gridToReal t) (gridToReal u) =
        dot (gridToReal t) (gridToReal v) := by
      simp only [dot_gridToReal, hslice]
    have hlift := grid_group_collision_lift t c u v h
    have hreal : ∀ i, gridToReal c i =
        gridToReal t i + gridToReal u i - gridToReal v i := by
      intro i
      dsimp [gridToReal]
      exact_mod_cast hlift i
    obtain ⟨huv, hct⟩ := sphere_slice_collision
      (gridToReal t) (gridToReal c) (gridToReal u) (gridToReal v) hnorm hdot hreal
    exact ⟨gridToReal_injective huv, gridToReal_injective hct⟩
  · rintro ⟨rfl, rfl⟩
    simp [sub_eq_add_neg, add_left_comm]

theorem indexed_grid_collision {S U : Type*} {d Q : ℕ}
    (tag : S → Grid d Q) (point : S → U → Grid d Q)
    (htag : Function.Injective tag)
    (hpoint : ∀ s, Function.Injective (point s))
    (hsphere : ∀ s s', gridSquaredNorm (tag s') = gridSquaredNorm (tag s))
    (hslice : ∀ s i j, gridDot (tag s) (point s i) = gridDot (tag s) (point s j)) :
    ∀ s s' i j,
      gridToGroup (point s i) + (gridToGroup (tag s) - gridToGroup (point s j)) =
        gridToGroup (tag s') ↔ s = s' ∧ i = j := by
  intro s s' i j
  rw [grid_sphere_slice_collision (tag s) (tag s') (point s i) (point s j)
    (hsphere s s') (hslice s i j)]
  constructor
  · rintro ⟨hij, hss⟩
    exact ⟨(htag hss).symm, hpoint s hij⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

theorem exists_modular_separation {d Q K m : ℕ}
    (hK : (d * Q ^ 2 + 1) * K ≤ Q ^ d)
    (hm : (d * Q ^ 2 + 1) * m ≤ Q ^ d) :
    ∃ (tag : Fin K → AuxiliaryGroup d Q)
      (point : Fin K → Fin m → AuxiliaryGroup d Q),
      ∀ s s' i j,
        point s i + (tag s - point s j) = tag s' ↔ s = s' ∧ i = j := by
  classical
  obtain ⟨tags, htags, ⟨radius, hradius⟩, hslices⟩ := grid_tags_slices hK hm
  choose slice hsliceCard level hlevel using
    (fun t : ↥tags => hslices t.val t.property)
  let tagEnum : Fin K ≃ ↥tags := (Finset.equivFinOfCardEq htags).symm
  let sliceEnum (t : ↥tags) : Fin m ≃ ↥(slice t) :=
    (Finset.equivFinOfCardEq (hsliceCard t)).symm
  let tagGrid (s : Fin K) : Grid d Q := (tagEnum s).val
  let pointGrid (s : Fin K) (i : Fin m) : Grid d Q :=
    (sliceEnum (tagEnum s) i).val
  have htag : Function.Injective tagGrid := by
    intro s s' h
    apply tagEnum.injective
    exact Subtype.ext h
  have hpoint : ∀ s, Function.Injective (pointGrid s) := by
    intro s i j h
    apply (sliceEnum (tagEnum s)).injective
    exact Subtype.ext h
  have hsphere : ∀ s s', gridSquaredNorm (tagGrid s') = gridSquaredNorm (tagGrid s) := by
    intro s s'
    have hc := (hradius (tagEnum s').val (tagEnum s').property).trans
      (hradius (tagEnum s).val (tagEnum s).property).symm
    exact congrArg Fin.val hc
  have hslice : ∀ s i j,
      gridDot (tagGrid s) (pointGrid s i) = gridDot (tagGrid s) (pointGrid s j) := by
    intro s i j
    have hc := (hlevel (tagEnum s) (sliceEnum (tagEnum s) i).val
      (sliceEnum (tagEnum s) i).property).trans
      (hlevel (tagEnum s) (sliceEnum (tagEnum s) j).val
        (sliceEnum (tagEnum s) j).property).symm
    exact congrArg Fin.val hc
  exact ⟨fun s => gridToGroup (tagGrid s), fun s i => gridToGroup (pointGrid s i),
    indexed_grid_collision tagGrid pointGrid htag hpoint hsphere hslice⟩

theorem card_auxiliaryGroup (d Q : ℕ) [NeZero (4 * Q)] :
    Fintype.card (AuxiliaryGroup d Q) = (4 * Q) ^ d := by
  simp [AuxiliaryGroup, ZMod.card]

end MatrixMultiplication.Foundation.Separation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexGroupTensor
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation

variable (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]

def groupTensor : Tensor ℂ G G G := fun a b c => if a + b = c then 1 else 0

theorem groupTensor_fourier :
    groupTensor G = fun a b c => ∑ χ : AddChar G ℂ,
      Tensor.rankOne (fun a => χ a / (Fintype.card G : ℂ))
        (fun b => χ b) (fun c => χ (-c)) a b c := by
  funext a b c
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    groupTensor G a b c =
        (∑ χ : AddChar G ℂ, χ (a + b - c)) / (Fintype.card G : ℂ) := by
      rw [AddChar.sum_apply_eq_ite]
      by_cases h : a + b = c
      · simp [groupTensor, h, hcard]
      · simp [groupTensor, h, sub_ne_zero.mpr h]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro χ hχ
      simp only [Tensor.rankOne, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring

theorem groupTensor_rankAtMost : Tensor.RankAtMost (groupTensor G) (Fintype.card G) := by
  rw [groupTensor_fourier]
  simpa only [AddChar.card_eq] using
    Tensor.rankAtMost_sum_rankOne
      (fun χ : AddChar G ℂ => fun a => χ a / (Fintype.card G : ℂ))
      (fun χ : AddChar G ℂ => fun b => χ b)
      (fun χ : AddChar G ℂ => fun c => χ (-c))

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexAuxiliarySeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

instance auxiliarySeparation_modulus_neZero (K : ℕ) :
    NeZero (4 * Separation.gridWidth K) :=
  ⟨Nat.mul_ne_zero (by decide)
    (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2)
      (Separation.gridWidth_ge_two K)))⟩

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexTypeCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A I J : Type*} [Fintype A] [DecidableEq A] [Fintype I] [Fintype J]
  [DecidableEq I]

def wordPopulation (w : I → A) (a : A) : ℕ := Fintype.card {i // w i = a}

omit [DecidableEq I] in
theorem wordPopulation_sum (w : I → A) :
    ∑ a, wordPopulation w a = Fintype.card I := by
  simpa [wordPopulation] using Fintype.card_congr (Equiv.sigmaFiberEquiv w)

omit [Fintype A] [DecidableEq I] in
theorem wordPopulation_reindex (w : I → A) (e : J ≃ I) (a : A) :
    wordPopulation (w ∘ e) a = wordPopulation w a :=
  Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

abbrev ExactWords (counts : A → ℕ) :=
  {w : Fin (∑ a, counts a) → A // ∀ a, wordPopulation w a = counts a}

theorem wordPopulation_sigma_fst (counts : A → ℕ) (a : A) :
    wordPopulation (fun i : Σ b, Fin (counts b) => i.1) a = counts a := by
  let e : {i : Σ b, Fin (counts b) // i.1 = a} ≃ Fin (counts a) :=
    { toFun := fun i => i.property ▸ i.val.2
      invFun := fun i => ⟨⟨a, i⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨b, i⟩, h⟩
        cases h
        rfl
      right_inv := by intro i; rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem exactWords_nonempty (counts : A → ℕ) : Nonempty (ExactWords counts) := by
  classical
  let e : Fin (∑ a, counts a) ≃ (Σ a, Fin (counts a)) :=
    Fintype.equivOfCardEq (by simp)
  refine ⟨⟨(fun i : Σ a, Fin (counts a) => i.1) ∘ e, ?_⟩⟩
  intro a
  rw [wordPopulation_reindex, wordPopulation_sigma_fst]

omit [Fintype A] [DecidableEq I] in
theorem samePopulation_iff_permutation (w v : I → A) :
    (∀ a, wordPopulation v a = wordPopulation w a) ↔
      ∃ e : Equiv.Perm I, w ∘ e = v := by
  classical
  constructor
  · intro h
    let es : ∀ a, {i // v i = a} ≃ {i // w i = a} :=
      fun a => Fintype.equivOfCardEq (h a)
    refine ⟨Equiv.ofFiberEquiv es, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map es i
  · rintro ⟨e, rfl⟩ a
    exact wordPopulation_reindex w e a

theorem samePopulation_card_mul (w : I → A) :
    Fintype.card {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} *
      (∏ a, (wordPopulation w a).factorial) = (Fintype.card I).factorial := by
  classical
  let G := DomMulAct (Equiv.Perm I)
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  let eOrbit : {v : I → A // ∀ a, wordPopulation v a = wordPopulation w a} ≃
      MulAction.orbit G w :=
    Equiv.subtypeEquivRight fun v => by
      rw [samePopulation_iff_permutation, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨e, he⟩
        exact ⟨DomMulAct.mk e, he⟩
      · rintro ⟨g, hg⟩
        exact ⟨DomMulAct.mk.symm g, hg⟩
  let eStab : MulAction.stabilizer G w ≃
      {e : Equiv.Perm I // w ∘ e = w} :=
    Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
  have hstab : Fintype.card (MulAction.stabilizer G w) =
      ∏ a, (wordPopulation w a).factorial := by
    rw [Fintype.card_congr eStab]
    exact DomMulAct.stabilizer_card w
  have hgroup : Fintype.card G = (Fintype.card I).factorial :=
    (Fintype.card_congr DomMulAct.mk.symm).trans Fintype.card_perm
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G w
  rw [← Fintype.card_congr eOrbit, hstab, hgroup] at h
  exact h

theorem exactWords_card (counts : A → ℕ) :
    Fintype.card (ExactWords counts) = Nat.multinomial Finset.univ counts := by
  classical
  obtain ⟨w⟩ := exactWords_nonempty counts
  let e : ExactWords counts ≃
      {v : Fin (∑ a, counts a) → A // ∀ a,
        wordPopulation v a = wordPopulation w.val a} :=
    Equiv.subtypeEquivRight fun v => by simp only [w.property]
  have h := samePopulation_card_mul w.val
  rw [← Fintype.card_congr e] at h
  simp only [w.property, Fintype.card_fin] at h
  exact Nat.eq_div_of_mul_eq_left
    (ne_of_gt (Nat.prod_factorial_pos Finset.univ counts)) h

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

abbrev PopulationWords (I : Type*) [Fintype I] (counts : A → ℕ) :=
  {w : I → A // ∀ a, wordPopulation w a = counts a}

noncomputable def populationWordsEquiv (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) : PopulationWords I counts ≃ ExactWords counts := by
  let e : I ≃ Fin (∑ a, counts a) := Fintype.equivFinOfCardEq h
  exact
    { toFun := fun w =>
        ⟨w.val ∘ e.symm, fun a => (wordPopulation_reindex w.val e.symm a).trans (w.property a)⟩
      invFun := fun w =>
        ⟨w.val ∘ e, fun a => (wordPopulation_reindex w.val e a).trans (w.property a)⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp }

theorem populationWords_card (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) :
    Fintype.card (PopulationWords I counts) = Nat.multinomial Finset.univ counts := by
  rw [Fintype.card_congr (populationWordsEquiv counts h), exactWords_card]

abbrev ConditionalWords (w : I → A) (counts : A → B → ℕ) :=
  {r : I → B // ∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b}

def fiberWordEquiv (w : I → A) : (I → B) ≃ (∀ a, {i // w i = a} → B) where
  toFun r _ i := r i.val
  invFun r i := r (w i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv := by
    intro r
    funext a i
    rcases i with ⟨i, hi⟩
    cases hi
    rfl

omit [Fintype A] [Fintype B] [DecidableEq I] in
theorem wordPopulation_fiber (w : I → A) (r : I → B) (a : A) (b : B) :
    wordPopulation (fun i : {i // w i = a} => r i.val) b =
      Fintype.card {i // w i = a ∧ r i = b} :=
  Fintype.card_congr
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun i => w i = a) (fun i => r i = b))

def conditionalWordsEquiv (w : I → A) (counts : A → B → ℕ) :
    ConditionalWords w counts ≃ ∀ a, PopulationWords {i // w i = a} (counts a) := by
  let e : ConditionalWords w counts ≃
      {r : ∀ a, {i // w i = a} → B // ∀ a b, wordPopulation (r a) b = counts a b} :=
    Equiv.subtypeEquiv (fiberWordEquiv w) fun r => by
      change (∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b) ↔
        ∀ a b, wordPopulation (fun i : {i // w i = a} => r i.val) b = counts a b
      simp only [wordPopulation_fiber]
  exact e.trans (Equiv.subtypePiEquivPi
    (β := fun a : A => {i // w i = a} → B)
    (p := fun a r => ∀ b, wordPopulation r b = counts a b))

theorem conditionalWords_card (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Fintype.card (ConditionalWords w counts) =
      ∏ a, Nat.multinomial Finset.univ (counts a) := by
  rw [Fintype.card_congr (conditionalWordsEquiv w counts), Fintype.card_pi]
  exact Finset.prod_congr rfl fun a _ => populationWords_card (counts a) (h a)

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexHierarchyTypeCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

universe u v

def pushforwardCounts {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (b : B) : ℕ := by
  classical
  exact ∑ a, if label a = b then counts a else 0

theorem pushforwardCounts_apply {A B : Type*} [Fintype A]
    (counts : A → ℕ) (label : A → B) (hinjective : Function.Injective label)
    (a : A) : pushforwardCounts counts label (label a) = counts a := by
  classical
  simp [pushforwardCounts, hinjective.eq_iff]

theorem pushforwardCounts_sum_pair {A B C : Type*}
    [Fintype A] [Fintype C] (counts : A → ℕ)
    (coarse : A → B) (fine : A → C) (b : B) :
    (∑ c, pushforwardCounts counts (fun a => (coarse a, fine a)) (b, c)) =
      pushforwardCounts counts coarse b := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : coarse a = b
  · simp [Prod.mk.injEq, hab]
  · simp [Prod.mk.injEq, hab]

namespace LabelHierarchyCounts

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)]

def refinementCount (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ) : ℕ :=
  ∏ r : LabelRecord Label n,
    Nat.multinomial Finset.univ (fun s : Label n => counts (n + 1) (r, s))

def sourcePrefixCounts {A : Type v} [Fintype A] (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) : LabelRecord Label n → ℕ :=
  pushforwardCounts counts (labelRecordOf labels n)

theorem sourcePrefixCounts_compatible {A : Type v} [Fintype A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ)
    (r : LabelRecord Label n) :
    sourcePrefixCounts counts labels n r =
      ∑ s : Label n, sourcePrefixCounts counts labels (n + 1) (r, s) :=
  (pushforwardCounts_sum_pair counts (labelRecordOf labels n) (labels n) r).symm

end LabelHierarchyCounts
end MatrixMultiplication.Foundation

end

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

def fiberTransform (MX : X → A' → A → K) (MY : Y → B' → B → K)
    (MZ : Z → C' → C → K) (T : Tensor K (X × A) (Y × B) (Z × C)) :
    Tensor K (X × A') (Y × B') (Z × C') :=
  fun x y z => ∑ a, ∑ b, ∑ c,
    MX x.1 x.2 a * MY y.1 y.2 b * MZ z.1 z.2 c *
      T (x.1, a) (y.1, b) (z.1, c)

end LocalMaps
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexLabelHierarchySeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace LabelHierarchySeparation

section ExactPools

variable {X Y Z Prefix Label : Type*} [DecidableEq Label]

noncomputable def poolEnumeration (pool : Prefix → Finset Label) (k : ℕ)
    (counts : ∀ p, (pool p).card = k) : ∀ p, ↥(pool p) ≃ Fin k :=
  fun p => Finset.equivFinOfCardEq (counts p)

noncomputable def poolAuxiliaryCost (k : ℕ) : ℕ :=
  if k = 1 then 1 else Separation.gridGroupOrder k

abbrev PoolAuxiliaryGroup (k : ℕ) :=
  Separation.AuxiliaryGroup (Separation.gridDimension k) (Separation.gridWidth k)

noncomputable def poolAuxiliaryTensor (k : ℕ) :
    Tensor ℂ (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) :=
  if k = 1 then Tensor.rankOne (fun _ => 1) (fun _ => 1) (fun _ => 1)
  else groupTensor (PoolAuxiliaryGroup k)

theorem poolAuxiliaryTensor_rankAtMost (k : ℕ) :
    Tensor.RankAtMost (poolAuxiliaryTensor k) (poolAuxiliaryCost k) := by
  classical
  by_cases hk : k = 1
  · simpa only [poolAuxiliaryTensor, poolAuxiliaryCost, ite_eq_left hk] using
      Tensor.rankOne_rankAtMost (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
        (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
        (fun _ : PoolAuxiliaryGroup k => (1 : ℂ))
  · simpa only [poolAuxiliaryTensor, poolAuxiliaryCost, ite_eq_right hk,
      PoolAuxiliaryGroup, Separation.card_auxiliaryGroup, Separation.gridGroupOrder]
      using groupTensor_rankAtMost (PoolAuxiliaryGroup k)

end ExactPools

end LabelHierarchySeparation
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

namespace LabelHierarchySeparation

theorem population_le_poolAuxiliaryCost (k : ℕ) : k ≤ poolAuxiliaryCost k := by
  unfold poolAuxiliaryCost
  split_ifs with hk
  · simp [hk]
  · exact Separation.population_le_gridGroupOrder k

end LabelHierarchySeparation

end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexStageHierarchyResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.StageHierarchyResources

open Filter LabelHierarchyCounts
open scoped BigOperators Topology

universe u v

local instance (priority := low) instDecidableEq_solutions {B : Type*} : DecidableEq B := Classical.decEq B

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

def stageRefinementCount (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) : ℕ :=
  refinementCount (sourcePrefixCounts (fun a => t * counts a) labels) n

theorem stageRefinementCount_pos (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) : 0 < stageRefinementCount counts labels n t := by
  unfold stageRefinementCount refinementCount
  exact Finset.prod_pos (fun r _ => Nat.multinomial_pos _ _)

theorem stageConditionalWords_card {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    Fintype.card (ConditionalWords w
      (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))) =
      stageRefinementCount counts labels n t := by
  exact conditionalWords_card w
    (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))
    (fun r => (hword r).trans
      (sourcePrefixCounts_compatible (fun a => t * counts a) labels n r))

theorem stageConditionalPool_card {Position : Type*} [Fintype Position]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (w : Position → LabelRecord Label n)
    (hword : ∀ r, wordPopulation w r = sourcePrefixCounts (fun a => t * counts a) labels n r) :
    (Finset.univ.filter (fun fine : Position → Label n =>
      ∀ r s, Fintype.card {i // w i = r ∧ fine i = s} =
        sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))).card =
      stageRefinementCount counts labels n t := by
  simpa only [ConditionalWords, Fintype.card_subtype] using
    stageConditionalWords_card counts labels n t w hword

def stageCost (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ) : ℕ :=
  LabelHierarchySeparation.poolAuxiliaryCost (stageRefinementCount counts labels n t)

def stagePairingProduct (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) : ℕ :=
  ∏ n : Fin depth, stageRefinementCount counts labels n.val t

def stageAuxiliaryBudget (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) : ℕ :=
  ∏ n : Fin depth, stageCost counts labels n.val t

theorem stagePairingProduct_succ (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) :
    stagePairingProduct counts labels (n + 1) t =
      stagePairingProduct counts labels n t * stageRefinementCount counts labels n t := by
  exact Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => stageRefinementCount counts labels i.val t)

theorem stageAuxiliaryBudget_succ (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n t : ℕ) :
    stageAuxiliaryBudget counts labels (n + 1) t =
      stageAuxiliaryBudget counts labels n t * stageCost counts labels n t := by
  exact Fin.prod_univ_castSucc
    (fun i : Fin (n + 1) => stageCost counts labels i.val t)

end MatrixMultiplication.Foundation.StageHierarchyResources

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ConditionalLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Filter
open scoped Topology BigOperators Classical

inductive ReaderPair where
  | xy | xz | yz
  deriving DecidableEq

end MatrixMultiplication

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

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {X Y Z : Type uCoord}

def Leaf (S : FlaggedTensor X Y Z) :=
  {p : X × Y × Z // S.tensor p.1 p.2.1 p.2.2 ≠ 0}

def Coordinate (X Y Z : Type uCoord) : Color → Type uCoord
  | .B => X
  | .A => Z
  | .C => Y

def coordinate (p : X × Y × Z) : (c : Color) → Coordinate X Y Z c
  | .B => p.1
  | .A => p.2.2
  | .C => p.2.1

def ownerFlag (S : FlaggedTensor X Y Z) : (c : Color) → Coordinate X Y Z c → Prop
  | .B => S.flagB
  | .A => S.flagA
  | .C => S.flagC

def leafColor (S : FlaggedTensor X Y Z) (a : Leaf S) : Color :=
  if S.flagB a.val.1 then .B else if S.flagA a.val.2.2 then .A else .C

theorem leafColor_eq_iff (S : FlaggedTensor X Y Z) (a : Leaf S) (c : Color) :
    leafColor S a = c ↔ ownerFlag S c (coordinate a.val c) := by
  have h := S.one_hot _ _ _ a.property
  cases c <;>
    by_cases hb : S.flagB a.val.1 <;>
    by_cases ha : S.flagA a.val.2.2 <;>
    by_cases hc : S.flagC a.val.2.1 <;>
    simp_all [leafColor, ownerFlag, coordinate]

theorem complete_supported (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) :
    Tensor.power S.tensor m a.val.1 a.val.2.1 a.val.2.2 ≠ 0 := by
  have h := a.property
  change (if weight S center m a.val.1 a.val.2.1 a.val.2.2 = 1 then
    Tensor.power S.tensor m a.val.1 a.val.2.1 a.val.2.2 else 0) ≠ 0 at h
  split_ifs at h with hw
  · exact h
  · exact False.elim (h rfl)

def slot (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) (i : Fin m) : Leaf S :=
  ⟨(a.val.1 i, a.val.2.1 i, a.val.2.2 i),
    (Finset.prod_ne_zero_iff.mp (complete_supported S center m a)) i (Finset.mem_univ i)⟩

theorem raisedFlag_iff_output {I : Type*} (p : I → Color) (center output : Color)
    (active : raisedFlag center output (fun i => p i = output))
    (allowed : ∀ i, p i = center ∨ p i = output) (c : Color) :
    raisedFlag center c (fun i => p i = c) ↔ c = output := by
  constructor
  · intro hc
    by_contra hco
    by_cases hcc : center = c
    · subst c
      have hne : center ≠ output := hco
      have ha : ∃ i, p i = output := by
        simpa only [raisedFlag, ite_eq_right hne] using active
      have hall : ∀ i, p i = center := by
        simpa only [raisedFlag, ite_eq_left rfl, ite_true, if_true] using hc
      obtain ⟨i, hi⟩ := ha
      exact hne ((hall i).symm.trans hi)
    · have ha : ∃ i, p i = c := by
        simpa only [raisedFlag, ite_eq_right hcc] using hc
      obtain ⟨i, hi⟩ := ha
      rcases allowed i with h | h
      · exact hcc (h.symm.trans hi)
      · exact hco (hi.symm.trans h)
  · rintro rfl
    exact active

def wordCoordinates {m : ℕ} (S : FlaggedTensor X Y Z) (w : Fin m → Leaf S) :
    (Fin m → X) × (Fin m → Y) × (Fin m → Z) :=
  (fun i => (w i).val.1, fun i => (w i).val.2.1, fun i => (w i).val.2.2)

theorem word_ownerFlag (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (w : Fin m → Leaf S) (c : Color) :
    ownerFlag (complete S center m) c (coordinate (wordCoordinates S w) c) ↔
      raisedFlag center c (fun i => leafColor S (w i) = c) := by
  have heq : (fun i => leafColor S (w i) = c) =
      (fun i => ownerFlag S c (coordinate (w i).val c)) := by
    funext i
    exact propext (leafColor_eq_iff S (w i) c)
  rw [heq]
  cases c <;> rfl

def packLeaf (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (w : Fin m → Leaf S)
    (active : raisedFlag center output (fun i => leafColor S (w i) = output))
    (allowed : ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output) :
    Leaf (complete S center m) := by
  have hflag (c : Color) :
      ownerFlag (complete S center m) c (coordinate (wordCoordinates S w) c) ↔
        c = output :=
    (word_ownerFlag S center m w c).trans
      (raisedFlag_iff_output _ center output active allowed c)
  have hw : weight S center m (wordCoordinates S w).1
      (wordCoordinates S w).2.1 (wordCoordinates S w).2.2 = 1 := by
    have hb := hflag .B
    have ha := hflag .A
    have hc := hflag .C
    change flagB S center m (wordCoordinates S w).1 ↔ Color.B = output at hb
    change flagA S center m (wordCoordinates S w).2.2 ↔ Color.A = output at ha
    change flagC S center m (wordCoordinates S w).2.1 ↔ Color.C = output at hc
    simp only [weight, hb, ha, hc]
    cases output <;> simp
  refine ⟨wordCoordinates S w, ?_⟩
  rw [complete_tensor, ite_eq_left hw]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (w i).property

@[simp] theorem slot_packLeaf (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (w : Fin m → Leaf S) (active) (allowed) :
    slot S center m (packLeaf S center output m w active allowed) = w := by
  funext i
  apply Subtype.ext
  rfl

def RetainedLeaf (S : FlaggedTensor X Y Z) (first second : Color) :=
  {a : Leaf S // leafColor S a = first ∨ leafColor S a = second}

def terminationFirstRead (S : FlaggedTensor X Y Z) (first second : Color)
    (u : Coordinate X Y Z first) : Color :=
  if ownerFlag S first u then first else second

def terminationSecondRead (S : FlaggedTensor X Y Z) (first second : Color)
    (u : Coordinate X Y Z second) : Color :=
  if ownerFlag S second u then second else first

theorem termination_readable (S : FlaggedTensor X Y Z) (first second : Color)
    (a : RetainedLeaf S first second) :
    terminationFirstRead S first second (coordinate a.val.val first) = leafColor S a.val ∧
    terminationSecondRead S first second (coordinate a.val.val second) = leafColor S a.val := by
  have hf := leafColor_eq_iff S a.val first
  have hs := leafColor_eq_iff S a.val second
  constructor
  · by_cases h : leafColor S a.val = first
    · simp only [terminationFirstRead, ite_eq_left (hf.mp h), h]
    · rw [terminationFirstRead, ite_eq_right (fun hflag => h (hf.mpr hflag))]
      exact (Or.resolve_left a.property h).symm
  · by_cases h : leafColor S a.val = second
    · simp only [terminationSecondRead, ite_eq_left (hs.mp h), h]
    · rw [terminationSecondRead, ite_eq_right (fun hflag => h (hs.mpr hflag))]
      exact (Or.resolve_right a.property h).symm

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v

def firstSide : ReaderPair → Color
  | .xy => .B
  | .xz => .B
  | .yz => .C

def secondSide : ReaderPair → Color
  | .xy => .C
  | .xz => .A
  | .yz => .A

end MatrixMultiplication.CompletionLabels.TopologicalFlatten

namespace MatrixMultiplication.CompletionLabels

open RecursiveCompletion TopologicalFlatten
attribute [local instance] Classical.propDecidable Classical.decEq

variable {X Y Z : Type uCoord}

def ownerPair : Color → Color → ReaderPair
  | .B, .A | .A, .B => .xz
  | .A, .C | .C, .A => .yz
  | _, _ => .xy

theorem ownerPair_first_mem (center output : Color) (h : center ≠ output) :
    firstSide (ownerPair center output) = center ∨
      firstSide (ownerPair center output) = output := by
  cases center <;> cases output <;> simp_all [ownerPair, firstSide]

theorem ownerPair_second_mem (center output : Color) (h : center ≠ output) :
    secondSide (ownerPair center output) = center ∨
      secondSide (ownerPair center output) = output := by
  cases center <;> cases output <;> simp_all [ownerPair, secondSide]

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten

open MatrixMultiplication.Foundation RecursiveCompletion

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v w z u' v' w'

structure Program (A : Type u) (Coord : Color → Type v)
    (Context : Type z) (Code : Type w) (depth : ℕ) where
  context : A → Context
  view : (side : Color) → A → Coord side
  pair : ℕ → ReaderPair
  labels : ℕ → A → Code
  read : (n : ℕ) → (side : Color) → Context → (Fin n → Code) → Coord side → Code
  readable : ∀ n, n < depth → ∀ a side,
    (side = firstSide (pair n) ∨ side = secondSide (pair n)) →
      read n side (context a) (fun j => labels j.val a) (view side a) = labels n a

namespace Program

variable {A : Type u} {Coord : Color → Type v}
  {Context : Type z} {Code : Type w} {depth : ℕ}

def Complete (p : Program A Coord Context Code depth) : Prop :=
  ∀ a b, p.context a = p.context b →
    (∀ n, n < depth → p.labels n a = p.labels n b) → a = b

def pullback {B : Type u'} {NewCoord : Color → Type v'}
    (p : Program A Coord Context Code depth) (source : B → A)
    (view : (side : Color) → B → NewCoord side)
    (project : (side : Color) → NewCoord side → Coord side)
    (projects : ∀ side b, project side (view side b) = p.view side (source b)) :
    Program B NewCoord Context Code depth where
  context b := p.context (source b)
  view := view
  pair := p.pair
  labels n b := p.labels n (source b)
  read n side ctx prior own := p.read n side ctx prior (project side own)
  readable := by
    intro n hn b side hs
    simpa only [projects side b] using p.readable n hn (source b) side hs

def recode {NewCode : Type w'} (p : Program A Coord Context Code depth)
    (encode : Code → NewCode) (decode : NewCode → Code)
    (roundtrip : Function.LeftInverse decode encode) :
    Program A Coord Context NewCode depth where
  context := p.context
  view := p.view
  pair := p.pair
  labels n a := encode (p.labels n a)
  read n side ctx prior own := encode (p.read n side ctx (fun j => decode (prior j)) own)
  readable := by
    intro n hn a side hs
    have hprior : (fun j : Fin n => decode (encode (p.labels j.val a))) =
        (fun j : Fin n => p.labels j.val a) := by
      funext j
      exact roundtrip _
    dsimp
    rw [hprior, p.readable n hn a side hs]

def single (context : A → Context) (view : (side : Color) → A → Coord side)
    (pair : ReaderPair) (label : A → Code)
    (read : (side : Color) → Context → Coord side → Code)
    (correct : ∀ a side, (side = firstSide pair ∨ side = secondSide pair) →
      read side (context a) (view side a) = label a) :
    Program A Coord Context Code 1 where
  context := context
  view := view
  pair _ := pair
  labels _ := label
  read _ side ctx _ own := read side ctx own
  readable := by
    intro n hn a side hs
    exact correct a side hs

def appendLabel (d : ℕ) (f g : ℕ → A → Code) (n : ℕ) (a : A) : Code :=
  if n < d then f n a else g (n - d) a

def takeArray {n d : ℕ} (h : d ≤ n) (prior : Fin n → Code) : Fin d → Code :=
  fun j => prior ⟨j.val, lt_of_lt_of_le j.isLt h⟩

def dropArray {n d : ℕ} (h : d ≤ n) (prior : Fin n → Code) : Fin (n - d) → Code :=
  fun j => prior ⟨d + j.val, by omega⟩

def append {OtherContext : Type z} {d e : ℕ}
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a) :
    Program A Coord Context Code (d + e) where
  context := p.context
  view := p.view
  pair n := if n < d then p.pair n else q.pair (n - d)
  labels := appendLabel d p.labels q.labels
  read n side ctx prior own :=
    if h : n < d then p.read n side ctx prior own
    else q.read (n - d) side
      (derive ctx (takeArray (Nat.le_of_not_gt h) prior))
      (dropArray (Nat.le_of_not_gt h) prior) own
  readable := by
    intro n hn a side hs
    by_cases h : n < d
    · have hprior : (fun j : Fin n => appendLabel d p.labels q.labels j.val a) =
          (fun j : Fin n => p.labels j.val a) := by
        funext j
        simp [appendLabel, lt_trans j.isLt h]
      simp only [ite_eq_left h] at hs
      simp only [dite_eq_left h]
      rw [hprior]
      simpa only [appendLabel, ite_eq_left h] using p.readable n h a side hs
    · have hd : d ≤ n := Nat.le_of_not_gt h
      have hhead : takeArray hd (fun j : Fin n => appendLabel d p.labels q.labels j.val a) =
          (fun j : Fin d => p.labels j.val a) := by
        funext j
        simp [takeArray, appendLabel, j.isLt]
      have htail : dropArray hd (fun j : Fin n => appendLabel d p.labels q.labels j.val a) =
          (fun j : Fin (n - d) => q.labels j.val a) := by
        funext j
        have hj : ¬ d + j.val < d := by omega
        simp [dropArray, appendLabel, hj]
      have hnq : n - d < e := by omega
      simp only [ite_eq_right h] at hs
      simp only [dite_eq_right h]
      rw [hhead, htail, derive_correct a, sameView side a]
      simpa only [appendLabel, ite_eq_right h] using q.readable (n - d) hnq a side hs

end Program
end MatrixMultiplication.CompletionLabels.TopologicalFlatten

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten
attribute [local instance] Classical.propDecidable Classical.decEq

variable {X Y Z : Type uCoord}

def rootColor (n : ℕ) : Color := if n = 0 then .B else if n = 1 then .A else .C

def rootIndex : Color → Fin 3
  | .B => 0
  | .A => 1
  | .C => 2

@[simp] theorem rootColor_rootIndex (c : Color) : rootColor (rootIndex c).val = c := by
  cases c <;> simp [rootIndex, rootColor]

end MatrixMultiplication.CompletionLabels

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

universe w
variable {X Y Z : Type uCoord} {Code : Type w} {depth : ℕ}

structure ReadableTensor (S : FlaggedTensor X Y Z) where
  Code : Type
  [finiteCode : Fintype Code]
  [inhabitedCode : Inhabited Code]
  depth : ℕ
  program : Program (Leaf S) (Coordinate X Y Z) Color Code depth
  context_eq : ∀ a, program.context a = leafColor S a
  view_eq : ∀ side a, program.view side a = coordinate a.val side
  complete : program.Complete

attribute [instance] ReadableTensor.finiteCode ReadableTensor.inhabitedCode

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {X Y Z : Type uCoord} {Code : Type u} {depth : ℕ}

def terminationSideRead (S : FlaggedTensor X Y Z) (first second side : Color)
    (own : Coordinate X Y Z side) : Color :=
  if side = first then
    if ownerFlag S side own then first else second
  else if ownerFlag S side own then second else first

theorem terminationSideRead_correct (S : FlaggedTensor X Y Z)
    (first second : Color) (distinct : first ≠ second)
    (a : RetainedLeaf S first second) (side : Color)
    (hs : side = first ∨ side = second) :
    terminationSideRead S first second side (coordinate a.val.val side) =
      leafColor S a.val := by
  rcases hs with h | h
  · subst side
    simpa only [terminationSideRead, ite_eq_left rfl, ite_true, if_true, terminationFirstRead] using
      (termination_readable S first second a).1
  · subst side
    simpa only [terminationSideRead, ite_eq_right (Ne.symm distinct), terminationSecondRead] using
      (termination_readable S first second a).2

def terminationRoot (S : FlaggedTensor X Y Z) (first second : Color)
    (distinct : first ≠ second) :
    Program (RetainedLeaf S first second) (Coordinate X Y Z) PUnit Color 1 :=
  Program.single (fun _ => PUnit.unit)
    (fun side a => coordinate a.val.val side)
    (ownerPair first second) (fun a => leafColor S a.val)
    (fun side _ own => terminationSideRead S first second side own)
    (by
      intro a side hs
      apply terminationSideRead_correct S first second distinct a side
      rcases hs with h | h
      · rw [h]
        exact ownerPair_first_mem first second distinct
      · rw [h]
        exact ownerPair_second_mem first second distinct)

def terminationInherited (S : FlaggedTensor X Y Z) (first second : Color)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (RetainedLeaf S first second) (Coordinate X Y Z) Color Code depth :=
  p.pullback Subtype.val (fun side a => coordinate a.val.val side) (fun _ => id)
    (fun side a => (view_eq side a.val).symm)

def terminationDecodeColor (fallback : Color) : Color ⊕ Code → Color
  | .inl color => color
  | .inr _ => fallback

def terminationDecodeOld [Inhabited Code] : Color ⊕ Code → Code
  | .inl _ => default
  | .inr code => code

def terminationProgram [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (RetainedLeaf S first second) (Coordinate X Y Z)
      PUnit (Color ⊕ Code) (1 + depth) :=
  ((terminationRoot S first second distinct).recode Sum.inl
    (terminationDecodeColor first) (fun _ => rfl)).append
    ((terminationInherited S first second p view_eq).recode Sum.inr
      terminationDecodeOld (fun _ => rfl))
    (by intro side a; rfl)
    (fun _ prior => terminationDecodeColor first (prior 0))
    (by
      intro a
      change leafColor S a.val = p.context a.val
      exact (context_eq a.val).symm)

@[simp] theorem terminationProgram_context [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (a : RetainedLeaf S first second) :
    (terminationProgram S first second distinct p context_eq view_eq).context a =
      PUnit.unit := rfl

@[simp] theorem terminationProgram_view [Inhabited Code]
    (S : FlaggedTensor X Y Z) (first second : Color) (distinct : first ≠ second)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (side : Color) (a : RetainedLeaf S first second) :
    (terminationProgram S first second distinct p context_eq view_eq).view side a =
      coordinate a.val.val side := rfl

end MatrixMultiplication.CompletionLabels

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexConditionalPrefixWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.ConditionalPrefixWords

open LabelHierarchyCounts StageHierarchyResources
open scoped BigOperators

universe u v w

local instance (priority := low) instDecidableEq_solutions {B : Type*} : DecidableEq B := Classical.decEq B

instance labelRecordZero_subsingleton {Label : ℕ → Type v} :
    Subsingleton (LabelRecord Label 0) := by
  change Subsingleton PUnit
  infer_instance

theorem population_fst {B C Position : Type*}
    [Fintype B] [Fintype C] [Fintype Position]
    (word : Position → B × C) (b : B) :
    wordPopulation (fun i => (word i).1) b = ∑ c, wordPopulation word (b, c) := by
  calc
    wordPopulation (fun i => (word i).1) b =
        ∑ c, wordPopulation (fun i : {i // (word i).1 = b} => (word i.val).2) c :=
      (wordPopulation_sum _).symm
    _ = ∑ c, Fintype.card {i // (word i).1 = b ∧ (word i).2 = c} := by
      apply Finset.sum_congr rfl
      intro c hc
      exact wordPopulation_fiber (fun i => (word i).1) (fun i => (word i).2) b c
    _ = ∑ c, wordPopulation word (b, c) := by
      apply Finset.sum_congr rfl
      intro c hc
      simp only [wordPopulation, Prod.ext_iff]

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

abbrev ExactPrefix (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (Position : Type w) [Fintype Position] :=
  PopulationWords Position (sourcePrefixCounts (fun a => t * counts a) labels n)

variable {Position : Type w} [Fintype Position]
variable {counts : A → ℕ} {labels : ∀ n, A → Label n} {n t : ℕ}

abbrev conditionalPool (old : ExactPrefix counts labels n t Position) :=
  ConditionalWords old.val
    (fun r s => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))

def conditionalFinset (old : ExactPrefix counts labels n t Position) :
    Finset (Position → Label n) :=
  Finset.univ.filter (fun fine => ∀ r s,
    Fintype.card {i // old.val i = r ∧ fine i = s} =
      sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s))

@[simp] theorem mem_conditionalFinset (old : ExactPrefix counts labels n t Position)
    (fine : Position → Label n) :
    fine ∈ conditionalFinset old ↔ ∀ r s,
      Fintype.card {i // old.val i = r ∧ fine i = s} =
        sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s) := by
  simp only [conditionalFinset, Finset.mem_filter, Finset.mem_univ, true_and]

def conditionalFinsetEquiv (old : ExactPrefix counts labels n t Position) :
    ↥(conditionalFinset old) ≃ conditionalPool old :=
  Equiv.subtypeEquivRight (fun fine => mem_conditionalFinset old fine)

theorem conditionalFinset_card (old : ExactPrefix counts labels n t Position) :
    (conditionalFinset old).card = stageRefinementCount counts labels n t :=
  stageConditionalPool_card counts labels n t old.val old.property

def conditionalFinsetEquivFin (old : ExactPrefix counts labels n t Position) :
    ↥(conditionalFinset old) ≃ Fin (stageRefinementCount counts labels n t) :=
  LabelHierarchySeparation.poolEnumeration
    (fun previous : ExactPrefix counts labels n t Position => conditionalFinset previous)
    (stageRefinementCount counts labels n t) (fun previous => conditionalFinset_card previous) old

def conditionalPoolEquivFin (old : ExactPrefix counts labels n t Position) :
    conditionalPool old ≃ Fin (stageRefinementCount counts labels n t) :=
  (conditionalFinsetEquiv old).symm.trans (conditionalFinsetEquivFin old)

@[simp] theorem decodedFine_eq_geometryDecode (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    ((conditionalPoolEquivFin old).symm code).val =
      ((LabelHierarchySeparation.poolEnumeration
        (fun previous : ExactPrefix counts labels n t Position => conditionalFinset previous)
        (stageRefinementCount counts labels n t)
        (fun previous => conditionalFinset_card previous) old).symm code).val := rfl

def appendPrefix (old : ExactPrefix counts labels n t Position) (fine : conditionalPool old) :
    ExactPrefix counts labels (n + 1) t Position := by
  classical
  refine ⟨fun i => (old.val i, fine.val i), ?_⟩
  rintro ⟨r, s⟩
  refine Eq.trans ?_ (fine.property r s)
  unfold wordPopulation
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i => Prod.ext_iff)

omit [∀ n, Fintype (Label n)] in
@[simp] theorem appendPrefix_val (old : ExactPrefix counts labels n t Position)
    (fine : conditionalPool old) (i : Position) :
    (appendPrefix old fine).val i = (old.val i, fine.val i) := rfl

def oldPrefix (next : ExactPrefix counts labels (n + 1) t Position) :
    ExactPrefix counts labels n t Position := by
  classical
  refine ⟨fun i => (next.val i).1, ?_⟩
  intro r
  calc
    wordPopulation (fun i => (next.val i).1) r =
        ∑ s : Label n, wordPopulation next.val (r, s) := by
      have h := population_fst next.val r
      refine h.trans ?_
      apply Finset.sum_congr rfl
      intro s hs
      unfold wordPopulation
      exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
    _ = ∑ s : Label n,
        sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact next.property (r, s)
    _ = sourcePrefixCounts (fun a => t * counts a) labels n r :=
      (sourcePrefixCounts_compatible (fun a => t * counts a) labels n r).symm

@[simp] theorem oldPrefix_val (next : ExactPrefix counts labels (n + 1) t Position)
    (i : Position) : (oldPrefix next).val i = (next.val i).1 := rfl

def finePrefix (next : ExactPrefix counts labels (n + 1) t Position) :
    conditionalPool (oldPrefix next) := by
  classical
  refine ⟨fun i => (next.val i).2, ?_⟩
  intro r s
  refine Eq.trans ?_ (next.property (r, s))
  unfold wordPopulation
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun i => by
    change ((next.val i).1 = r ∧ (next.val i).2 = s) ↔ next.val i = (r, s)
    constructor
    · rintro ⟨hfst, hsnd⟩
      exact Prod.ext hfst hsnd
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)

@[simp] theorem finePrefix_val (next : ExactPrefix counts labels (n + 1) t Position)
    (i : Position) : (finePrefix next).val i = (next.val i).2 := rfl

@[simp] theorem oldPrefix_appendPrefix (old : ExactPrefix counts labels n t Position)
    (fine : conditionalPool old) : oldPrefix (appendPrefix old fine) = old := by
  apply Subtype.ext
  rfl

def nextPrefixSigmaEquiv (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (Position : Type w) [Fintype Position] :
    ExactPrefix counts labels (n + 1) t Position ≃
      Σ old : ExactPrefix counts labels n t Position, conditionalPool old where
  toFun next := ⟨oldPrefix next, finePrefix next⟩
  invFun p := appendPrefix p.1 p.2
  left_inv next := by
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    rintro ⟨⟨old, ho⟩, ⟨fine, hf⟩⟩
    rfl

def nextPrefixEquiv (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)
    (Position : Type w) [Fintype Position] :
    ExactPrefix counts labels (n + 1) t Position ≃
      ExactPrefix counts labels n t Position × Fin (stageRefinementCount counts labels n t) :=
  (nextPrefixSigmaEquiv counts labels n t Position).trans
    (Equiv.sigmaEquivProdOfEquiv (fun old => conditionalPoolEquivFin old))

def appendCode (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    ExactPrefix counts labels (n + 1) t Position :=
  appendPrefix old ((conditionalPoolEquivFin old).symm code)

@[simp] theorem appendCode_val (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) (i : Position) :
    (appendCode old code).val i =
      (old.val i, ((conditionalPoolEquivFin old).symm code).val i) := rfl

@[simp] theorem nextPrefixEquiv_symm_apply
    (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    (nextPrefixEquiv counts labels n t Position).symm (old, code) = appendCode old code := rfl

@[simp] theorem nextPrefixEquiv_appendCode
    (old : ExactPrefix counts labels n t Position)
    (code : Fin (stageRefinementCount counts labels n t)) :
    nextPrefixEquiv counts labels n t Position (appendCode old code) = (old, code) :=
  (nextPrefixEquiv counts labels n t Position).apply_symm_apply (old, code)

section Root

omit [∀ n, Fintype (Label n)]

theorem rootPopulation (counts : A → ℕ) (labels : ∀ n, A → Label n) (t : ℕ)
    (r : LabelRecord Label 0) :
    sourcePrefixCounts (fun a => t * counts a) labels 0 r = ∑ a, t * counts a := by
  cases r
  unfold sourcePrefixCounts pushforwardCounts
  apply Finset.sum_congr rfl
  intro a ha
  exact ite_eq_left (Subsingleton.elim _ _)

def rootPrefixWord (counts : A → ℕ) (labels : ∀ n, A → Label n) (t : ℕ)
    (Position : Type w) [Fintype Position]
    (hN : Fintype.card Position = ∑ a, t * counts a) :
    ExactPrefix counts labels 0 t Position := by
  classical
  refine ⟨fun _ => PUnit.unit, ?_⟩
  intro r
  cases r
  calc
    _ = Fintype.card Position := by
      unfold wordPopulation
      exact Fintype.card_congr (Equiv.subtypeUnivEquiv (fun _ => rfl))
    _ = ∑ a, t * counts a := hN
    _ = sourcePrefixCounts (fun a => t * counts a) labels 0 PUnit.unit :=
      (rootPopulation counts labels t PUnit.unit).symm

@[simp] theorem rootPrefixWord_val (counts : A → ℕ) (labels : ∀ n, A → Label n) (t : ℕ)
    (hN : Fintype.card Position = ∑ a, t * counts a) (i : Position) :
    (rootPrefixWord counts labels t Position hN).val i = PUnit.unit := rfl

end Root

section Terminal

omit [∀ n, Fintype (Label n)]

variable {depth : ℕ}

theorem prefixSymbol_in_source_range (word : ExactPrefix counts labels depth t Position)
    (i : Position) : ∃ a : A, labelRecordOf labels depth a = word.val i := by
  by_contra hnone
  have hnot : ∀ a : A, labelRecordOf labels depth a ≠ word.val i := not_exists.mp hnone
  have hzero : sourcePrefixCounts (fun a => t * counts a) labels depth (word.val i) = 0 := by
    simp [sourcePrefixCounts, pushforwardCounts, hnot]
  have hpos : 0 < wordPopulation word.val (word.val i) :=
    Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩
  rw [word.property (word.val i)] at hpos
  exact (Nat.ne_of_gt hpos) hzero

def sourceSymbol (word : ExactPrefix counts labels depth t Position) (i : Position) : A :=
  Classical.choose (prefixSymbol_in_source_range word i)

@[simp] theorem sourceSymbol_record (word : ExactPrefix counts labels depth t Position)
    (i : Position) : labelRecordOf labels depth (sourceSymbol word i) = word.val i :=
  Classical.choose_spec (prefixSymbol_in_source_range word i)

theorem sourceSymbol_eq_iff
    (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : ExactPrefix counts labels depth t Position) (i : Position) (a : A) :
    sourceSymbol word i = a ↔ word.val i = labelRecordOf labels depth a := by
  constructor
  · intro h
    rw [← sourceSymbol_record word i, h]
  · intro h
    exact hinjective ((sourceSymbol_record word i).trans h)

def decodeSourceWord (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : ExactPrefix counts labels depth t Position) :
    PopulationWords Position (fun a => t * counts a) := by
  refine ⟨fun i => sourceSymbol word i, ?_⟩
  intro a
  calc
    wordPopulation (fun i => sourceSymbol word i) a =
        wordPopulation word.val (labelRecordOf labels depth a) :=
      Fintype.card_congr (Equiv.subtypeEquivRight
        (fun i => sourceSymbol_eq_iff hinjective word i a))
    _ = sourcePrefixCounts (fun a => t * counts a) labels depth (labelRecordOf labels depth a) :=
      word.property _
    _ = t * counts a := pushforwardCounts_apply (fun a => t * counts a)
      (labelRecordOf labels depth) hinjective a

def encodeSourceWord (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth t : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : PopulationWords Position (fun a => t * counts a)) :
    ExactPrefix counts labels depth t Position := by
  refine ⟨fun i => labelRecordOf labels depth (word.val i), ?_⟩
  intro r
  by_cases hr : ∃ a : A, labelRecordOf labels depth a = r
  · obtain ⟨a, rfl⟩ := hr
    calc
      wordPopulation (fun i => labelRecordOf labels depth (word.val i))
          (labelRecordOf labels depth a) = wordPopulation word.val a := by
        simp only [wordPopulation, hinjective.eq_iff]
      _ = t * counts a := word.property a
      _ = sourcePrefixCounts (fun a => t * counts a) labels depth (labelRecordOf labels depth a) :=
        (pushforwardCounts_apply (fun a => t * counts a)
          (labelRecordOf labels depth) hinjective a).symm
  · have hnot : ∀ a : A, labelRecordOf labels depth a ≠ r := not_exists.mp hr
    simp [wordPopulation, sourcePrefixCounts, pushforwardCounts, hnot]

@[simp] theorem encodeSourceWord_val (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : PopulationWords Position (fun a => t * counts a)) (i : Position) :
    (encodeSourceWord counts labels depth t hinjective word).val i =
      labelRecordOf labels depth (word.val i) := rfl

@[simp] theorem sourceSymbol_encodeSourceWord (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : PopulationWords Position (fun a => t * counts a)) (i : Position) :
    sourceSymbol (encodeSourceWord counts labels depth t hinjective word) i = word.val i :=
  hinjective (sourceSymbol_record (encodeSourceWord counts labels depth t hinjective word) i)

def sourcePrefixEquiv (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth t : ℕ)
    (Position : Type w) [Fintype Position]
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    ExactPrefix counts labels depth t Position ≃ PopulationWords Position (fun a => t * counts a) where
  toFun word := decodeSourceWord hinjective word
  invFun word := encodeSourceWord counts labels depth t hinjective word
  left_inv word := by
    apply Subtype.ext
    funext i
    exact sourceSymbol_record word i
  right_inv word := by
    apply Subtype.ext
    funext i
    exact sourceSymbol_encodeSourceWord counts labels depth t hinjective word i

@[simp] theorem sourcePrefixEquiv_apply_val (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : ExactPrefix counts labels depth t Position) (i : Position) :
    (sourcePrefixEquiv counts labels depth t Position hinjective word).val i =
      sourceSymbol word i := rfl

@[simp] theorem sourcePrefixEquiv_symm_val (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth t : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth))
    (word : PopulationWords Position (fun a => t * counts a)) (i : Position) :
    ((sourcePrefixEquiv counts labels depth t Position hinjective).symm word).val i =
      labelRecordOf labels depth (word.val i) := rfl

end Terminal

end MatrixMultiplication.Foundation.ConditionalPrefixWords

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCoppersmithWinograd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace CoppersmithWinograd

open Polynomial

def tensor : Tensor ℂ (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => if x.val + y.val + z.val = 2 then 1 else 0

def first : Fin 3 → Fin 3 → Polynomial ℂ
  | 0, x => C (1 / 2) * X ^ x.val
  | 1, x => C (1 / 2) * (-X) ^ x.val
  | 2, x => if x.val = 0 then -1 else 0

def other : Fin 3 → Fin 3 → Polynomial ℂ
  | 0, x => X ^ x.val
  | 1, x => (-X) ^ x.val
  | 2, x => if x.val = 0 then 1 else 0

def polynomial : Tensor (Polynomial ℂ) (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => ∑ i, Tensor.rankOne (first i) (other i) (other i) x y z

theorem rank_bound : Tensor.RankAtMost polynomial 3 :=
  ⟨first, other, other, rfl⟩

theorem polynomial_apply (x y z : Fin 3) :
    polynomial x y z =
      if x.val + y.val + z.val = 2 ∨ x.val + y.val + z.val = 4 ∨
          x.val + y.val + z.val = 6 then
        X ^ (x.val + y.val + z.val) else 0 := by
  have htwo : C (2 : ℂ) = (2 : Polynomial ℂ) := by
    calc
      _ = C ((1 : ℂ) + 1) := by norm_num
      _ = C (1 : ℂ) + C (1 : ℂ) := Polynomial.C_add
      _ = 2 := by norm_num [Polynomial.C_1]
  have hhalf : C (1 / 2 : ℂ) * 2 = (1 : Polynomial ℂ) := by
    calc
      _ = C ((1 / 2 : ℂ) * 2) := by rw [Polynomial.C_mul, htwo]
      _ = 1 := by norm_num
  have hhalf_mul (p : Polynomial ℂ) : C (1 / 2 : ℂ) * p * 2 = p := by
    calc
      _ = (C (1 / 2 : ℂ) * 2) * p := by ring
      _ = p := by rw [hhalf, one_mul]
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [polynomial, Tensor.rankOne, first, other, Fin.sum_univ_succ] <;>
      ring_nf <;> simp only [hhalf, hhalf_mul, neg_add_cancel]

theorem leading (x y z : Fin 3) : (polynomial x y z).coeff 2 = tensor x y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    (first | (simp [polynomial_apply, tensor]; all_goals first | (norm_num [polynomial_apply, tensor]; done) | rfl | decide) | (norm_num [polynomial_apply, tensor]; done) | norm_num [polynomial_apply, tensor])

theorem vanishes (x y z : Fin 3) (k : ℕ) (hk : k < 2) :
    (polynomial x y z).coeff k = 0 := by
  have hcases : k = 0 ∨ k = 1 := by omega
  rcases hcases with rfl | rfl <;>
    fin_cases x <;> fin_cases y <;> fin_cases z <;>
      (first | (simp [polynomial_apply]; all_goals first | (norm_num [polynomial_apply]; done) | rfl | decide) | (norm_num [polynomial_apply]; done) | norm_num [polynomial_apply])

theorem degree_bound (x y z : Fin 3) : (polynomial x y z).degree ≤ 6 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    (first | (simp [polynomial_apply]; all_goals first | (norm_num [polynomial_apply]; done) | rfl | decide) | (norm_num [polynomial_apply]; done) | norm_num [polynomial_apply])

def approximation : Tensor.PolynomialApproximation tensor 3 2 6 where
  polynomial := polynomial
  rank_bound := rank_bound
  vanishes := vanishes
  leading := leading
  degree_bound := degree_bound

end CoppersmithWinograd
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCWOriginalWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CWOriginalWords

open scoped BigOperators

abbrev OriginalComponent :=
  {xyz : Fin 3 × Fin 3 × Fin 3 // xyz.1.val + xyz.2.1.val + xyz.2.2.val = 2}

@[simp] theorem originalComponent_card : Fintype.card OriginalComponent = 6 := by
  decide

namespace OriginalComponent

def x (g : OriginalComponent) : Fin 3 := g.val.1
def y (g : OriginalComponent) : Fin 3 := g.val.2.1
def z (g : OriginalComponent) : Fin 3 := g.val.2.2

@[ext] theorem ext {g h : OriginalComponent}
    (hx : g.x = h.x) (hy : g.y = h.y) (hz : g.z = h.z) : g = h := by
  apply Subtype.ext
  exact Prod.ext hx (Prod.ext hy hz)

end OriginalComponent

theorem tensor_ne_zero_iff (x y z : Fin 3) :
    CoppersmithWinograd.tensor x y z ≠ 0 ↔ x.val + y.val + z.val = 2 := by
  by_cases h : x.val + y.val + z.val = 2 <;> simp [CoppersmithWinograd.tensor, h]

section Words

variable {Site : Type*}

def xWord (word : Site → OriginalComponent) : Site → Fin 3 := fun s => (word s).x
def yWord (word : Site → OriginalComponent) : Site → Fin 3 := fun s => (word s).y
def zWord (word : Site → OriginalComponent) : Site → Fin 3 := fun s => (word s).z

def originalWords (word : Site → OriginalComponent) :
    (Site → Fin 3) × (Site → Fin 3) × (Site → Fin 3) :=
  (xWord word, yWord word, zWord word)

theorem originalWords_injective : Function.Injective (originalWords (Site := Site)) := by
  intro first second he
  funext s
  apply OriginalComponent.ext
  · exact congrFun (congrArg Prod.fst he) s
  · exact congrFun (congrArg (fun words => words.2.1) he) s
  · exact congrFun (congrArg (fun words => words.2.2) he) s

end Words

end MatrixMultiplication.Foundation.CWOriginalWords

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCWBoundary
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation
namespace CWBoundary

open Polynomial

def deleted : Tensor ℂ (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => if x = 1 ∧ y = 0 ∧ z = 1 then 1 else 0

def tensor : Tensor ℂ (Fin 3) (Fin 3) (Fin 3) :=
  fun x y z => if x = 1 ∧ y = 0 ∧ z = 1 then 0
    else CoppersmithWinograd.tensor x y z

@[simp] theorem tensor_deleted : tensor 1 0 1 = 0 := by simp [tensor]

section LocalMaps

variable {K : Type*} [CommSemiring K]

def diagonalMap (w : Fin 3 → K) : Fin 3 → Fin 3 → K :=
  fun output input => if input = output then w output else 0

def outerWeight (t : K) (x : Fin 3) : K := if x = 1 then t else 1

def middleWeight (t : K) (y : Fin 3) : K := if y = 1 then 1 else t

def outerMap (t : K) : Fin 3 → Fin 3 → K := diagonalMap (outerWeight t)

def middleMap (t : K) : Fin 3 → Fin 3 → K := diagonalMap (middleWeight t)

theorem restrict_diagonal_apply (a b c : Fin 3 → K)
    (T : Tensor K (Fin 3) (Fin 3) (Fin 3)) (x y z : Fin 3) :
    Tensor.restrict (diagonalMap a) (diagonalMap b) (diagonalMap c) T x y z =
      a x * b y * c z * T x y z := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

theorem weight_on_support (t : K) (x y z : Fin 3)
    (hs : x.val + y.val + z.val = 2) :
    outerWeight t x * middleWeight t y * outerWeight t z =
      if x = 1 ∧ y = 0 ∧ z = 1 then t ^ 3 else t := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num at hs <;> norm_num [outerWeight, middleWeight]
  all_goals ring

theorem scale_lifted_tensor (f : ℂ →+* K) (t : K) :
    Tensor.restrict (outerMap t) (middleMap t) (outerMap t)
      (fun x y z => f (CoppersmithWinograd.tensor x y z)) =
      fun x y z => t * f (tensor x y z) + t ^ 3 * f (deleted x y z) := by
  funext x y z
  rw [outerMap, middleMap, restrict_diagonal_apply]
  by_cases hs : x.val + y.val + z.val = 2
  · rw [weight_on_support t x y z hs]
    by_cases hd : x = 1 ∧ y = 0 ∧ z = 1 <;>
      simp [tensor, deleted, CoppersmithWinograd.tensor, hs, hd]
  · by_cases hd : x = 1 ∧ y = 0 ∧ z = 1
    · rcases hd with ⟨rfl, rfl, rfl⟩
      norm_num at hs
    · simp [tensor, deleted, CoppersmithWinograd.tensor, hs, hd]

end LocalMaps

def scalingPolynomial : Tensor (Polynomial ℂ) (Fin 3) (Fin 3) (Fin 3) :=
  Tensor.restrict (outerMap X) (middleMap X) (outerMap X)
    (fun x y z => C (CoppersmithWinograd.tensor x y z))

theorem scalingPolynomial_apply (x y z : Fin 3) :
    scalingPolynomial x y z = X * C (tensor x y z) + X ^ 3 * C (deleted x y z) := by
  exact congrFun (congrFun (congrFun (scale_lifted_tensor C X) x) y) z

theorem scalingPolynomial_coeff (x y z : Fin 3) (k : ℕ) :
    (scalingPolynomial x y z).coeff k =
      (if k = 1 then tensor x y z else 0) +
        (if k = 3 then deleted x y z else 0) := by
  rw [scalingPolynomial_apply, Polynomial.coeff_add,
    mul_comm X (C (tensor x y z)), mul_comm (X ^ 3) (C (deleted x y z)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem scalingPolynomial_leading (x y z : Fin 3) :
    (scalingPolynomial x y z).coeff 1 = tensor x y z := by
  simp [scalingPolynomial_coeff]

end CWBoundary
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCWPrimitiveDegeneration
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation
namespace CWPrimitiveDegeneration

open Polynomial

theorem outerMap_degree (output input : Fin 3) :
    (CWBoundary.outerMap (X : Polynomial ℂ) output input).degree ≤ 1 := by
  by_cases heq : input = output
  · rw [CWBoundary.outerMap, CWBoundary.diagonalMap, ite_eq_left heq]
    by_cases hone : output = 1 <;> simp [CWBoundary.outerWeight, hone]
  · simp [CWBoundary.outerMap, CWBoundary.diagonalMap, heq]

theorem middleMap_degree (output input : Fin 3) :
    (CWBoundary.middleMap (X : Polynomial ℂ) output input).degree ≤ 1 := by
  by_cases heq : input = output
  · rw [CWBoundary.middleMap, CWBoundary.diagonalMap, ite_eq_left heq]
    by_cases hone : output = 1 <;> simp [CWBoundary.middleWeight, hone]
  · simp [CWBoundary.middleMap, CWBoundary.diagonalMap, heq]

def boundary : Tensor.PolynomialRestrictionDegeneration
    CoppersmithWinograd.tensor CWBoundary.tensor 1 1 1 1 where
  leftMap := CWBoundary.outerMap X
  middleMap := CWBoundary.middleMap X
  rightMap := CWBoundary.outerMap X
  left_degree := outerMap_degree
  middle_degree := middleMap_degree
  right_degree := outerMap_degree
  vanishes := by
    intro x y z j hj
    have hjzero : j = 0 := by omega
    subst j
    change (CWBoundary.scalingPolynomial x y z).coeff 0 = 0
    simp [CWBoundary.scalingPolynomial_coeff]
  leading := CWBoundary.scalingPolynomial_leading

@[simp] theorem boundary_basePolynomial :
    boundary.basePolynomial = CWBoundary.scalingPolynomial := rfl

def boundaryApproximation : Tensor.PolynomialApproximation CWBoundary.tensor 3 5 15 :=
  boundary.compose CoppersmithWinograd.approximation

@[simp] theorem boundaryApproximation_polynomial :
    boundaryApproximation.polynomial =
      Tensor.restrict (CWBoundary.outerMap X) (CWBoundary.middleMap X)
        (CWBoundary.outerMap X)
        (fun x y z => Polynomial.expand ℂ 2 (CoppersmithWinograd.polynomial x y z)) := rfl

theorem cw_cyclic : Tensor.cyclic CoppersmithWinograd.tensor =
    CoppersmithWinograd.tensor := by
  funext x y z
  simp [Tensor.cyclic, CoppersmithWinograd.tensor,
    Nat.add_comm, Nat.add_left_comm]

def cyclicBoundary : Tensor.PolynomialRestrictionDegeneration
    CoppersmithWinograd.tensor (Tensor.cyclic CWBoundary.tensor) 1 1 1 1 where
  leftMap := boundary.cyclic.leftMap
  middleMap := boundary.cyclic.middleMap
  rightMap := boundary.cyclic.rightMap
  left_degree := boundary.cyclic.left_degree
  middle_degree := boundary.cyclic.middle_degree
  right_degree := boundary.cyclic.right_degree
  vanishes := by
    intro x y z j hj
    simpa only [cw_cyclic] using boundary.cyclic.vanishes x y z j hj
  leading := by
    intro x y z
    simpa only [cw_cyclic] using boundary.cyclic.leading x y z

def twiceCyclicBoundary : Tensor.PolynomialRestrictionDegeneration
    CoppersmithWinograd.tensor (Tensor.cyclic (Tensor.cyclic CWBoundary.tensor))
      1 1 1 1 where
  leftMap := cyclicBoundary.cyclic.leftMap
  middleMap := cyclicBoundary.cyclic.middleMap
  rightMap := cyclicBoundary.cyclic.rightMap
  left_degree := cyclicBoundary.cyclic.left_degree
  middle_degree := cyclicBoundary.cyclic.middle_degree
  right_degree := cyclicBoundary.cyclic.right_degree
  vanishes := by
    intro x y z j hj
    simpa only [cw_cyclic] using cyclicBoundary.cyclic.vanishes x y z j hj
  leading := by
    intro x y z
    simpa only [cw_cyclic] using cyclicBoundary.cyclic.leading x y z

def cyclicBoundaryApproximation :
    Tensor.PolynomialApproximation (Tensor.cyclic CWBoundary.tensor) 3 5 15 :=
  cyclicBoundary.compose CoppersmithWinograd.approximation

def twiceCyclicBoundaryApproximation :
    Tensor.PolynomialApproximation (Tensor.cyclic (Tensor.cyclic CWBoundary.tensor))
      3 5 15 :=
  twiceCyclicBoundary.compose CoppersmithWinograd.approximation

@[simp] theorem cyclicBoundaryApproximation_polynomial :
    cyclicBoundaryApproximation.polynomial =
      Tensor.restrict (CWBoundary.middleMap X) (CWBoundary.outerMap X)
        (CWBoundary.outerMap X)
        (fun x y z => Polynomial.expand ℂ 2 (CoppersmithWinograd.polynomial x y z)) := rfl

@[simp] theorem twiceCyclicBoundaryApproximation_polynomial :
    twiceCyclicBoundaryApproximation.polynomial =
      Tensor.restrict (CWBoundary.outerMap X) (CWBoundary.outerMap X)
        (CWBoundary.middleMap X)
        (fun x y z => Polynomial.expand ℂ 2 (CoppersmithWinograd.polynomial x y z)) := rfl

end CWPrimitiveDegeneration
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexElementary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

namespace MatrixMultiplication.Foundation.Elementary

inductive BoundaryTerm where
  | a0 | a1 | b0 | b1 | c
  deriving DecidableEq, BEq, Repr

namespace BoundaryTerm

def x : BoundaryTerm → Nat
  | .a0 | .a1 | .c => 0
  | .b0 => 2
  | .b1 => 1

def y : BoundaryTerm → Nat
  | .a0 | .b0 => 0
  | .a1 | .b1 => 1
  | .c => 2

def z : BoundaryTerm → Nat
  | .a0 => 2
  | .a1 => 1
  | .b0 | .b1 | .c => 0

def all : List BoundaryTerm := [.a0, .a1, .b0, .b1, .c]

end BoundaryTerm

def testA (w : List BoundaryTerm) : Bool := w.all (fun s => s.z != 0)
def testB (w : List BoundaryTerm) : Bool := w.any (fun s => s.x != 0)
def testC (w : List BoundaryTerm) : Bool := w.any (fun s => s.y == 2)

def retained (w : List BoundaryTerm) : Bool :=
  !(testB w && testC w) && !testA w

def triples : List (List BoundaryTerm) :=
  BoundaryTerm.all.flatMap fun a =>
    BoundaryTerm.all.flatMap fun b =>
      BoundaryTerm.all.map fun third => [a, b, third]

end MatrixMultiplication.Foundation.Elementary

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCW75Primitive
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff _root_.OAI.MatrixMultiplication.RecursiveCompletion.complete_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CW75Primitive

open Polynomial
open scoped BigOperators Classical

abbrev Word := Fin 3 → Fin 3

def source : Tensor ℂ Word Word Word := Tensor.power CWBoundary.tensor 3

def hasB (x : Word) : Prop := ∃ i, x i ≠ 0

def hasC (y : Word) : Prop := ∃ i, y i = 2

def allA (z : Word) : Prop := ∀ i, z i ≠ 0

def retained (x y z : Word) : Prop := ¬ (hasB x ∧ hasC y) ∧ ¬ allA z

def tensor : Tensor ℂ Word Word Word :=
  fun x y z => if retained x y z then source x y z else 0

def mixed : Tensor ℂ Word Word Word :=
  fun x y z => if hasB x ∧ hasC y ∧ ¬ allA z then source x y z else 0

theorem boundary_active (x y z : Fin 3) (h : CWBoundary.tensor x y z ≠ 0) :
    z ≠ 0 ↔ x = 0 ∧ y ≠ 2 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [← Fin.val_eq_val, CWBoundary.tensor, CoppersmithWinograd.tensor] at h <;>
      (first | (simp [← Fin.val_eq_val]; all_goals first | (norm_num [← Fin.val_eq_val]; done) | rfl | decide) | (norm_num [← Fin.val_eq_val]; done) | norm_num [← Fin.val_eq_val])

theorem source_factors (x y z : Word) (h : source x y z ≠ 0) (i : Fin 3) :
    CWBoundary.tensor (x i) (y i) (z i) ≠ 0 := by
  unfold source Tensor.power at h
  exact (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)

theorem allA_iff (x y z : Word) (h : source x y z ≠ 0) :
    allA z ↔ ¬ hasB x ∧ ¬ hasC y := by
  have hpoint (i : Fin 3) : z i ≠ 0 ↔ x i = 0 ∧ y i ≠ 2 :=
    boundary_active _ _ _ (source_factors x y z h i)
  simp only [allA, hasB, hasC, not_exists, not_not, hpoint, forall_and]

def leftMap (output input : Word) : Polynomial ℂ :=
  if input = output then (if hasB output then X else 1) else 0

def middleMap (output input : Word) : Polynomial ℂ :=
  if input = output then (if hasC output then X else 1) else 0

def rightMap (output input : Word) : Polynomial ℂ :=
  if input = output ∧ ¬ allA output then 1 else 0

def polynomial : Tensor (Polynomial ℂ) Word Word Word :=
  Tensor.restrict leftMap middleMap rightMap (fun x y z => C (source x y z))

theorem polynomial_apply (x y z : Word) :
    polynomial x y z = if allA z then 0 else
      (if hasB x then X else 1) * (if hasC y then X else 1) * C (source x y z) := by
  by_cases hz : allA z <;>
    simp [polynomial, Tensor.restrict, leftMap, middleMap, rightMap,
      ite_mul, mul_ite, hz]

theorem polynomial_identity (x y z : Word) :
    polynomial x y z = X * C (tensor x y z) + X ^ 2 * C (mixed x y z) := by
  by_cases hs : source x y z = 0
  · simp [polynomial_apply, tensor, mixed, hs]
  · have hA := allA_iff x y z hs
    by_cases hz : allA z <;> by_cases hx : hasB x <;> by_cases hy : hasC y
    all_goals simp_all [polynomial_apply, tensor, mixed, retained, pow_two]

theorem polynomial_coeff (x y z : Word) (j : ℕ) :
    (polynomial x y z).coeff j =
      (if j = 1 then tensor x y z else 0) + (if j = 2 then mixed x y z else 0) := by
  rw [polynomial_identity, Polynomial.coeff_add,
    mul_comm X (C (tensor x y z)), mul_comm (X ^ 2) (C (mixed x y z)),
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]

theorem leftMap_degree (output input : Word) : (leftMap output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hx : hasB output <;>
    simp [leftMap, heq, hx]

theorem middleMap_degree (output input : Word) : (middleMap output input).degree ≤ 1 := by
  by_cases heq : input = output <;> by_cases hy : hasC output <;>
    simp [middleMap, heq, hy]

theorem rightMap_degree (output input : Word) : (rightMap output input).degree ≤ 0 := by
  by_cases h : input = output ∧ ¬ allA output <;> simp [rightMap, h]

def restriction : Tensor.PolynomialRestrictionDegeneration source tensor 1 1 1 0 where
  leftMap := leftMap
  middleMap := middleMap
  rightMap := rightMap
  left_degree := leftMap_degree
  middle_degree := middleMap_degree
  right_degree := rightMap_degree
  vanishes := by
    intro x y z j hj
    have hcoeff := polynomial_coeff x y z j
    unfold polynomial at hcoeff
    rw [hcoeff]
    have hjzero : j = 0 := by omega
    simp [hjzero]
  leading := by
    intro x y z
    have hcoeff := polynomial_coeff x y z 1
    unfold polynomial at hcoeff
    rw [hcoeff]
    simp

@[simp] theorem restriction_basePolynomial : restriction.basePolynomial = polynomial := rfl

open Elementary

def component : BoundaryTerm → CWOriginalWords.OriginalComponent
  | .a0 => ⟨(0, 0, 2), by decide⟩
  | .a1 => ⟨(0, 1, 1), by decide⟩
  | .b0 => ⟨(2, 0, 0), by decide⟩
  | .b1 => ⟨(1, 1, 0), by decide⟩
  | .c => ⟨(0, 2, 0), by decide⟩

theorem component_injective : Function.Injective component := by
  intro a b h
  have hx := congrArg (fun g => (CWOriginalWords.OriginalComponent.x g).val) h
  have hy := congrArg (fun g => (CWOriginalWords.OriginalComponent.y g).val) h
  have hz := congrArg (fun g => (CWOriginalWords.OriginalComponent.z g).val) h
  cases a <;> cases b <;>
    simp_all [component, CWOriginalWords.OriginalComponent.x,
      CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z]

def listedWord (w : List BoundaryTerm) : Fin 3 → CWOriginalWords.OriginalComponent :=
  fun i => component (w.getD i.val .a0)

def listedX (w : List BoundaryTerm) : Word := CWOriginalWords.xWord (listedWord w)
def listedY (w : List BoundaryTerm) : Word := CWOriginalWords.yWord (listedWord w)
def listedZ (w : List BoundaryTerm) : Word := CWOriginalWords.zWord (listedWord w)

theorem tensor_on_triple (a b third : BoundaryTerm) :
    tensor (listedX [a, b, third]) (listedY [a, b, third]) (listedZ [a, b, third]) =
      if Elementary.retained [a, b, third] then 1 else 0 := by
  have hboundary (s : BoundaryTerm) :
      CWBoundary.tensor (component s).x (component s).y (component s).z = 1 := by
    cases s <;>
      (first | (simp [component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z, CWBoundary.tensor, CoppersmithWinograd.tensor, ← Fin.val_eq_val]; all_goals first | (norm_num [component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z, CWBoundary.tensor, CoppersmithWinograd.tensor, ← Fin.val_eq_val]; done) | rfl | decide) | (norm_num [component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z, CWBoundary.tensor, CoppersmithWinograd.tensor, ← Fin.val_eq_val]; done) | norm_num [component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z, CWBoundary.tensor, CoppersmithWinograd.tensor, ← Fin.val_eq_val])
  have hx (s : BoundaryTerm) : (component s).x.val = s.x := by cases s <;> rfl
  have hy (s : BoundaryTerm) : (component s).y.val = s.y := by cases s <;> rfl
  have hz (s : BoundaryTerm) : (component s).z.val = s.z := by cases s <;> rfl
  simp [tensor, retained, source, Tensor.power,
      hasB, hasC, allA, Fin.exists_fin_succ, Fin.forall_fin_succ,
      listedX, listedY, listedZ, listedWord,
      CWOriginalWords.xWord, CWOriginalWords.yWord, CWOriginalWords.zWord,
      ← Fin.val_eq_val, hboundary, hx, hy, hz,
      Elementary.retained, Elementary.testA, Elementary.testB, Elementary.testC]
  cases a <;> cases b <;> cases third <;>
    norm_num [BoundaryTerm.x, BoundaryTerm.y, BoundaryTerm.z]

theorem mem_triples_shape (w : List BoundaryTerm) (hw : w ∈ Elementary.triples) :
    ∃ a b third, w = [a, b, third] := by
  simp only [Elementary.triples, List.mem_flatMap, List.mem_map] at hw
  rcases hw with ⟨a, _, b, _, third, _, rfl⟩
  exact ⟨a, b, third, rfl⟩

theorem tensor_on_enumeration (w : List BoundaryTerm) (hw : w ∈ Elementary.triples) :
    tensor (listedX w) (listedY w) (listedZ w) =
      if Elementary.retained w then 1 else 0 := by
  rcases mem_triples_shape w hw with ⟨a, b, third, rfl⟩
  exact tensor_on_triple a b third

theorem retained_coefficient_one (w : List BoundaryTerm)
    (hw : w ∈ Elementary.triples.filter Elementary.retained) :
    tensor (listedX w) (listedY w) (listedZ w) = 1 := by
  rw [tensor_on_enumeration w (List.mem_filter.mp hw).1]
  simp [(List.mem_filter.mp hw).2]

theorem listedWords_injective (w v : List BoundaryTerm)
    (hw : w ∈ Elementary.triples) (hv : v ∈ Elementary.triples)
    (he : CWOriginalWords.originalWords (listedWord w) =
      CWOriginalWords.originalWords (listedWord v)) : w = v := by
  rcases mem_triples_shape w hw with ⟨a, b, third, rfl⟩
  rcases mem_triples_shape v hv with ⟨a', b', c', rfl⟩
  have hword := CWOriginalWords.originalWords_injective he
  have ha := component_injective (by simpa [listedWord] using congrFun hword 0)
  have hb := component_injective (by simpa [listedWord] using congrFun hword 1)
  have hc := component_injective (by simpa [listedWord] using congrFun hword 2)
  simp [ha, hb, hc]

theorem boundary_component_complete (x y z : Fin 3)
    (h : CWBoundary.tensor x y z ≠ 0) :
    ∃ a : BoundaryTerm, (component a).x = x ∧ (component a).y = y ∧
      (component a).z = z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [CWBoundary.tensor, CoppersmithWinograd.tensor] at h
  all_goals first
    | exact ⟨.a0, rfl, rfl, rfl⟩
    | exact ⟨.a1, rfl, rfl, rfl⟩
    | exact ⟨.b0, rfl, rfl, rfl⟩
    | exact ⟨.b1, rfl, rfl, rfl⟩
    | exact ⟨.c, rfl, rfl, rfl⟩

theorem term_mem_all (a : BoundaryTerm) : a ∈ BoundaryTerm.all := by
  cases a <;> simp [BoundaryTerm.all]

theorem triple_mem (a b third : BoundaryTerm) : [a, b, third] ∈ Elementary.triples := by
  simp only [Elementary.triples, List.mem_flatMap, List.mem_map]
  exact ⟨a, term_mem_all a, b, term_mem_all b, third, term_mem_all third, rfl⟩

end MatrixMultiplication.Foundation.CW75Primitive

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCW75LabelHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CW75LabelHierarchy

open Elementary
open scoped Classical

abbrev Word := CW75Primitive.Word
abbrev BitWord := Fin 3 → Bool

def retainedWords : Finset (List BoundaryTerm) :=
  (Elementary.triples.filter Elementary.retained).toFinset

abbrev Scalar := ↥retainedWords

theorem scalar_mem (a : Scalar) :
    a.val ∈ Elementary.triples.filter Elementary.retained := by
  exact List.mem_toFinset.mp a.property

def letter (a : Scalar) (i : Fin 3) : BoundaryTerm := a.val.getD i.val .a0

def grade (a : Scalar) : Fin 3 → CWOriginalWords.OriginalComponent :=
  fun i => CW75Primitive.component (letter a i)

def x (a : Scalar) : Word := CWOriginalWords.xWord (grade a)
def y (a : Scalar) : Word := CWOriginalWords.yWord (grade a)
def z (a : Scalar) : Word := CWOriginalWords.zWord (grade a)

theorem coefficient_one (a : Scalar) : CW75Primitive.tensor (x a) (y a) (z a) = 1 :=
  CW75Primitive.retained_coefficient_one a.val (scalar_mem a)

theorem grade_injective : Function.Injective grade := by
  intro a b h
  apply Subtype.ext
  exact CW75Primitive.listedWords_injective a.val b.val
    (List.mem_filter.mp (scalar_mem a)).1 (List.mem_filter.mp (scalar_mem b)).1
    (congrArg CWOriginalWords.originalWords h)

theorem coordinates_injective : Function.Injective (fun a : Scalar => (x a, y a, z a)) := by
  intro a b h
  apply grade_injective
  exact CWOriginalWords.originalWords_injective h

theorem retained_actual (a : Scalar) :
    CW75Primitive.retained (x a) (y a) (z a) := by
  by_contra h
  have hc := coefficient_one a
  simp [CW75Primitive.tensor, h] at hc

theorem source_ne_zero (a : Scalar) :
    CW75Primitive.source (x a) (y a) (z a) ≠ 0 := by
  intro h
  have hc := coefficient_one a
  simp [CW75Primitive.tensor, h] at hc

theorem hasB_iff_not_hasC (a : Scalar) :
    CW75Primitive.hasB (x a) ↔ ¬ CW75Primitive.hasC (y a) := by
  have hr := retained_actual a
  have ha := CW75Primitive.allA_iff (x a) (y a) (z a) (source_ne_zero a)
  constructor
  · intro hb hc
    exact hr.1 ⟨hb, hc⟩
  · intro hc
    by_contra hb
    exact hr.2 (ha.mpr ⟨hb, hc⟩)

def outer (a : Scalar) : Bool := decide (CW75Primitive.hasB (x a))

def bPositions (a : Scalar) : BitWord := fun i => decide (x a i ≠ 0)
def cPositions (a : Scalar) : BitWord := fun i => decide (y a i = 2)
def aChoices (a : Scalar) : BitWord := fun i => decide (z a i = 1)
def bChoices (a : Scalar) : BitWord := fun i => decide (x a i = 1)

def outerX (u : Word) : Bool := decide (CW75Primitive.hasB u)
def outerY (v : Word) : Bool := !decide (CW75Primitive.hasC v)

def bPositionsX (u : Word) : BitWord := fun i => decide (u i ≠ 0)
def bPositionsZ (pb : Bool) (w : Word) : BitWord :=
  fun i => if pb then decide (w i = 0) else false

def cPositionsY (v : Word) : BitWord := fun i => decide (v i = 2)
def cPositionsZ (pb : Bool) (w : Word) : BitWord :=
  fun i => if pb then false else decide (w i = 0)

def aChoicesY (bs cs : BitWord) (v : Word) : BitWord :=
  fun i => !bs i && !cs i && decide (v i = 1)
def aChoicesZ (w : Word) : BitWord := fun i => decide (w i = 1)

def bChoicesX (u : Word) : BitWord := fun i => decide (u i = 1)
def bChoicesY (bs : BitWord) (v : Word) : BitWord :=
  fun i => bs i && decide (v i = 1)

theorem outerX_read (a : Scalar) : outerX (x a) = outer a := rfl

theorem outerY_read (a : Scalar) : outerY (y a) = outer a := by
  simp only [outerY, outer, hasB_iff_not_hasC, decide_not]

theorem bPositionsX_read (a : Scalar) : bPositionsX (x a) = bPositions a := rfl

theorem bPositionsZ_read (a : Scalar) : bPositionsZ (outer a) (z a) = bPositions a := by
  funext i
  have hactive := CW75Primitive.boundary_active (x a i) (y a i) (z a i)
    (CW75Primitive.source_factors (x a) (y a) (z a) (source_ne_zero a) i)
  by_cases hb : CW75Primitive.hasB (x a)
  · have hy : y a i ≠ 2 := fun h => (hasB_iff_not_hasC a).mp hb ⟨i, h⟩
    have he : z a i = 0 ↔ x a i ≠ 0 := by tauto
    simp [bPositionsZ, outer, bPositions, hb, he]
  · have hx : x a i = 0 := by
      by_contra h
      exact hb ⟨i, h⟩
    simp [bPositionsZ, outer, bPositions, hb, hx]

theorem cPositionsY_read (a : Scalar) : cPositionsY (y a) = cPositions a := rfl

theorem cPositionsZ_read (a : Scalar) : cPositionsZ (outer a) (z a) = cPositions a := by
  funext i
  have hactive := CW75Primitive.boundary_active (x a i) (y a i) (z a i)
    (CW75Primitive.source_factors (x a) (y a) (z a) (source_ne_zero a) i)
  by_cases hb : CW75Primitive.hasB (x a)
  · have hy : y a i ≠ 2 := fun h => (hasB_iff_not_hasC a).mp hb ⟨i, h⟩
    simp [cPositionsZ, outer, cPositions, hb, hy]
  · have hx : x a i = 0 := by
      by_contra h
      exact hb ⟨i, h⟩
    have he : z a i = 0 ↔ y a i = 2 := by tauto
    simp [cPositionsZ, outer, cPositions, hb, he]

theorem aChoicesY_read (a : Scalar) :
    aChoicesY (bPositions a) (cPositions a) (y a) = aChoices a := by
  funext i
  change (!decide ((CW75Primitive.component (letter a i)).x ≠ 0) &&
    !decide ((CW75Primitive.component (letter a i)).y = 2) &&
    decide ((CW75Primitive.component (letter a i)).y = 1)) =
    decide ((CW75Primitive.component (letter a i)).z = 1)
  cases letter a i <;>
    (first | (simp [CW75Primitive.component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z, ← Fin.val_eq_val]; all_goals first | (norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z, ← Fin.val_eq_val]; done) | rfl | decide) | (norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z, ← Fin.val_eq_val]; done) | norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z, ← Fin.val_eq_val])

theorem aChoicesZ_read (a : Scalar) : aChoicesZ (z a) = aChoices a := rfl

theorem bChoicesX_read (a : Scalar) : bChoicesX (x a) = bChoices a := rfl

theorem bChoicesY_read (a : Scalar) :
    bChoicesY (bPositions a) (y a) = bChoices a := by
  funext i
  change (decide ((CW75Primitive.component (letter a i)).x ≠ 0) &&
    decide ((CW75Primitive.component (letter a i)).y = 1)) =
    decide ((CW75Primitive.component (letter a i)).x = 1)
  cases letter a i <;>
    (first | (simp [CW75Primitive.component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, ← Fin.val_eq_val]; all_goals first | (norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, ← Fin.val_eq_val]; done) | rfl | decide) | (norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, ← Fin.val_eq_val]; done) | norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x, CWOriginalWords.OriginalComponent.y, ← Fin.val_eq_val])

def Label : ℕ → Type
  | 0 => Bool
  | _ + 1 => BitWord

instance labelFintype (n : ℕ) : Fintype (Label n) := by
  cases n <;> simp only [Label] <;> infer_instance

inductive Side where
  | x | y | z
  deriving DecidableEq

def originalCoordinate : Side → Scalar → Word
  | .x => x
  | .y => y
  | .z => z

end MatrixMultiplication.Foundation.CW75LabelHierarchy

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexWitness
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

open scoped BigOperators
open Filter

namespace MatrixMultiplication.ComplexWitness

open MatrixMultiplication.Foundation

abbrev CurveCoordinate := CW75Primitive.Word
abbrev CurveLeaf := CW75LabelHierarchy.Scalar

abbrev CurveLabel := CW75LabelHierarchy.Label

def curveLabels : (n : ℕ) → CurveLeaf → CurveLabel n
  | 0 => CW75LabelHierarchy.outer
  | 1 => CW75LabelHierarchy.bPositions
  | 2 => CW75LabelHierarchy.bChoices
  | 3 => CW75LabelHierarchy.cPositions
  | 4 => CW75LabelHierarchy.aChoices
  | _ + 5 => fun _ _ => false

def curveFirstSide : ℕ → CW75LabelHierarchy.Side
  | 3 | 4 => .y
  | _ => .x

def curveSecondSide : ℕ → CW75LabelHierarchy.Side
  | 1 | 3 | 4 => .z
  | _ => .y

def curveFirstReader : (n : ℕ) → LabelRecord CurveLabel n → CurveCoordinate → CurveLabel n
  | 0, _ => CW75LabelHierarchy.outerX
  | 1, _ => CW75LabelHierarchy.bPositionsX
  | 2, _ => CW75LabelHierarchy.bChoicesX
  | 3, _ => CW75LabelHierarchy.cPositionsY
  | 4, prior => CW75LabelHierarchy.aChoicesY prior.1.1.2 prior.2
  | _ + 5, _ => fun _ _ => false

def curveSecondReader : (n : ℕ) → LabelRecord CurveLabel n → CurveCoordinate → CurveLabel n
  | 0, _ => CW75LabelHierarchy.outerY
  | 1, prior => CW75LabelHierarchy.bPositionsZ prior.2
  | 2, prior => CW75LabelHierarchy.bChoicesY prior.2
  | 3, prior => CW75LabelHierarchy.cPositionsZ prior.1.1.2
  | 4, _ => CW75LabelHierarchy.aChoicesZ
  | _ + 5, _ => fun _ _ => false

theorem curveFirstReader_readable (n : ℕ) (hn : n < 5) (s : CurveLeaf) :
    curveFirstReader n (labelRecordOf curveLabels n s)
        (CW75LabelHierarchy.originalCoordinate (curveFirstSide n) s) =
      curveLabels n s := by
  interval_cases n
  · exact CW75LabelHierarchy.outerX_read s
  · exact CW75LabelHierarchy.bPositionsX_read s
  · exact CW75LabelHierarchy.bChoicesX_read s
  · exact CW75LabelHierarchy.cPositionsY_read s
  · exact CW75LabelHierarchy.aChoicesY_read s

theorem curveSecondReader_readable (n : ℕ) (hn : n < 5) (s : CurveLeaf) :
    curveSecondReader n (labelRecordOf curveLabels n s)
        (CW75LabelHierarchy.originalCoordinate (curveSecondSide n) s) =
      curveLabels n s := by
  interval_cases n
  · exact CW75LabelHierarchy.outerY_read s
  · exact CW75LabelHierarchy.bPositionsZ_read s
  · exact CW75LabelHierarchy.bChoicesY_read s
  · exact CW75LabelHierarchy.cPositionsZ_read s
  · exact CW75LabelHierarchy.aChoicesZ_read s

end MatrixMultiplication.ComplexWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedWords

open MatrixMultiplication.Foundation
open CW75LabelHierarchy ConditionalPrefixWords ComplexWitness
open scoped BigOperators Classical

universe u v

abbrev BlockPosition (counts : Scalar → ℕ) (t : ℕ) := Fin (t * ∑ a, counts a)

variable {Position : Type u} [Fintype Position]

abbrev LongWord (Position : Type u) := Position → Word

def longX (word : Position → Scalar) : LongWord Position := fun i => x (word i)
def longY (word : Position → Scalar) : LongWord Position := fun i => y (word i)
def longZ (word : Position → Scalar) : LongWord Position := fun i => z (word i)

def longCoordinate (side : Side) (word : Position → Scalar) : LongWord Position :=
  fun i => originalCoordinate side (word i)

def coordinateOf : Side → LongWord Position → LongWord Position → LongWord Position →
    LongWord Position
  | .x, u, _, _ => u
  | .y, _, v, _ => v
  | .z, _, _, w => w

omit [Fintype Position] in
theorem coordinateOf_original (side : Side) (word : Position → Scalar) :
    coordinateOf side (longX word) (longY word) (longZ word) =
      longCoordinate side word := by
  cases side <;> rfl

omit [Fintype Position] in
theorem longCoordinates_injective : Function.Injective
    (fun word : Position → Scalar => (longX word, longY word, longZ word)) := by
  intro word other h
  funext i
  apply coordinates_injective
  exact Prod.ext (congrFun (congrArg Prod.fst h) i)
    (Prod.ext (congrFun (congrArg (fun q => q.2.1) h) i)
      (congrFun (congrArg (fun q => q.2.2) h) i))

variable {Prefix : Type v} {counts : Scalar → ℕ} {n t : ℕ}

def Represents (priorWord : Prefix → ExactPrefix counts curveLabels n t Position)
    (prior : Prefix) (u v w : LongWord Position) (word : Position → Scalar) : Prop :=
  u = longX word ∧ v = longY word ∧ w = longZ word ∧
    ∀ i, (priorWord prior).val i = labelRecordOf curveLabels n (word i)

def eligible (priorWord : Prefix → ExactPrefix counts curveLabels n t Position)
    (prior : Prefix) (u v w : LongWord Position) : Prop :=
  ∃ word : Position → Scalar, Represents priorWord prior u v w word

def firstRead (priorWord : Prefix → ExactPrefix counts curveLabels n t Position)
    (prior : Prefix) (own : LongWord Position) : Position → Label n :=
  fun i => curveFirstReader n ((priorWord prior).val i) (own i)

def secondRead (priorWord : Prefix → ExactPrefix counts curveLabels n t Position)
    (prior : Prefix) (own : LongWord Position) : Position → Label n :=
  fun i => curveSecondReader n ((priorWord prior).val i) (own i)

theorem firstRead_on_original_word
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (word : Position → Scalar) (hn : n < 5)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf curveLabels n (word i)) :
    firstRead priorWord prior (longCoordinate (curveFirstSide n) word) =
      fun i => curveLabels n (word i) := by
  funext i
  change curveFirstReader n ((priorWord prior).val i)
    (originalCoordinate (curveFirstSide n) (word i)) = curveLabels n (word i)
  rw [hprior i]
  exact curveFirstReader_readable n hn (word i)

theorem secondRead_on_original_word
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (word : Position → Scalar) (hn : n < 5)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf curveLabels n (word i)) :
    secondRead priorWord prior (longCoordinate (curveSecondSide n) word) =
      fun i => curveLabels n (word i) := by
  funext i
  change curveSecondReader n ((priorWord prior).val i)
    (originalCoordinate (curveSecondSide n) (word i)) = curveLabels n (word i)
  rw [hprior i]
  exact curveSecondReader_readable n hn (word i)

theorem readers_recover_original_fine
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) (hn : n < 5) (h : eligible priorWord prior u v w) :
    ∃ word : Position → Scalar, Represents priorWord prior u v w word ∧
      firstRead priorWord prior (coordinateOf (curveFirstSide n) u v w) =
        (fun i => curveLabels n (word i)) ∧
      secondRead priorWord prior (coordinateOf (curveSecondSide n) u v w) =
        (fun i => curveLabels n (word i)) := by
  obtain ⟨word, hw⟩ := h
  refine ⟨word, hw, ?_, ?_⟩
  · rw [hw.1, hw.2.1, hw.2.2.1, coordinateOf_original]
    exact firstRead_on_original_word priorWord prior word hn hw.2.2.2
  · rw [hw.1, hw.2.1, hw.2.2.1, coordinateOf_original]
    exact secondRead_on_original_word priorWord prior word hn hw.2.2.2

theorem readable_of_eligible
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) (hn : n < 5) (h : eligible priorWord prior u v w) :
    firstRead priorWord prior (coordinateOf (curveFirstSide n) u v w) =
      secondRead priorWord prior (coordinateOf (curveSecondSide n) u v w) := by
  obtain ⟨word, _, hfirst, hsecond⟩ :=
    readers_recover_original_fine priorWord prior u v w hn h
  exact hfirst.trans hsecond.symm

theorem represented_word_unique
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) {word other : Position → Scalar}
    (hword : Represents priorWord prior u v w word)
    (hother : Represents priorWord prior u v w other) : word = other := by
  apply longCoordinates_injective
  exact Prod.ext (hword.1.symm.trans hother.1)
    (Prod.ext (hword.2.1.symm.trans hother.2.1)
      (hword.2.2.1.symm.trans hother.2.2.1))

theorem eligible_coefficient_one
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) (h : eligible priorWord prior u v w) (i : Position) :
    CW75Primitive.tensor (u i) (v i) (w i) = 1 := by
  obtain ⟨word, hw⟩ := h
  rw [hw.1, hw.2.1, hw.2.2.1]
  exact coefficient_one (word i)

theorem eligible_appendCode_iff
    (old : ExactPrefix counts curveLabels n t Position)
    (code : Fin (StageHierarchyResources.stageRefinementCount counts curveLabels n t))
    (u v w : LongWord Position) :
    eligible id (appendCode old code) u v w ↔
      ∃ word : Position → Scalar, Represents id old u v w word ∧
        ((conditionalPoolEquivFin old).symm code).val =
          (fun i => curveLabels n (word i)) := by
  constructor
  · rintro ⟨word, hu, hv, hw, hprior⟩
    refine ⟨word, ⟨hu, hv, hw, ?_⟩, ?_⟩
    · intro i
      have hi := hprior i
      change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
        (labelRecordOf curveLabels n (word i), curveLabels n (word i)) at hi
      exact congrArg Prod.fst hi
    · funext i
      have hi := hprior i
      change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
        (labelRecordOf curveLabels n (word i), curveLabels n (word i)) at hi
      exact congrArg Prod.snd hi
  · rintro ⟨word, ⟨hu, hv, hw, hprior⟩, hfine⟩
    refine ⟨word, hu, hv, hw, ?_⟩
    intro i
    change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
      (labelRecordOf curveLabels n (word i), curveLabels n (word i))
    exact Prod.ext (hprior i) (congrFun hfine i)

theorem represented_fine_eq
    (priorWord : Prefix → ExactPrefix counts curveLabels n t Position) (prior : Prefix)
    (u v w : LongWord Position) {word other : Position → Scalar}
    (hword : Represents priorWord prior u v w word)
    (hother : Represents priorWord prior u v w other) :
    (fun i => curveLabels n (word i)) = (fun i => curveLabels n (other i)) := by
  rw [represented_word_unique priorWord prior u v w hword hother]

theorem eligible_appendCode_iff_of_represents
    (old : ExactPrefix counts curveLabels n t Position)
    (code : Fin (StageHierarchyResources.stageRefinementCount counts curveLabels n t))
    (u v w : LongWord Position) (word : Position → Scalar)
    (hword : Represents id old u v w word) :
    eligible id (appendCode old code) u v w ↔
      ((conditionalPoolEquivFin old).symm code).val = (fun i => curveLabels n (word i)) := by
  rw [eligible_appendCode_iff]
  constructor
  · rintro ⟨other, hother, hfine⟩
    exact hfine.trans (represented_fine_eq id old u v w hother hword)
  · intro hfine
    exact ⟨word, hword, hfine⟩

end MatrixMultiplication.CW75ReorderedWords

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialLocalConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialLocalConstruction

open scoped BigOperators
open _root_.OAI.MatrixMultiplication.Foundation.Tensor LocalMaps

variable {X Y Z AX AY AZ Label Grade : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]

def kernel {OX OY OZ : Type*}
    (auxiliary : Tensor ℂ AX AY AZ)
    (leftMap : X → OX → AX → Polynomial ℂ)
    (middleMap : Y → OY → AY → Polynomial ℂ)
    (rightMap : Z → OZ → AZ → Polynomial ℂ) :
    Tensor (Polynomial ℂ) (X × OX) (Y × OY) (Z × OZ) :=
  fiberTransform leftMap middleMap rightMap
    (fun x y z => Polynomial.C (auxiliary x.2 y.2 z.2))

end MatrixMultiplication.Foundation.PolynomialLocalConstruction

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexTensorRestrictionComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [CommSemiring K]

theorem sum_interleaved_triples {U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (f : X → Y → Z → U → V → W → K) :
    (∑ x, ∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
      ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w, f x y z u v w := by
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ u, ∑ y, ∑ v, ∑ z, ∑ w, f x y z u v w) =
        ∑ y, ∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      calc
        (∑ u, ∑ v, ∑ z, ∑ w, f x y z u v w) =
            ∑ u, ∑ z, ∑ v, ∑ w, f x y z u v w := by
          apply Finset.sum_congr rfl
          intro u hu
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem restrict_product {U V W U' V' W' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (D : U' → U → K) (E : V' → V → K) (F : W' → W → K)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    restrict (fun (x : X' × U') (u : X × U) => A x.1 u.1 * D x.2 u.2)
      (fun (y : Y' × V') (v : Y × V) => B y.1 v.1 * E y.2 v.2)
      (fun (z : Z' × W') (w : Z × W) => C z.1 w.1 * F z.2 w.2) (product T S) =
      product (restrict A B C T) (restrict D E F S) := by
  funext x' y' z'
  simp only [restrict, product, Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * D x'.2 u) * (B y'.1 y * E y'.2 v) *
          (C z'.1 z * F z'.2 w) * (T x y z * S u v w) :=
      sum_interleaved_triples _
    _ = ∑ x, ∑ y, ∑ z, ∑ u, ∑ v, ∑ w,
        (A x'.1 x * B y'.1 y * C z'.1 z * T x y z) *
          (D x'.2 u * E y'.2 v * F z'.2 w * S u v w) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = _ := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

end Algebra

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialControlledKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation
namespace PolynomialControlledKernel

open _root_.OAI.MatrixMultiplication.Foundation.Tensor LocalMaps PolynomialLocalConstruction
open scoped BigOperators

section ScalarCoefficients

variable {F : Type*} [Field F]

theorem expanded_mul_coeff_window (P Q : Polynomial F) (d k : ℕ) (a : F)
    (hP : ∀ j, j < d → P.coeff j = 0) (hPa : P.coeff d = a)
    (j : ℕ) (hj : j ≤ d * (k + 1) + k) :
    (Polynomial.expand F (k + 1) P * Q).coeff j =
      if d * (k + 1) ≤ j then a * Q.coeff (j - d * (k + 1)) else 0 := by
  obtain ⟨P₀, hP₀⟩ := Polynomial.X_pow_dvd_iff.mpr hP
  have hconstant : P₀.coeff 0 = a := by
    rw [hP₀] at hPa
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self] using hPa
  have hfactor : Polynomial.expand F (k + 1) P * Q =
      Polynomial.X ^ (d * (k + 1)) *
        (Q * Polynomial.expand F (k + 1) P₀) := by
    rw [hP₀, map_mul, map_pow, Polynomial.expand_X]
    simp only [← pow_mul]
    rw [Nat.mul_comm (k + 1) d]
    ring
  rw [hfactor, Polynomial.coeff_X_pow_mul']
  split_ifs with hdj
  · have hsmall : j - d * (k + 1) ≤ k := by omega
    rw [Tensor.coeff_mul_expand_eq_constant Q P₀ a hconstant k _ hsmall,
      Polynomial.coeff_mul_C, mul_comm]
  · rfl

theorem expanded_mul_vanishes_of_leading_support (P Q : Polynomial F)
    (d k : ℕ) (a : F)
    (hP : ∀ j, j < d → P.coeff j = 0) (hPa : P.coeff d = a)
    (hQ : a ≠ 0 → ∀ j, j < k → Q.coeff j = 0)
    (j : ℕ) (hj : j < d * (k + 1) + k) :
    (Polynomial.expand F (k + 1) P * Q).coeff j = 0 := by
  rw [expanded_mul_coeff_window P Q d k a hP hPa j (Nat.le_of_lt hj)]
  split_ifs with hdj
  · by_cases ha : a = 0
    · simp [ha]
    · rw [hQ ha _ (by omega), mul_zero]
  · rfl

theorem expanded_mul_leading_of_leading_support (P Q : Polynomial F)
    (d k : ℕ) (a b : F)
    (hP : ∀ j, j < d → P.coeff j = 0) (hPa : P.coeff d = a)
    (hQb : a ≠ 0 → Q.coeff k = b) :
    (Polynomial.expand F (k + 1) P * Q).coeff (d * (k + 1) + k) = a * b := by
  rw [expanded_mul_coeff_window P Q d k a hP hPa _ le_rfl]
  simp only [Nat.le_add_right, ite_true, if_true, Nat.add_sub_cancel_left]
  by_cases ha : a = 0
  · simp [ha]
  · rw [hQb ha]

end ScalarCoefficients

abbrev Output (Prefix New OldCoord NewCoord : Type*) :=
  (Prefix × OldCoord) × (New × NewCoord)

section ActualMatrices

variable {X Y Z Prefix New PX PY PZ NX NY NZ AP BP CP AS BS CS : Type*}
variable [Fintype AP] [Fintype BP] [Fintype CP]
variable [Fintype AS] [Fintype BS] [Fintype CS]

def expandMap {O A : Type*} (factor : ℕ) (M : X → O → A → Polynomial ℂ) :
    X → O → A → Polynomial ℂ :=
  fun x output input => Polynomial.expand ℂ factor (M x output input)

def controlledMap (kStep : ℕ)
    (previous : X → (Prefix × PX) → AP → Polynomial ℂ)
    (step : Prefix → X → (New × NX) → AS → Polynomial ℂ) :
    X → Output Prefix New PX NX → (AP × AS) → Polynomial ℂ :=
  fun x output input =>
    Polynomial.expand ℂ (kStep + 1) (previous x output.1 input.1) *
      step output.1.1 x output.2 input.2

omit [Fintype AP] [Fintype AS] in
theorem controlledMap_degree (kStep dPrevious dStep : ℕ)
    (previous : X → (Prefix × PX) → AP → Polynomial ℂ)
    (step : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (hp : ∀ x output input, (previous x output input).degree ≤ dPrevious)
    (hs : ∀ prior x output input, (step prior x output input).degree ≤ dStep)
    (x : X) (output : Output Prefix New PX NX) (input : AP × AS) :
    (controlledMap kStep previous step x output input).degree ≤
      dPrevious * (kStep + 1) + dStep := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_mul_le_of_le
  · rw [Polynomial.natDegree_expand]
    exact Nat.mul_le_mul_right (kStep + 1)
      (Polynomial.natDegree_le_of_degree_le (hp x output.1 input.1))
  · exact Polynomial.natDegree_le_of_degree_le
      (hs output.1.1 x output.2 input.2)

theorem kernel_expandMap (factor : ℕ) (auxiliary : Tensor ℂ AP BP CP)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (x : X × (Prefix × PX)) (y : Y × (Prefix × PY)) (z : Z × (Prefix × PZ)) :
    kernel auxiliary (expandMap factor MX) (expandMap factor MY) (expandMap factor MZ)
        x y z = Polynomial.expand ℂ factor (kernel auxiliary MX MY MZ x y z) := by
  simp only [kernel, fiberTransform, expandMap, map_sum, map_mul, Polynomial.expand_C]

def mixedStageKernel (auxiliary : Tensor ℂ AS BS CS)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ) :
    Tensor (Polynomial ℂ) (X × Output Prefix New PX NX)
      (Y × Output Prefix New PY NY) (Z × Output Prefix New PZ NZ) :=
  fun x y z => kernel auxiliary (SX x.2.1.1) (SY y.2.1.1) (SZ z.2.1.1)
    (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2)

def controlledKernel (kStep : ℕ)
    (previousAuxiliary : Tensor ℂ AP BP CP) (stepAuxiliary : Tensor ℂ AS BS CS)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ) :
    Tensor (Polynomial ℂ) (X × Output Prefix New PX NX)
      (Y × Output Prefix New PY NY) (Z × Output Prefix New PZ NZ) :=
  kernel (Tensor.product previousAuxiliary stepAuxiliary)
    (controlledMap kStep MX SX) (controlledMap kStep MY SY) (controlledMap kStep MZ SZ)

theorem controlledKernel_factor (kStep : ℕ)
    (previousAuxiliary : Tensor ℂ AP BP CP) (stepAuxiliary : Tensor ℂ AS BS CS)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ)
    (x : X × Output Prefix New PX NX) (y : Y × Output Prefix New PY NY)
    (z : Z × Output Prefix New PZ NZ) :
    controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ x y z =
      Polynomial.expand ℂ (kStep + 1)
        (kernel previousAuxiliary MX MY MZ (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1)) *
      mixedStageKernel stepAuxiliary SX SY SZ x y z := by
  have h := congrFun (congrFun (congrFun
    (Tensor.restrict_product (expandMap (kStep + 1) MX x.1)
      (expandMap (kStep + 1) MY y.1) (expandMap (kStep + 1) MZ z.1)
      (SX x.2.1.1 x.1) (SY y.2.1.1 y.1) (SZ z.2.1.1 z.1)
      (fun a b c => Polynomial.C (previousAuxiliary a b c))
      (fun a b c => Polynomial.C (stepAuxiliary a b c))) x.2) y.2) z.2
  have hproduct :
      controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ x y z =
        kernel previousAuxiliary (expandMap (kStep + 1) MX)
          (expandMap (kStep + 1) MY) (expandMap (kStep + 1) MZ)
          (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) *
        mixedStageKernel stepAuxiliary SX SY SZ x y z := by
    simpa only [controlledKernel, kernel, fiberTransform, Tensor.restrict, Tensor.product,
      controlledMap, expandMap, mixedStageKernel, map_mul] using h
  rw [hproduct, kernel_expandMap]

def controlledLeading
    (previous : Tensor ℂ (X × (Prefix × PX)) (Y × (Prefix × PY)) (Z × (Prefix × PZ)))
    (step : Prefix → Tensor ℂ (X × (New × NX)) (Y × (New × NY)) (Z × (New × NZ))) :
    Tensor ℂ (X × Output Prefix New PX NX) (Y × Output Prefix New PY NY)
      (Z × Output Prefix New PZ NZ) :=
  fun x y z => previous (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) *
    step x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2)

theorem controlledKernel_coefficients (dPrevious kStep : ℕ)
    (previousAuxiliary : Tensor ℂ AP BP CP) (stepAuxiliary : Tensor ℂ AS BS CS)
    (MX : X → (Prefix × PX) → AP → Polynomial ℂ)
    (MY : Y → (Prefix × PY) → BP → Polynomial ℂ)
    (MZ : Z → (Prefix × PZ) → CP → Polynomial ℂ)
    (SX : Prefix → X → (New × NX) → AS → Polynomial ℂ)
    (SY : Prefix → Y → (New × NY) → BS → Polynomial ℂ)
    (SZ : Prefix → Z → (New × NZ) → CS → Polynomial ℂ)
    (previous : Tensor ℂ (X × (Prefix × PX)) (Y × (Prefix × PY)) (Z × (Prefix × PZ)))
    (step : Prefix → Tensor ℂ (X × (New × NX)) (Y × (New × NY)) (Z × (New × NZ)))
    (support : X → Y → Z → Prop) (eligible : Prefix → X → Y → Z → Prop)
    (hprevious_low : ∀ x y z, support x.1 y.1 z.1 → ∀ j, j < dPrevious →
      (kernel previousAuxiliary MX MY MZ x y z).coeff j = 0)
    (hprevious_leading : ∀ x y z, support x.1 y.1 z.1 →
      (kernel previousAuxiliary MX MY MZ x y z).coeff dPrevious = previous x y z)
    (hprevious_support : ∀ x y z, support x.1 y.1 z.1 → previous x y z ≠ 0 →
      x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ eligible x.2.1 x.1 y.1 z.1)
    (hstep_low : ∀ prior x y z, eligible prior x.1 y.1 z.1 →
      ∀ j, j < kStep →
      (kernel stepAuxiliary (SX prior) (SY prior) (SZ prior) x y z).coeff j = 0)
    (hstep_leading : ∀ prior x y z, eligible prior x.1 y.1 z.1 →
      (kernel stepAuxiliary (SX prior) (SY prior) (SZ prior) x y z).coeff kStep =
        step prior x y z) :
    (∀ x y z, support x.1 y.1 z.1 → ∀ j, j < dPrevious * (kStep + 1) + kStep →
      (controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ x y z).coeff j = 0) ∧
    (∀ x y z, support x.1 y.1 z.1 →
      (controlledKernel kStep previousAuxiliary stepAuxiliary MX MY MZ SX SY SZ x y z).coeff
        (dPrevious * (kStep + 1) + kStep) = controlledLeading previous step x y z) := by
  have hselected : ∀ (x : X × Output Prefix New PX NX)
      (y : Y × Output Prefix New PY NY) (z : Z × Output Prefix New PZ NZ),
      support x.1 y.1 z.1 →
      previous (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) ≠ 0 →
      (∀ j, j < kStep → (mixedStageKernel stepAuxiliary SX SY SZ x y z).coeff j = 0) ∧
        (mixedStageKernel stepAuxiliary SX SY SZ x y z).coeff kStep =
          step x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2) := by
    intro x y z hs hn
    obtain ⟨hxy, hxz, he⟩ :=
      hprevious_support (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1) hs hn
    have hy : y.2.1.1 = x.2.1.1 := hxy.symm
    have hz : z.2.1.1 = x.2.1.1 := hxz.symm
    constructor
    · intro j hj
      simpa only [mixedStageKernel, hy, hz] using
        hstep_low x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2) he j hj
    · simpa only [mixedStageKernel, hy, hz] using
        hstep_leading x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2) he
  constructor
  · intro x y z hs j hj
    rw [controlledKernel_factor]
    exact expanded_mul_vanishes_of_leading_support _ _ dPrevious kStep
      (previous (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1))
      (hprevious_low _ _ _ hs) (hprevious_leading _ _ _ hs)
      (fun hn => (hselected x y z hs hn).1) j hj
  · intro x y z hs
    rw [controlledKernel_factor]
    exact expanded_mul_leading_of_leading_support _ _ dPrevious kStep
      (previous (x.1, x.2.1) (y.1, y.2.1) (z.1, z.2.1))
      (step x.2.1.1 (x.1, x.2.2) (y.1, y.2.2) (z.1, z.2.2))
      (hprevious_low _ _ _ hs) (hprevious_leading _ _ _ hs)
      (fun hn => (hselected x y z hs hn).2)

end ActualMatrices

end PolynomialControlledKernel
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialKernelExecution
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialKernelExecution

open _root_.OAI.MatrixMultiplication.Foundation.Tensor PolynomialLocalConstruction PolynomialControlledKernel

variable {X Y Z Prefix PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]

structure Execution (X Y Z Prefix PX PY PZ AX AY AZ : Type*)
    [Fintype AX] [Fintype AY] [Fintype AZ] (support : X → Y → Z → Prop) where
  auxiliary : Tensor ℂ AX AY AZ
  rankBound : ℕ
  auxiliary_rank : RankAtMost auxiliary rankBound
  order : ℕ
  leftDegree : ℕ
  middleDegree : ℕ
  rightDegree : ℕ
  leftMap : X → (Prefix × PX) → AX → Polynomial ℂ
  middleMap : Y → (Prefix × PY) → AY → Polynomial ℂ
  rightMap : Z → (Prefix × PZ) → AZ → Polynomial ℂ
  left_degree : ∀ x output input, (leftMap x output input).degree ≤ leftDegree
  middle_degree : ∀ y output input, (middleMap y output input).degree ≤ middleDegree
  right_degree : ∀ z output input, (rightMap z output input).degree ≤ rightDegree
  value : Tensor ℂ (X × (Prefix × PX)) (Y × (Prefix × PY)) (Z × (Prefix × PZ))
  vanishes : ∀ x y z, support x.1 y.1 z.1 → ∀ j < order,
    (kernel auxiliary leftMap middleMap rightMap x y z).coeff j = 0
  leading : ∀ x y z, support x.1 y.1 z.1 →
    (kernel auxiliary leftMap middleMap rightMap x y z).coeff order = value x y z
  synchronized : ∀ x y z, support x.1 y.1 z.1 → value x y z ≠ 0 →
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1

variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
variable {New NX NY NZ BX BY BZ : Type*}
variable [Fintype BX] [Fintype BY] [Fintype BZ]

structure Stage (New NX NY NZ BX BY BZ : Type*)
    [Fintype BX] [Fintype BY] [Fintype BZ] where
  auxiliary : Tensor ℂ BX BY BZ
  rankBound : ℕ
  auxiliary_rank : RankAtMost auxiliary rankBound
  order : ℕ
  leftDegree : ℕ
  middleDegree : ℕ
  rightDegree : ℕ
  leftMap : Prefix → X → (New × NX) → BX → Polynomial ℂ
  middleMap : Prefix → Y → (New × NY) → BY → Polynomial ℂ
  rightMap : Prefix → Z → (New × NZ) → BZ → Polynomial ℂ
  left_degree : ∀ prior x output input, (leftMap prior x output input).degree ≤ leftDegree
  middle_degree : ∀ prior y output input, (middleMap prior y output input).degree ≤ middleDegree
  right_degree : ∀ prior z output input, (rightMap prior z output input).degree ≤ rightDegree
  eligible : Prefix → X → Y → Z → Prop
  previous_eligible : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
    eligible x.2.1 x.1 y.1 z.1
  value : Prefix → Tensor ℂ (X × (New × NX)) (Y × (New × NY)) (Z × (New × NZ))
  vanishes : ∀ prior x y z, eligible prior x.1 y.1 z.1 → ∀ j < order,
    (kernel auxiliary (leftMap prior) (middleMap prior) (rightMap prior) x y z).coeff j = 0
  leading : ∀ prior x y z, eligible prior x.1 y.1 z.1 →
    (kernel auxiliary (leftMap prior) (middleMap prior) (rightMap prior) x y z).coeff order =
      value prior x y z
  synchronized : ∀ prior x y z, eligible prior x.1 y.1 z.1 → value prior x y z ≠ 0 →
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1

def pack {OldCoord NewCoord : Type*} :
    ((Prefix × New) × (OldCoord × NewCoord)) → Output Prefix New OldCoord NewCoord :=
  fun output => ((output.1.1, output.2.1), (output.1.2, output.2.2))

namespace Execution

variable (S : Stage E New NX NY NZ BX BY BZ)

def step : Execution X Y Z (Prefix × New) (PX × NX) (PY × NY) (PZ × NZ)
    (AX × BX) (AY × BY) (AZ × BZ) support := by
  have coefficients := controlledKernel_coefficients E.order S.order
    E.auxiliary S.auxiliary E.leftMap E.middleMap E.rightMap
    S.leftMap S.middleMap S.rightMap E.value S.value support S.eligible
    E.vanishes E.leading
    (fun x y z hs hn => ⟨(E.synchronized x y z hs hn).1,
      (E.synchronized x y z hs hn).2, S.previous_eligible x y z hs hn⟩)
    S.vanishes S.leading
  refine {
    auxiliary := Tensor.product E.auxiliary S.auxiliary
    rankBound := E.rankBound * S.rankBound
    auxiliary_rank := E.auxiliary_rank.product S.auxiliary_rank
    order := E.order * (S.order + 1) + S.order
    leftDegree := E.leftDegree * (S.order + 1) + S.leftDegree
    middleDegree := E.middleDegree * (S.order + 1) + S.middleDegree
    rightDegree := E.rightDegree * (S.order + 1) + S.rightDegree
    leftMap := fun x output input =>
      controlledMap S.order E.leftMap S.leftMap x (pack output) input
    middleMap := fun y output input =>
      controlledMap S.order E.middleMap S.middleMap y (pack output) input
    rightMap := fun z output input =>
      controlledMap S.order E.rightMap S.rightMap z (pack output) input
    left_degree := fun x output input =>
      controlledMap_degree S.order E.leftDegree S.leftDegree E.leftMap S.leftMap
        E.left_degree S.left_degree x (pack output) input
    middle_degree := fun y output input =>
      controlledMap_degree S.order E.middleDegree S.middleDegree E.middleMap S.middleMap
        E.middle_degree S.middle_degree y (pack output) input
    right_degree := fun z output input =>
      controlledMap_degree S.order E.rightDegree S.rightDegree E.rightMap S.rightMap
        E.right_degree S.right_degree z (pack output) input
    value := fun x y z => controlledLeading E.value S.value
      (x.1, pack x.2) (y.1, pack y.2) (z.1, pack z.2)
    vanishes := fun x y z hs j hj =>
      coefficients.1 (x.1, pack x.2) (y.1, pack y.2) (z.1, pack z.2) hs j hj
    leading := fun x y z hs =>
      coefficients.2 (x.1, pack x.2) (y.1, pack y.2) (z.1, pack z.2) hs
    synchronized := ?_
  }
  intro x y z hs hn
  have hproduct :
      E.value (x.1, (x.2.1.1, x.2.2.1)) (y.1, (y.2.1.1, y.2.2.1))
        (z.1, (z.2.1.1, z.2.2.1)) *
      S.value x.2.1.1 (x.1, (x.2.1.2, x.2.2.2))
        (y.1, (y.2.1.2, y.2.2.2)) (z.1, (z.2.1.2, z.2.2.2)) ≠ 0 := hn
  have hp := (mul_ne_zero_iff.mp hproduct).1
  have hs' := (mul_ne_zero_iff.mp hproduct).2
  have hprior := E.synchronized _ _ _ hs hp
  have heligible := S.previous_eligible _ _ _ hs hp
  have hnew := S.synchronized _ _ _ _ heligible hs'
  exact ⟨Prod.ext hprior.1 hnew.1, Prod.ext hprior.2 hnew.2⟩

@[simp] theorem step_rankBound : (step E S).rankBound = E.rankBound * S.rankBound := rfl

@[simp] theorem step_auxiliary :
    (step E S).auxiliary = Tensor.product E.auxiliary S.auxiliary := rfl

@[simp] theorem step_order : (step E S).order = E.order * (S.order + 1) + S.order := rfl

@[simp] theorem step_value
    (x : X × ((Prefix × New) × (PX × NX)))
    (y : Y × ((Prefix × New) × (PY × NY)))
    (z : Z × ((Prefix × New) × (PZ × NZ))) :
    (step E S).value x y z =
      E.value (x.1, (x.2.1.1, x.2.2.1)) (y.1, (y.2.1.1, y.2.2.1))
        (z.1, (z.2.1.1, z.2.2.1)) *
      S.value x.2.1.1 (x.1, (x.2.1.2, x.2.2.2))
        (y.1, (y.2.1.2, y.2.2.2)) (z.1, (z.2.1.2, z.2.2.2)) := rfl

end Execution
end MatrixMultiplication.Foundation.PolynomialKernelExecution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexConstantPolynomialKernel
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialLocalConstruction

open _root_.OAI.MatrixMultiplication.Foundation.Tensor LocalMaps

variable {X Y Z AX AY AZ OX OY OZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]

def constantMatrix (M : X → OX → AX → ℂ) : X → OX → AX → Polynomial ℂ :=
  fun x u i => Polynomial.C (M x u i)

omit [Fintype AX] in
theorem constantMatrix_degree (M : X → OX → AX → ℂ) (x : X) (u : OX) (i : AX) :
    (constantMatrix M x u i).degree ≤ (0 : ℕ) := by
  simpa only [constantMatrix, Nat.cast_zero] using
    (Polynomial.degree_C_le (a := M x u i))

theorem fiberTransform_constantMatrix
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ)
    (T : Tensor ℂ (X × AX) (Y × AY) (Z × AZ)) :
    fiberTransform (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)
      (fun x y z => Polynomial.C (T x y z)) =
      fun x y z => Polynomial.C (fiberTransform MX MY MZ T x y z) := by
  funext x y z
  simp only [fiberTransform, constantMatrix, map_sum, map_mul]

theorem kernel_constantMatrix (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ) :
    kernel auxiliary (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ) =
      fun x y z => Polynomial.C
        (fiberTransform MX MY MZ (fun x y z => auxiliary x.2 y.2 z.2) x y z) :=
  fiberTransform_constantMatrix MX MY MZ _

@[simp] theorem kernel_constantMatrix_coeff_zero (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → ℂ) (MY : Y → OY → AY → ℂ)
    (MZ : Z → OZ → AZ → ℂ) (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    (kernel auxiliary (constantMatrix MX) (constantMatrix MY) (constantMatrix MZ)
      x y z).coeff 0 =
      fiberTransform MX MY MZ (fun x y z => auxiliary x.2 y.2 z.2) x y z := by
  rw [kernel_constantMatrix]
  exact Polynomial.coeff_C_zero

section CoordinateSelectors

variable [DecidableEq AX] [DecidableEq AY] [DecidableEq AZ]

def weightedCoordinateMatrix (select : X × OX → AX) (weight : X × OX → ℂ) :
    X → OX → AX → ℂ :=
  fun x u i => if i = select (x, u) then weight (x, u) else 0

def weightedCoordinatePolynomialMatrix
    (select : X × OX → AX) (weight : X × OX → ℂ) :
    X → OX → AX → Polynomial ℂ :=
  constantMatrix (weightedCoordinateMatrix select weight)

omit [Fintype AX] in
theorem weightedCoordinatePolynomialMatrix_degree
    (select : X × OX → AX) (weight : X × OX → ℂ) (x : X) (u : OX) (i : AX) :
    (weightedCoordinatePolynomialMatrix select weight x u i).degree ≤ (0 : ℕ) :=
  constantMatrix_degree _ x u i

theorem fiberTransform_weightedCoordinateMatrix
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (wx : X × OX → ℂ) (wy : Y × OY → ℂ) (wz : Z × OZ → ℂ)
    (T : Tensor ℂ (X × AX) (Y × AY) (Z × AZ)) :
    fiberTransform (weightedCoordinateMatrix fx wx) (weightedCoordinateMatrix fy wy)
        (weightedCoordinateMatrix fz wz) T =
      fun x y z => wx x * wy y * wz z * T (x.1, fx x) (y.1, fy y) (z.1, fz z) := by
  funext x y z
  simp [fiberTransform, weightedCoordinateMatrix, ite_mul, mul_ite]

theorem kernel_weightedCoordinatePolynomialMatrix (auxiliary : Tensor ℂ AX AY AZ)
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (wx : X × OX → ℂ) (wy : Y × OY → ℂ) (wz : Z × OZ → ℂ) :
    kernel auxiliary (weightedCoordinatePolynomialMatrix fx wx)
        (weightedCoordinatePolynomialMatrix fy wy) (weightedCoordinatePolynomialMatrix fz wz) =
      fun x y z => Polynomial.C
        (wx x * wy y * wz z * auxiliary (fx x) (fy y) (fz z)) := by
  unfold weightedCoordinatePolynomialMatrix
  rw [kernel_constantMatrix, fiberTransform_weightedCoordinateMatrix]

@[simp] theorem kernel_weightedCoordinatePolynomialMatrix_coeff_zero
    (auxiliary : Tensor ℂ AX AY AZ)
    (fx : X × OX → AX) (fy : Y × OY → AY) (fz : Z × OZ → AZ)
    (wx : X × OX → ℂ) (wy : Y × OY → ℂ) (wz : Z × OZ → ℂ)
    (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    (kernel auxiliary (weightedCoordinatePolynomialMatrix fx wx)
      (weightedCoordinatePolynomialMatrix fy wy) (weightedCoordinatePolynomialMatrix fz wz)
      x y z).coeff 0 = wx x * wy y * wz z * auxiliary (fx x) (fy y) (fz z) := by
  rw [kernel_weightedCoordinatePolynomialMatrix]
  exact Polynomial.coeff_C_zero

end CoordinateSelectors

end MatrixMultiplication.Foundation.PolynomialLocalConstruction

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPrefixSeparationPolynomialStage
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PrefixSeparationPolynomialStage

open _root_.OAI.MatrixMultiplication.Foundation.Tensor LabelHierarchySeparation PolynomialLocalConstruction

variable {Prefix X Y Z : Type*}

abbrev InformedOutput (k : ℕ) := Fin k × Fin k
abbrev MissingOutput (k : ℕ) := Fin k × PUnit

theorem exists_auxiliary_coordinates (k : ℕ) :
    ∃ (left right : Fin k → Fin k → PoolAuxiliaryGroup k)
      (tag : Fin k → PoolAuxiliaryGroup k),
      ∀ s s' i j,
        poolAuxiliaryTensor k (left s i) (right s j) (tag s') =
          if s = s' ∧ i = j then 1 else 0 := by
  classical
  by_cases hk : k = 1
  · subst k
    refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ => 0, ?_⟩
    intro s s' i j
    simp [poolAuxiliaryTensor, Tensor.rankOne, Subsingleton.elim s s',
      Subsingleton.elim i j]
  · obtain ⟨tag, point, collision⟩ := Separation.exists_modular_separation
      (Separation.grid_population_bound k) (Separation.grid_population_bound k)
    refine ⟨point, fun s j => tag s - point s j, tag, ?_⟩
    intro s s' i j
    simp only [poolAuxiliaryTensor, ite_eq_right hk, groupTensor, collision]

def informedWeight {k : ℕ} (keep : X → Prop) (code : X → Fin k) :
    X × InformedOutput k → ℂ := by
  classical
  exact fun x => if keep x.1 ∧ x.2.1 = code x.1 then 1 else 0

def missingWeight {k : ℕ} (keep : Z → Prop) : Z × MissingOutput k → ℂ := by
  classical
  exact fun z => if keep z.1 then 1 else 0

def stageLeading (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeY : Prefix → Y → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) :
    Tensor ℂ (X × InformedOutput k) (Y × InformedOutput k) (Z × MissingOutput k) := by
  classical
  exact fun x y z => if
      (keepX prior x.1 ∧ x.2.1 = codeX prior x.1) ∧
      (keepY prior y.1 ∧ y.2.1 = codeY prior y.1) ∧
      keepZ prior z.1 ∧
      (codeX prior x.1 = z.2.1 ∧ x.2.2 = y.2.2)
    then 1 else 0

theorem stageLeading_synchronized (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeY : Prefix → Y → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix)
    (x : X × InformedOutput k) (y : Y × InformedOutput k) (z : Z × MissingOutput k)
    (codes : codeX prior x.1 = codeY prior y.1)
    (nonzero : stageLeading k codeX codeY keepX keepY keepZ prior x y z ≠ 0) :
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ x.2.2 = y.2.2 := by
  classical
  have guard :
      (keepX prior x.1 ∧ x.2.1 = codeX prior x.1) ∧
      (keepY prior y.1 ∧ y.2.1 = codeY prior y.1) ∧
      keepZ prior z.1 ∧
      (codeX prior x.1 = z.2.1 ∧ x.2.2 = y.2.2) := by
    by_contra hn
    exact nonzero (by simp [stageLeading, hn])
  exact ⟨guard.1.2.trans (codes.trans guard.2.1.2.symm),
    guard.1.2.trans guard.2.2.2.1, guard.2.2.2.2⟩

theorem exists_prefix_stage (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeY : Prefix → Y → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → codeX p x = codeY p y) :
    ∃ (MX : Prefix → X → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (poolAuxiliaryTensor k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (stageLeading k codeX codeY keepX keepY keepZ p x y z) := by
  classical
  obtain ⟨left, right, tag, coefficients⟩ := exists_auxiliary_coordinates k
  let fx : Prefix → X × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p x => left (codeX p x.1) x.2.2
  let fy : Prefix → Y × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p y => right (codeY p y.1) y.2.2
  let fz : Prefix → Z × MissingOutput k → PoolAuxiliaryGroup k :=
    fun _ z => tag z.2.1
  let MX := fun p => weightedCoordinatePolynomialMatrix (fx p)
    (informedWeight (keepX p) (codeX p))
  let MY := fun p => weightedCoordinatePolynomialMatrix (fy p)
    (informedWeight (keepY p) (codeY p))
  let MZ := fun p => weightedCoordinatePolynomialMatrix (fz p) (missingWeight (keepZ p))
  refine ⟨MX, MY, MZ, ?_, ?_, ?_, ?_⟩
  · intro p x u i
    exact weightedCoordinatePolynomialMatrix_degree _ _ x u i
  · intro p y v j
    exact weightedCoordinatePolynomialMatrix_degree _ _ y v j
  · intro p z w l
    exact weightedCoordinatePolynomialMatrix_degree _ _ z w l
  · intro p x y z h
    have codes := agree p x.1 y.1 z.1 h
    change kernel (poolAuxiliaryTensor k)
      (weightedCoordinatePolynomialMatrix (fx p) (informedWeight (keepX p) (codeX p)))
      (weightedCoordinatePolynomialMatrix (fy p) (informedWeight (keepY p) (codeY p)))
      (weightedCoordinatePolynomialMatrix (fz p) (missingWeight (keepZ p))) x y z = _
    rw [kernel_weightedCoordinatePolynomialMatrix]
    dsimp only [fx, fy, fz]
    rw [← codes, coefficients]
    congr 1
    unfold informedWeight missingWeight stageLeading
    split_ifs <;> simp_all

section RawPools

variable {RawLabel : Type*} [DecidableEq RawLabel]

def maskedPoolCode (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k) (p : Prefix) (label : RawLabel) : Fin k := by
  classical
  exact if h : label ∈ pool p then (poolEnumeration pool k counts p) ⟨label, h⟩
    else ⟨0, positive⟩

theorem maskedPoolCode_decode (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (p : Prefix) (label : RawLabel) (allowed : label ∈ pool p) :
    ((poolEnumeration pool k counts p).symm
      (maskedPoolCode pool k positive counts p label)).val = label := by
  simp [maskedPoolCode, allowed]

def rawPoolLeading (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readY : Prefix → Y → RawLabel) :
    Prefix → Tensor ℂ (X × InformedOutput k) (Y × InformedOutput k)
      (Z × MissingOutput k) :=
  stageLeading k
    (fun p x => maskedPoolCode pool k positive counts p (readX p x))
    (fun p y => maskedPoolCode pool k positive counts p (readY p y))
    (fun p x => readX p x ∈ pool p) (fun p y => readY p y ∈ pool p)
    (fun _ _ => True)

theorem exists_raw_pool_stage (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readY : Prefix → Y → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readY p y) :
    ∃ (MX : Prefix → X → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (poolAuxiliaryTensor k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (rawPoolLeading pool k positive counts readX readY p x y z) := by
  apply exists_prefix_stage k
    (fun p x => maskedPoolCode pool k positive counts p (readX p x))
    (fun p y => maskedPoolCode pool k positive counts p (readY p y))
    (fun p x => readX p x ∈ pool p) (fun p y => readY p y ∈ pool p)
    (fun _ _ => True) eligible
  intro p x y z h
  exact congrArg (maskedPoolCode pool k positive counts p) (agree p x y z h)

end RawPools

end MatrixMultiplication.Foundation.PrefixSeparationPolynomialStage

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexConditionalHierarchyStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.ConditionalHierarchyStage

open _root_.OAI.MatrixMultiplication.Foundation.Tensor PolynomialLocalConstruction PolynomialKernelExecution
open PrefixSeparationPolynomialStage LabelHierarchySeparation

variable {Prefix RawLabel X Y Z : Type*} [DecidableEq RawLabel]

def decodePool (pool : Prefix → Finset RawLabel) (k : ℕ)
    (counts : ∀ p, (pool p).card = k) (p : Prefix) (q : Fin k) : RawLabel :=
  ((poolEnumeration pool k counts p).symm q).val

omit [DecidableEq RawLabel] in
theorem decodePool_mem (pool : Prefix → Finset RawLabel) (k : ℕ)
    (counts : ∀ p, (pool p).card = k) (p : Prefix) (q : Fin k) :
    decodePool pool k counts p q ∈ pool p :=
  ((poolEnumeration pool k counts p).symm q).property

theorem decodePool_eq_iff (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (p : Prefix) (q : Fin k) (s : RawLabel) :
    decodePool pool k counts p q = s ↔
      s ∈ pool p ∧ q = maskedPoolCode pool k positive counts p s := by
  classical
  constructor
  · intro h
    have hs : s ∈ pool p := h ▸ decodePool_mem pool k counts p q
    refine ⟨hs, ?_⟩
    have hsub : (poolEnumeration pool k counts p).symm q = ⟨s, hs⟩ :=
      Subtype.ext h
    have hcode := congrArg (poolEnumeration pool k counts p) hsub
    simpa [maskedPoolCode, hs] using hcode
  · rintro ⟨hs, rfl⟩
    exact maskedPoolCode_decode pool k positive counts p s hs

def decodedLeading (pool : Prefix → Finset RawLabel) (k : ℕ)
    (counts : ∀ p, (pool p).card = k)
    (fine : Prefix → X → Y → Z → RawLabel) (p : Prefix) :
    Tensor ℂ (X × InformedOutput k) (Y × InformedOutput k)
      (Z × MissingOutput k) := by
  classical
  exact fun x y z => if
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
      decodePool pool k counts p x.2.1 = fine p x.1 y.1 z.1 ∧ x.2.2 = y.2.2
    then 1 else 0

theorem rawPoolLeading_eq_decodedLeading (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readY : Prefix → Y → RawLabel)
    (fine : Prefix → X → Y → Z → RawLabel) (p : Prefix)
    (x : X × InformedOutput k) (y : Y × InformedOutput k) (z : Z × MissingOutput k)
    (hx : readX p x.1 = fine p x.1 y.1 z.1)
    (hy : readY p y.1 = fine p x.1 y.1 z.1) :
    rawPoolLeading pool k positive counts readX readY p x y z =
      decodedLeading pool k counts fine p x y z := by
  classical
  unfold rawPoolLeading stageLeading decodedLeading
  simp only [hx, hy]
  congr 1
  apply propext
  constructor
  · rintro ⟨⟨hmem, hxc⟩, ⟨_, hyc⟩, _, hcz, hij⟩
    exact ⟨hxc.trans hyc.symm, hxc.trans hcz,
      (decodePool_eq_iff pool k positive counts p x.2.1 _).mpr ⟨hmem, hxc⟩, hij⟩
  · rintro ⟨hxy, hxz, hdecode, hij⟩
    obtain ⟨hmem, hxc⟩ := (decodePool_eq_iff pool k positive counts p x.2.1 _).mp hdecode
    exact ⟨⟨hmem, hxc⟩, ⟨hmem, hxy.symm.trans hxc⟩, trivial,
      hxc.symm.trans hxz, hij⟩

section ExecutionStage

variable {PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}

theorem exists_rawPoolStage
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readY : Prefix → Y → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readY p y) :
    ∃ S : Stage E (Fin k) (Fin k) (Fin k) PUnit
        (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k),
      S.auxiliary = poolAuxiliaryTensor k ∧
      S.rankBound = poolAuxiliaryCost k ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeading pool k positive counts readX readY := by
  classical
  obtain ⟨MX, MY, MZ, hMX, hMY, hMZ, hkernel⟩ :=
    exists_raw_pool_stage pool k positive counts readX readY eligible agree
  let S : Stage E (Fin k) (Fin k) (Fin k) PUnit
      (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) := {
    auxiliary := poolAuxiliaryTensor k
    rankBound := poolAuxiliaryCost k
    auxiliary_rank := poolAuxiliaryTensor_rankAtMost k
    order := 0
    leftDegree := 0
    middleDegree := 0
    rightDegree := 0
    leftMap := MX
    middleMap := MY
    rightMap := MZ
    left_degree := hMX
    middle_degree := hMY
    right_degree := hMZ
    eligible := eligible
    previous_eligible := previous
    value := rawPoolLeading pool k positive counts readX readY
    vanishes := by
      intro _ _ _ _ _ j hj
      exact (Nat.not_lt_zero j hj).elim
    leading := by
      intro p x y z he
      rw [hkernel p x y z he]
      exact Polynomial.coeff_C_zero
    synchronized := by
      intro p x y z he hn
      have hread := agree p x.1 y.1 z.1 he
      have hcodes : maskedPoolCode pool k positive counts p (readX p x.1) =
          maskedPoolCode pool k positive counts p (readY p y.1) := congrArg _ hread
      have hsync := stageLeading_synchronized k _ _ _ _ _ p x y z hcodes hn
      exact ⟨hsync.1, hsync.2.1⟩
  }
  exact ⟨S, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ExecutionStage

section ExactConditionalPools

open ConditionalPrefixWords StageHierarchyResources LabelHierarchyCounts

variable {A Position : Type*} [Fintype A] [Fintype Position]
variable {Label : ℕ → Type*} [∀ n, Fintype (Label n)]
variable (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)

local instance (priority := low) instDecidableEq_solutions {B : Type*} : DecidableEq B := Classical.decEq B

def actualPool
    (priorWord : Prefix → ExactPrefix counts labels n t Position) :
    Prefix → Finset (Position → Label n) :=
  fun p => conditionalFinset (priorWord p)

theorem actualPool_card
    (priorWord : Prefix → ExactPrefix counts labels n t Position) (p : Prefix) :
    (actualPool counts labels n t priorWord p).card = stageRefinementCount counts labels n t :=
  conditionalFinset_card (priorWord p)

theorem exists_actualPoolStage
    {PX PY PZ AX AY AZ : Type*} [Fintype AX] [Fintype AY] [Fintype AZ]
    {support : X → Y → Z → Prop}
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (readX : Prefix → X → Position → Label n)
    (readY : Prefix → Y → Position → Label n)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readY p y) :
    ∃ S : Stage E (Fin (stageRefinementCount counts labels n t))
        (Fin (stageRefinementCount counts labels n t))
        (Fin (stageRefinementCount counts labels n t)) PUnit
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t)),
      S.auxiliary = poolAuxiliaryTensor (stageRefinementCount counts labels n t) ∧
      S.rankBound = stageCost counts labels n t ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeading (actualPool counts labels n t priorWord)
        (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
        (actualPool_card counts labels n t priorWord) readX readY := by
  exact exists_rawPoolStage E (actualPool counts labels n t priorWord)
    (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
    (actualPool_card counts labels n t priorWord) readX readY eligible previous agree

end ExactConditionalPools

end MatrixMultiplication.Foundation.ConditionalHierarchyStage

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexPrefixSeparationOrientations
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PrefixSeparationOrientations

open _root_.OAI.MatrixMultiplication.Foundation.Tensor LabelHierarchySeparation PolynomialLocalConstruction
open PrefixSeparationPolynomialStage

variable {Prefix X Y Z : Type*}

def auxiliaryXZ (k : ℕ) :
    Tensor ℂ (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) :=
  fun a b c => poolAuxiliaryTensor k a c b

def auxiliaryYZ (k : ℕ) :
    Tensor ℂ (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) :=
  fun a b c => poolAuxiliaryTensor k b c a

theorem auxiliaryXZ_rankAtMost (k : ℕ) :
    RankAtMost (auxiliaryXZ k) (poolAuxiliaryCost k) := by
  obtain ⟨a, b, c, h⟩ := poolAuxiliaryTensor_rankAtMost k
  refine ⟨a, c, b, ?_⟩
  funext x y z
  change poolAuxiliaryTensor k x z y = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

theorem auxiliaryYZ_rankAtMost (k : ℕ) :
    RankAtMost (auxiliaryYZ k) (poolAuxiliaryCost k) := by
  obtain ⟨a, b, c, h⟩ := poolAuxiliaryTensor_rankAtMost k
  refine ⟨c, a, b, ?_⟩
  funext x y z
  change poolAuxiliaryTensor k y z x = _
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [rankOne]
  ring

def stageLeadingXZ (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) :
    Tensor ℂ (X × InformedOutput k) (Y × MissingOutput k) (Z × InformedOutput k) :=
  fun x y z => stageLeading k codeX codeZ keepX keepZ keepY prior x z y

def stageLeadingYZ (k : ℕ)
    (codeY : Prefix → Y → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix) :
    Tensor ℂ (X × MissingOutput k) (Y × InformedOutput k) (Z × InformedOutput k) :=
  fun x y z => stageLeading k codeY codeZ keepY keepZ keepX prior y z x

theorem stageLeadingXZ_synchronized (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix)
    (x : X × InformedOutput k) (y : Y × MissingOutput k) (z : Z × InformedOutput k)
    (codes : codeX prior x.1 = codeZ prior z.1)
    (nonzero : stageLeadingXZ k codeX codeZ keepX keepY keepZ prior x y z ≠ 0) :
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ x.2.2 = z.2.2 := by
  obtain ⟨hxz, hxy, hij⟩ := stageLeading_synchronized k codeX codeZ
    keepX keepZ keepY prior x z y codes nonzero
  exact ⟨hxy, hxz, hij⟩

theorem stageLeadingYZ_synchronized (k : ℕ)
    (codeY : Prefix → Y → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop) (prior : Prefix)
    (x : X × MissingOutput k) (y : Y × InformedOutput k) (z : Z × InformedOutput k)
    (codes : codeY prior y.1 = codeZ prior z.1)
    (nonzero : stageLeadingYZ k codeY codeZ keepX keepY keepZ prior x y z ≠ 0) :
    x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ y.2.2 = z.2.2 := by
  obtain ⟨hyz, hyx, hij⟩ := stageLeading_synchronized k codeY codeZ
    keepY keepZ keepX prior y z x codes nonzero
  exact ⟨hyx.symm, hyx.symm.trans hyz, hij⟩

theorem exists_prefix_stage_XZ (k : ℕ)
    (codeX : Prefix → X → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → codeX p x = codeZ p z) :
    ∃ (MX : Prefix → X → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (auxiliaryXZ k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (stageLeadingXZ k codeX codeZ keepX keepY keepZ p x y z) := by
  classical
  obtain ⟨left, right, tag, coefficients⟩ := exists_auxiliary_coordinates k
  let fx : Prefix → X × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p x => left (codeX p x.1) x.2.2
  let fy : Prefix → Y × MissingOutput k → PoolAuxiliaryGroup k := fun _ y => tag y.2.1
  let fz : Prefix → Z × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p z => right (codeZ p z.1) z.2.2
  let MX := fun p => weightedCoordinatePolynomialMatrix (fx p)
    (informedWeight (keepX p) (codeX p))
  let MY := fun p => weightedCoordinatePolynomialMatrix (fy p) (missingWeight (keepY p))
  let MZ := fun p => weightedCoordinatePolynomialMatrix (fz p)
    (informedWeight (keepZ p) (codeZ p))
  refine ⟨MX, MY, MZ, ?_, ?_, ?_, ?_⟩
  · intro p x u i
    exact weightedCoordinatePolynomialMatrix_degree _ _ x u i
  · intro p y v j
    exact weightedCoordinatePolynomialMatrix_degree _ _ y v j
  · intro p z w l
    exact weightedCoordinatePolynomialMatrix_degree _ _ z w l
  · intro p x y z h
    have codes := agree p x.1 y.1 z.1 h
    change kernel (auxiliaryXZ k)
      (weightedCoordinatePolynomialMatrix (fx p) (informedWeight (keepX p) (codeX p)))
      (weightedCoordinatePolynomialMatrix (fy p) (missingWeight (keepY p)))
      (weightedCoordinatePolynomialMatrix (fz p) (informedWeight (keepZ p) (codeZ p))) x y z = _
    rw [kernel_weightedCoordinatePolynomialMatrix]
    dsimp only [fx, fy, fz, auxiliaryXZ]
    rw [← codes, coefficients]
    congr 1
    unfold informedWeight missingWeight stageLeadingXZ stageLeading
    split_ifs <;> simp_all

theorem exists_prefix_stage_YZ (k : ℕ)
    (codeY : Prefix → Y → Fin k) (codeZ : Prefix → Z → Fin k)
    (keepX : Prefix → X → Prop) (keepY : Prefix → Y → Prop)
    (keepZ : Prefix → Z → Prop)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → codeY p y = codeZ p z) :
    ∃ (MX : Prefix → X → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (auxiliaryYZ k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (stageLeadingYZ k codeY codeZ keepX keepY keepZ p x y z) := by
  classical
  obtain ⟨left, right, tag, coefficients⟩ := exists_auxiliary_coordinates k
  let fx : Prefix → X × MissingOutput k → PoolAuxiliaryGroup k := fun _ x => tag x.2.1
  let fy : Prefix → Y × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p y => left (codeY p y.1) y.2.2
  let fz : Prefix → Z × InformedOutput k → PoolAuxiliaryGroup k :=
    fun p z => right (codeZ p z.1) z.2.2
  let MX := fun p => weightedCoordinatePolynomialMatrix (fx p) (missingWeight (keepX p))
  let MY := fun p => weightedCoordinatePolynomialMatrix (fy p)
    (informedWeight (keepY p) (codeY p))
  let MZ := fun p => weightedCoordinatePolynomialMatrix (fz p)
    (informedWeight (keepZ p) (codeZ p))
  refine ⟨MX, MY, MZ, ?_, ?_, ?_, ?_⟩
  · intro p x u i
    exact weightedCoordinatePolynomialMatrix_degree _ _ x u i
  · intro p y v j
    exact weightedCoordinatePolynomialMatrix_degree _ _ y v j
  · intro p z w l
    exact weightedCoordinatePolynomialMatrix_degree _ _ z w l
  · intro p x y z h
    have codes := agree p x.1 y.1 z.1 h
    change kernel (auxiliaryYZ k)
      (weightedCoordinatePolynomialMatrix (fx p) (missingWeight (keepX p)))
      (weightedCoordinatePolynomialMatrix (fy p) (informedWeight (keepY p) (codeY p)))
      (weightedCoordinatePolynomialMatrix (fz p) (informedWeight (keepZ p) (codeZ p))) x y z = _
    rw [kernel_weightedCoordinatePolynomialMatrix]
    dsimp only [fx, fy, fz, auxiliaryYZ]
    rw [← codes, coefficients]
    congr 1
    unfold informedWeight missingWeight stageLeadingYZ stageLeading
    split_ifs <;> simp_all

section RawPools

variable {RawLabel : Type*} [DecidableEq RawLabel]

def rawPoolLeadingXZ (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readZ : Prefix → Z → RawLabel) (prior : Prefix) :
    Tensor ℂ (X × InformedOutput k) (Y × MissingOutput k) (Z × InformedOutput k) :=
  fun x y z => rawPoolLeading pool k positive counts readX readZ prior x z y

def rawPoolLeadingYZ (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readY : Prefix → Y → RawLabel) (readZ : Prefix → Z → RawLabel) (prior : Prefix) :
    Tensor ℂ (X × MissingOutput k) (Y × InformedOutput k) (Z × InformedOutput k) :=
  fun x y z => rawPoolLeading pool k positive counts readY readZ prior y z x

theorem exists_raw_pool_stage_XZ (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readZ : Prefix → Z → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readZ p z) :
    ∃ (MX : Prefix → X → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (auxiliaryXZ k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (rawPoolLeadingXZ pool k positive counts readX readZ p x y z) := by
  apply exists_prefix_stage_XZ k
    (fun p x => maskedPoolCode pool k positive counts p (readX p x))
    (fun p z => maskedPoolCode pool k positive counts p (readZ p z))
    (fun p x => readX p x ∈ pool p) (fun _ _ => True)
    (fun p z => readZ p z ∈ pool p) eligible
  intro p x y z h
  exact congrArg (maskedPoolCode pool k positive counts p) (agree p x y z h)

theorem exists_raw_pool_stage_YZ (pool : Prefix → Finset RawLabel) (k : ℕ)
    (positive : 0 < k) (counts : ∀ p, (pool p).card = k)
    (readY : Prefix → Y → RawLabel) (readZ : Prefix → Z → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (agree : ∀ p x y z, eligible p x y z → readY p y = readZ p z) :
    ∃ (MX : Prefix → X → MissingOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MY : Prefix → Y → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ)
      (MZ : Prefix → Z → InformedOutput k → PoolAuxiliaryGroup k → Polynomial ℂ),
      (∀ p x u i, (MX p x u i).degree ≤ (0 : ℕ)) ∧
      (∀ p y v j, (MY p y v j).degree ≤ (0 : ℕ)) ∧
      (∀ p z w l, (MZ p z w l).degree ≤ (0 : ℕ)) ∧
      ∀ p x y z, eligible p x.1 y.1 z.1 →
        kernel (auxiliaryYZ k) (MX p) (MY p) (MZ p) x y z =
          Polynomial.C (rawPoolLeadingYZ pool k positive counts readY readZ p x y z) := by
  apply exists_prefix_stage_YZ k
    (fun p y => maskedPoolCode pool k positive counts p (readY p y))
    (fun p z => maskedPoolCode pool k positive counts p (readZ p z))
    (fun _ _ => True) (fun p y => readY p y ∈ pool p)
    (fun p z => readZ p z ∈ pool p) eligible
  intro p x y z h
  exact congrArg (maskedPoolCode pool k positive counts p) (agree p x y z h)

end RawPools
end MatrixMultiplication.Foundation.PrefixSeparationOrientations

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexBalancedSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.BalancedSeparation

open scoped BigOperators
open _root_.OAI.MatrixMultiplication.Foundation.Tensor LabelHierarchySeparation

section SinglePool

def singlePairingX (k : ℕ) : (Fin 1 × Fin k) ≃ Fin k where
  toFun x := x.2
  invFun x := (0, x)
  left_inv _ := Prod.ext (Subsingleton.elim _ _) rfl
  right_inv _ := rfl

def singlePairingY (k : ℕ) : (Fin k × Fin 1) ≃ Fin k where
  toFun y := y.1
  invFun y := (y, 0)
  left_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  right_inv _ := rfl

def singlePairingZ : (Fin 1 × Fin 1) ≃ Unit where
  toFun _ := ()
  invFun _ := (0, 0)
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end SinglePool

end MatrixMultiplication.Foundation.BalancedSeparation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexInitialTargetKernel
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.Foundation.InitialTargetKernel

open _root_.OAI.MatrixMultiplication.Foundation.Tensor LocalMaps PolynomialLocalConstruction

variable {X Y Z RawLabel Label : Type*}

def Chosen (window : X → Prop) (read : X → RawLabel) (embed : Label → RawLabel)
    (label : Label) (x : X) : Prop :=
  window x ∧ read x = embed label

def Eligible (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (label : Label) : X → Y → Z → Prop :=
  fun x y z => Chosen PX lx embed label x ∧ Chosen PY ly embed label y ∧
    Chosen PZ lz embed label z

def auxiliary : Tensor ℂ Unit Unit Unit := fun _ _ _ => 1

theorem auxiliary_rank : RankAtMost auxiliary 1 := by
  have haux : auxiliary = rankOne (fun _ : Unit => (1 : ℂ))
      (fun _ : Unit => (1 : ℂ)) (fun _ : Unit => (1 : ℂ)) := by
    funext x y z
    simp only [auxiliary, rankOne, one_mul]
  rw [haux]
  exact rankOne_rankAtMost _ _ _

def sideMap (window : X → Prop) (read : X → RawLabel) (embed : Label → RawLabel) :
    X → (Label × (Fin 1 × Fin 1)) → Unit → Polynomial ℂ := by
  classical
  exact fun x output _ => Polynomial.C (if Chosen window read embed output.1 x then 1 else 0)

theorem sideMap_degree (window : X → Prop) (read : X → RawLabel)
    (embed : Label → RawLabel) (x : X) (output : Label × (Fin 1 × Fin 1)) (input : Unit) :
    (sideMap window read embed x output input).degree ≤ (0 : ℕ) := by
  classical
  exact Polynomial.degree_C_le

def rawLeading (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) :
    Tensor ℂ (X × (Label × (Fin 1 × Fin 1)))
      (Y × (Label × (Fin 1 × Fin 1))) (Z × (Label × (Fin 1 × Fin 1))) := by
  classical
  exact fun x y z => if Chosen PX lx embed x.2.1 x.1 ∧
      Chosen PY ly embed y.2.1 y.1 ∧ Chosen PZ lz embed z.2.1 z.1 then 1 else 0

def previousLeading (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) :
    Tensor ℂ (X × (Label × (Fin 1 × Fin 1)))
      (Y × (Label × (Fin 1 × Fin 1))) (Z × (Label × (Fin 1 × Fin 1))) := by
  classical
  exact fun x y z => if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
    Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1 then 1 else 0

theorem kernel_eq_C_rawLeading (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1))) :
    kernel auxiliary (sideMap PX lx embed) (sideMap PY ly embed) (sideMap PZ lz embed)
      x y z = Polynomial.C (rawLeading PX PY PZ lx ly lz embed x y z) := by
  classical
  by_cases hx : Chosen PX lx embed x.2.1 x.1 <;>
    by_cases hy : Chosen PY ly embed y.2.1 y.1 <;>
    by_cases hz : Chosen PZ lz embed z.2.1 z.1 <;>
    simp [kernel, fiberTransform, sideMap, auxiliary, rawLeading, hx, hy, hz]

theorem rawLeading_eq_previousLeading
    (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (injective : Function.Injective embed)
    (support : X → Y → Z → Prop)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      lx x = ly y ∧ lx x = lz z)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1)))
    (hs : support x.1 y.1 z.1) :
    rawLeading PX PY PZ lx ly lz embed x y z =
      previousLeading PX PY PZ lx ly lz embed x y z := by
  classical
  have hcondition :
      (Chosen PX lx embed x.2.1 x.1 ∧ Chosen PY ly embed y.2.1 y.1 ∧
        Chosen PZ lz embed z.2.1 z.1) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1) := by
    constructor
    · rintro ⟨hx, hy, hz⟩
      have hsync := compatible x.1 y.1 z.1 hs hx.1 hy.1 hz.1
      have hxy : x.2.1 = y.2.1 := injective (hx.2.symm.trans (hsync.1.trans hy.2))
      have hxz : x.2.1 = z.2.1 := injective (hx.2.symm.trans (hsync.2.trans hz.2))
      refine ⟨hxy, hxz, hx, ?_, ?_⟩
      · simpa only [hxy] using hy
      · simpa only [hxz] using hz
    · rintro ⟨hxy, hxz, hx, hy, hz⟩
      refine ⟨hx, ?_, ?_⟩
      · simpa only [hxy] using hy
      · simpa only [hxz] using hz
  simp only [rawLeading, previousLeading, hcondition]

theorem kernel_leading (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (injective : Function.Injective embed)
    (support : X → Y → Z → Prop)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      lx x = ly y ∧ lx x = lz z)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1)))
    (hs : support x.1 y.1 z.1) :
    (kernel auxiliary (sideMap PX lx embed) (sideMap PY ly embed) (sideMap PZ lz embed)
      x y z).coeff 0 = previousLeading PX PY PZ lx ly lz embed x y z := by
  rw [kernel_eq_C_rawLeading, Polynomial.coeff_C_zero]
  exact rawLeading_eq_previousLeading PX PY PZ lx ly lz embed injective support
    compatible x y z hs

theorem kernel_low (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1)))
    (j : ℕ) (hj : j < 0) :
    (kernel auxiliary (sideMap PX lx embed) (sideMap PY ly embed) (sideMap PZ lz embed)
      x y z).coeff j = 0 :=
  (Nat.not_lt_zero j hj).elim

theorem previousLeading_ne_zero_iff (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel)
    (x : X × (Label × (Fin 1 × Fin 1)))
    (y : Y × (Label × (Fin 1 × Fin 1))) (z : Z × (Label × (Fin 1 × Fin 1))) :
    previousLeading PX PY PZ lx ly lz embed x y z ≠ 0 ↔
      x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1 := by
  classical
  by_cases h : x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
      Eligible PX PY PZ lx ly lz embed x.2.1 x.1 y.1 z.1 <;>
    simp [previousLeading, h]

end MatrixMultiplication.Foundation.InitialTargetKernel

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexInitialTargetExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.InitialTargetExecution

open _root_.OAI.MatrixMultiplication.Foundation.Tensor LocalMaps PolynomialLocalConstruction PolynomialKernelExecution

variable {X Y Z RawLabel Label : Type*}

def scalarOutput : Label × Unit → Label × (Fin 1 × Fin 1) :=
  fun output => (output.1, (0, 0))

def initial (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
    (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
    (embed : Label → RawLabel) (injective : Function.Injective embed)
    (support : X → Y → Z → Prop)
    (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
      lx x = ly y ∧ lx x = lz z) :
    Execution X Y Z Label Unit Unit Unit Unit Unit Unit support where
  auxiliary := InitialTargetKernel.auxiliary
  rankBound := 1
  auxiliary_rank := InitialTargetKernel.auxiliary_rank
  order := 0
  leftDegree := 0
  middleDegree := 0
  rightDegree := 0
  leftMap := fun x output input =>
    InitialTargetKernel.sideMap PX lx embed x (scalarOutput output) input
  middleMap := fun y output input =>
    InitialTargetKernel.sideMap PY ly embed y (scalarOutput output) input
  rightMap := fun z output input =>
    InitialTargetKernel.sideMap PZ lz embed z (scalarOutput output) input
  left_degree := fun x output input =>
    InitialTargetKernel.sideMap_degree PX lx embed x (scalarOutput output) input
  middle_degree := fun y output input =>
    InitialTargetKernel.sideMap_degree PY ly embed y (scalarOutput output) input
  right_degree := fun z output input =>
    InitialTargetKernel.sideMap_degree PZ lz embed z (scalarOutput output) input
  value := fun x y z => InitialTargetKernel.previousLeading PX PY PZ lx ly lz embed
    (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2)
  vanishes := fun x y z _ j hj =>
    InitialTargetKernel.kernel_low PX PY PZ lx ly lz embed
      (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2) j hj
  leading := fun x y z hs =>
    InitialTargetKernel.kernel_leading PX PY PZ lx ly lz embed injective support compatible
      (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2) hs
  synchronized := by
    intro x y z _ hn
    have h := (InitialTargetKernel.previousLeading_ne_zero_iff PX PY PZ lx ly lz embed
      (x.1, scalarOutput x.2) (y.1, scalarOutput y.2) (z.1, scalarOutput z.2)).mp hn
    exact ⟨h.1, h.2.1⟩

variable (PX : X → Prop) (PY : Y → Prop) (PZ : Z → Prop)
variable (lx : X → RawLabel) (ly : Y → RawLabel) (lz : Z → RawLabel)
variable (embed : Label → RawLabel) (injective : Function.Injective embed)
variable (support : X → Y → Z → Prop)
variable (compatible : ∀ x y z, support x y z → PX x → PY y → PZ z →
  lx x = ly y ∧ lx x = lz z)

@[simp] theorem initial_rankBound :
    (initial PX PY PZ lx ly lz embed injective support compatible).rankBound = 1 := rfl

@[simp] theorem initial_order :
    (initial PX PY PZ lx ly lz embed injective support compatible).order = 0 := rfl

end MatrixMultiplication.Foundation.InitialTargetExecution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexExecutionPairingBudget
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.Foundation.ExecutionPairingBudget

open scoped BigOperators
open _root_.OAI.MatrixMultiplication.Foundation.Tensor PolynomialKernelExecution BalancedSeparation LabelHierarchySeparation

structure MatrixCoordinates (PX PY PZ : Type*) where
  rows : ℕ
  inner : ℕ
  columns : ℕ
  left : PX ≃ (Fin rows × Fin inner)
  middle : PY ≃ (Fin inner × Fin columns)
  right : PZ ≃ (Fin columns × Fin rows)

namespace MatrixCoordinates

variable {PX PY PZ NX NY NZ : Type*}

def volume (shape : MatrixCoordinates PX PY PZ) : ℕ :=
  shape.rows * shape.inner * shape.columns

def Positive (shape : MatrixCoordinates PX PY PZ) : Prop :=
  0 < shape.rows ∧ 0 < shape.inner ∧ 0 < shape.columns

def tensor (shape : MatrixCoordinates PX PY PZ) : Tensor ℂ PX PY PZ :=
  Tensor.pullback shape.left shape.middle shape.right
    (matrixCoefficients (Fin shape.rows) (Fin shape.inner) (Fin shape.columns))

def standard (a b c : ℕ) :
    MatrixCoordinates (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) where
  rows := a
  inner := b
  columns := c
  left := Equiv.refl _
  middle := Equiv.refl _
  right := Equiv.refl _

@[simp] theorem standard_volume (a b c : ℕ) : (standard a b c).volume = a * b * c := rfl

@[simp] theorem standard_tensor (a b c : ℕ) :
    (standard a b c).tensor = matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c) := rfl

def scalar : MatrixCoordinates Unit Unit Unit where
  rows := 1
  inner := 1
  columns := 1
  left := singlePairingZ.symm
  middle := singlePairingZ.symm
  right := singlePairingZ.symm

@[simp] theorem scalar_volume : scalar.volume = 1 := rfl

@[simp] theorem scalar_tensor : scalar.tensor = fun _ _ _ => (1 : ℂ) := by
  funext x y z
  rfl

def pairProductEquiv (a b c d : ℕ) :
    ((Fin a × Fin b) × (Fin c × Fin d)) ≃ (Fin (a * c) × Fin (b * d)) :=
  (Equiv.prodProdProdComm (Fin a) (Fin b) (Fin c) (Fin d)).trans
    (Equiv.prodCongr (@finProdFinEquiv a c) (@finProdFinEquiv b d))

@[simp] theorem pairProductEquiv_apply (a b c d : ℕ)
    (x : (Fin a × Fin b) × (Fin c × Fin d)) :
    pairProductEquiv a b c d x =
      (finProdFinEquiv (x.1.1, x.2.1), finProdFinEquiv (x.1.2, x.2.2)) := rfl

def product (old : MatrixCoordinates PX PY PZ) (new : MatrixCoordinates NX NY NZ) :
    MatrixCoordinates (PX × NX) (PY × NY) (PZ × NZ) where
  rows := old.rows * new.rows
  inner := old.inner * new.inner
  columns := old.columns * new.columns
  left := (Equiv.prodCongr old.left new.left).trans
    (pairProductEquiv old.rows old.inner new.rows new.inner)
  middle := (Equiv.prodCongr old.middle new.middle).trans
    (pairProductEquiv old.inner old.columns new.inner new.columns)
  right := (Equiv.prodCongr old.right new.right).trans
    (pairProductEquiv old.columns old.rows new.columns new.rows)

@[simp] theorem product_volume (old : MatrixCoordinates PX PY PZ)
    (new : MatrixCoordinates NX NY NZ) :
    (product old new).volume = old.volume * new.volume := by
  simp only [volume, product]
  ring

theorem product_positive (old : MatrixCoordinates PX PY PZ)
    (new : MatrixCoordinates NX NY NZ) (hold : old.Positive) (hnew : new.Positive) :
    (product old new).Positive :=
  ⟨Nat.mul_pos hold.1 hnew.1, Nat.mul_pos hold.2.1 hnew.2.1,
    Nat.mul_pos hold.2.2 hnew.2.2⟩

theorem product_tensor (old : MatrixCoordinates PX PY PZ)
    (new : MatrixCoordinates NX NY NZ) :
    (product old new).tensor = Tensor.product old.tensor new.tensor := by
  funext x y z
  have h := matrixCoefficients_product (K := ℂ)
    (((old.left x.1).1, (new.left x.2).1), ((old.left x.1).2, (new.left x.2).2))
    (((old.middle y.1).1, (new.middle y.2).1),
      ((old.middle y.1).2, (new.middle y.2).2))
    (((old.right z.1).1, (new.right z.2).1),
      ((old.right z.1).2, (new.right z.2).2))
  change matrixCoefficients (K := ℂ) (Fin (old.rows * new.rows))
    (Fin (old.inner * new.inner)) (Fin (old.columns * new.columns))
    (finProdFinEquiv ((old.left x.1).1, (new.left x.2).1),
      finProdFinEquiv ((old.left x.1).2, (new.left x.2).2))
    (finProdFinEquiv ((old.middle y.1).1, (new.middle y.2).1),
      finProdFinEquiv ((old.middle y.1).2, (new.middle y.2).2))
    (finProdFinEquiv ((old.right z.1).1, (new.right z.2).1),
      finProdFinEquiv ((old.right z.1).2, (new.right z.2).2)) = _
  simpa only [tensor, product, Tensor.pullback, Tensor.product,
    Equiv.trans_apply, Equiv.prodCongr_apply, pairProductEquiv_apply,
    matrixCoefficients, Equiv.apply_eq_iff_eq] using h.symm

end MatrixCoordinates

end MatrixMultiplication.Foundation.ExecutionPairingBudget

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexGeometricStageCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.Foundation.GeometricStageCoordinates

open _root_.OAI.MatrixMultiplication.Foundation.Tensor BalancedSeparation LabelHierarchySeparation ExecutionPairingBudget

def scalarPair : PUnit ≃ (Fin 1 × Fin 1) where
  toFun _ := (0, 0)
  invFun _ := PUnit.unit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

def xy (k : ℕ) : MatrixCoordinates (Fin k) (Fin k) PUnit where
  rows := 1
  inner := k
  columns := 1
  left := (singlePairingX k).symm
  middle := (singlePairingY k).symm
  right := scalarPair

def xz (k : ℕ) : MatrixCoordinates (Fin k) PUnit (Fin k) where
  rows := k
  inner := 1
  columns := 1
  left := (singlePairingY k).symm
  middle := scalarPair
  right := (singlePairingX k).symm

def yz (k : ℕ) : MatrixCoordinates PUnit (Fin k) (Fin k) where
  rows := 1
  inner := 1
  columns := k
  left := scalarPair
  middle := (singlePairingX k).symm
  right := (singlePairingY k).symm

@[simp] theorem xy_tensor_apply (k : ℕ) (x y : Fin k) (z : PUnit) :
    (xy k).tensor x y z = if x = y then 1 else 0 := by
  change (if x = y ∧ (0 : Fin 1) = 0 ∧ (0 : Fin 1) = 0 then (1 : ℂ) else 0) = _
  simp

@[simp] theorem xz_tensor_apply (k : ℕ) (x : Fin k) (y : PUnit) (z : Fin k) :
    (xz k).tensor x y z = if x = z then 1 else 0 := by
  change (if (0 : Fin 1) = 0 ∧ (0 : Fin 1) = 0 ∧ z = x then (1 : ℂ) else 0) = _
  simp [eq_comm]

@[simp] theorem yz_tensor_apply (k : ℕ) (x : PUnit) (y z : Fin k) :
    (yz k).tensor x y z = if y = z then 1 else 0 := by
  change (if (0 : Fin 1) = 0 ∧ y = z ∧ (0 : Fin 1) = 0 then (1 : ℂ) else 0) = _
  simp

@[simp] theorem xy_volume (k : ℕ) : (xy k).volume = k := by
  simp [MatrixCoordinates.volume, xy]

@[simp] theorem xz_volume (k : ℕ) : (xz k).volume = k := by
  simp [MatrixCoordinates.volume, xz]

@[simp] theorem yz_volume (k : ℕ) : (yz k).volume = k := by
  simp [MatrixCoordinates.volume, yz]

theorem xy_positive {k : ℕ} (hk : 0 < k) : (xy k).Positive :=
  ⟨Nat.zero_lt_one, hk, Nat.zero_lt_one⟩

theorem xz_positive {k : ℕ} (hk : 0 < k) : (xz k).Positive :=
  ⟨hk, Nat.zero_lt_one, Nat.zero_lt_one⟩

theorem yz_positive {k : ℕ} (hk : 0 < k) : (yz k).Positive :=
  ⟨Nat.zero_lt_one, Nat.zero_lt_one, hk⟩

end MatrixMultiplication.Foundation.GeometricStageCoordinates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedGeometricValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedGeometricValues

open MatrixMultiplication.Foundation
open ComplexWitness CW75LabelHierarchy CW75ReorderedWords ConditionalPrefixWords
open ConditionalHierarchyStage PrefixSeparationPolynomialStage PrefixSeparationOrientations
open StageHierarchyResources
open scoped Classical

variable {Position : Type*} [Fintype Position] {counts : Scalar → ℕ} {n t : ℕ}

abbrev size (counts : Scalar → ℕ) (n t : ℕ) := stageRefinementCount counts curveLabels n t

theorem actualPool_decode (old : ExactPrefix counts curveLabels n t Position)
    (code : Fin (size counts n t)) :
    decodePool (actualPool counts curveLabels n t id) (size counts n t)
      (actualPool_card counts curveLabels n t id) old code =
        ((conditionalPoolEquivFin old).symm code).val := rfl

theorem decode_eq_iff_eligible (old : ExactPrefix counts curveLabels n t Position)
    (code : Fin (size counts n t)) (u v w : LongWord Position)
    (word : Position → Scalar) (hword : Represents id old u v w word) :
    decodePool (actualPool counts curveLabels n t id) (size counts n t)
      (actualPool_card counts curveLabels n t id) old code = (fun i => curveLabels n (word i)) ↔
        eligible id (appendCode old code) u v w := by
  rw [actualPool_decode]
  exact (eligible_appendCode_iff_of_represents old code u v w word hword).symm

theorem first_read (old : ExactPrefix counts curveLabels n t Position)
    (u v w : LongWord Position) (word : Position → Scalar) (hn : n < 5)
    (hword : Represents id old u v w word) :
    firstRead id old (coordinateOf (curveFirstSide n) u v w) = fun i => curveLabels n (word i) := by
  rw [hword.1, hword.2.1, hword.2.2.1, coordinateOf_original]
  exact firstRead_on_original_word id old word hn hword.2.2.2

theorem second_read (old : ExactPrefix counts curveLabels n t Position)
    (u v w : LongWord Position) (word : Position → Scalar) (hn : n < 5)
    (hword : Represents id old u v w word) :
    secondRead id old (coordinateOf (curveSecondSide n) u v w) = fun i => curveLabels n (word i) := by
  rw [hword.1, hword.2.1, hword.2.2.1, coordinateOf_original]
  exact secondRead_on_original_word id old word hn hword.2.2.2

theorem raw_XY_normal
    (old : ExactPrefix counts curveLabels n t Position) (hn : n < 5)
    (hfirst : curveFirstSide n = .x) (hsecond : curveSecondSide n = .y)
    (x : LongWord Position × InformedOutput (size counts n t))
    (y : LongWord Position × InformedOutput (size counts n t))
    (z : LongWord Position × MissingOutput (size counts n t))
    (word : Position → Scalar) (hword : Represents id old x.1 y.1 z.1 word) :
    rawPoolLeading (actualPool counts curveLabels n t id) (size counts n t)
      (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
      (firstRead id) (secondRead id) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.xy (size counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hx := first_read old x.1 y.1 z.1 word hn hword
  have hy := second_read old x.1 y.1 z.1 word hn hword
  simp only [hfirst, coordinateOf] at hx
  simp only [hsecond, coordinateOf] at hy
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts curveLabels n t id) (size counts n t)
    (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
    (firstRead id) (secondRead id) (fun _ _ _ _ => fun i => curveLabels n (word i))
    old x y z hx hy]
  unfold decodedLeading
  simp only [decode_eq_iff_eligible old x.2.1 x.1 y.1 z.1 word hword,
    GeometricStageCoordinates.xy_tensor_apply]
  simp only [ite_and]

theorem raw_XZ_normal
    (old : ExactPrefix counts curveLabels n t Position) (hn : n < 5)
    (hfirst : curveFirstSide n = .x) (hsecond : curveSecondSide n = .z)
    (x : LongWord Position × InformedOutput (size counts n t))
    (y : LongWord Position × MissingOutput (size counts n t))
    (z : LongWord Position × InformedOutput (size counts n t))
    (word : Position → Scalar) (hword : Represents id old x.1 y.1 z.1 word) :
    rawPoolLeadingXZ (actualPool counts curveLabels n t id) (size counts n t)
      (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
      (firstRead id) (secondRead id) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.xz (size counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hx := first_read old x.1 y.1 z.1 word hn hword
  have hz := second_read old x.1 y.1 z.1 word hn hword
  simp only [hfirst, coordinateOf] at hx
  simp only [hsecond, coordinateOf] at hz
  unfold rawPoolLeadingXZ
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts curveLabels n t id) (size counts n t)
    (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
    (firstRead id) (secondRead id) (fun _ _ _ _ => fun i => curveLabels n (word i))
    old x z y hx hz]
  unfold decodedLeading
  simp only [decode_eq_iff_eligible old x.2.1 x.1 y.1 z.1 word hword,
    GeometricStageCoordinates.xz_tensor_apply]
  have hswap :
      (x.2.1 = z.2.1 ∧ x.2.1 = y.2.1 ∧
        eligible id (appendCode old x.2.1) x.1 y.1 z.1 ∧ x.2.2 = z.2.2) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible id (appendCode old x.2.1) x.1 y.1 z.1 ∧ x.2.2 = z.2.2) :=
    and_left_comm
  simp only [hswap, ite_and]

theorem raw_YZ_normal
    (old : ExactPrefix counts curveLabels n t Position) (hn : n < 5)
    (hfirst : curveFirstSide n = .y) (hsecond : curveSecondSide n = .z)
    (x : LongWord Position × MissingOutput (size counts n t))
    (y : LongWord Position × InformedOutput (size counts n t))
    (z : LongWord Position × InformedOutput (size counts n t))
    (word : Position → Scalar) (hword : Represents id old x.1 y.1 z.1 word) :
    rawPoolLeadingYZ (actualPool counts curveLabels n t id) (size counts n t)
      (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
      (firstRead id) (secondRead id) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.yz (size counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hy := first_read old x.1 y.1 z.1 word hn hword
  have hz := second_read old x.1 y.1 z.1 word hn hword
  simp only [hfirst, coordinateOf] at hy
  simp only [hsecond, coordinateOf] at hz
  unfold rawPoolLeadingYZ
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts curveLabels n t id) (size counts n t)
    (stageRefinementCount_pos counts curveLabels n t) (actualPool_card counts curveLabels n t id)
    (firstRead id) (secondRead id) (fun _ _ _ _ => fun i => curveLabels n (word i))
    old y z x hy hz]
  have hguard :
      (y.2.1 = z.2.1 ∧ y.2.1 = x.2.1 ∧
        decodePool (actualPool counts curveLabels n t id) (size counts n t)
          (actualPool_card counts curveLabels n t id) old y.2.1 = (fun i => curveLabels n (word i)) ∧
        y.2.2 = z.2.2) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible id (appendCode old x.2.1) x.1 y.1 z.1 ∧ y.2.2 = z.2.2) := by
    constructor
    · rintro ⟨hyz, hyx, hdecode, hpair⟩
      refine ⟨hyx.symm, hyx.symm.trans hyz, ?_, hpair⟩
      apply (decode_eq_iff_eligible old x.2.1 x.1 y.1 z.1 word hword).mp
      simpa only [hyx] using hdecode
    · rintro ⟨hxy, hxz, he, hpair⟩
      refine ⟨hxy.symm.trans hxz, hxy.symm, ?_, hpair⟩
      have hdecode := (decode_eq_iff_eligible old x.2.1 x.1 y.1 z.1 word hword).mpr he
      simpa only [hxy] using hdecode
  unfold decodedLeading
  simp only [hguard, GeometricStageCoordinates.yz_tensor_apply]
  simp only [ite_and]

end MatrixMultiplication.CW75ReorderedGeometricValues

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCW75InitialExecution
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.InitialTargetExecution.initial_order _root_.OAI.MatrixMultiplication.Foundation.InitialTargetExecution.initial_rankBound _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero _root_.OAI.MatrixMultiplication.RecursiveCompletion.complete_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coppersmith–Winograd tensors, tensor powers and local restrictions. -/

noncomputable section

namespace MatrixMultiplication.Foundation.CW75InitialExecution

open Polynomial
open scoped BigOperators Classical

abbrev Word := CW75Primitive.Word
abbrev Blocks (N : ℕ) := Fin N → Word

def fullSource (N : ℕ) : Tensor ℂ (Blocks N) (Blocks N) (Blocks N) :=
  Tensor.power (Tensor.power CoppersmithWinograd.tensor 3) N

def support {N : ℕ} (x y z : Blocks N) : Prop := fullSource N x y z ≠ 0

theorem support_iff {N : ℕ} (x y z : Blocks N) :
    support x y z ↔ ∀ i j, (x i j).val + (y i j).val + (z i j).val = 2 := by
  simp [support, fullSource, Tensor.power, Finset.prod_ne_zero_iff,
    CWOriginalWords.tensor_ne_zero_iff]

def boundaryPolynomial (x y z : Word) : Polynomial ℂ :=
  ∏ i, CWBoundary.scalingPolynomial (x i) (y i) (z i)

def boundaryNormalized (x y z : Word) : Polynomial ℂ :=
  ∏ i, (C (CWBoundary.tensor (x i) (y i) (z i)) +
    X ^ 2 * C (CWBoundary.deleted (x i) (y i) (z i)))

theorem boundaryPolynomial_factor (x y z : Word) :
    boundaryPolynomial x y z = X ^ 3 * boundaryNormalized x y z := by
  have hp (i : Fin 3) : CWBoundary.scalingPolynomial (x i) (y i) (z i) =
      X * (C (CWBoundary.tensor (x i) (y i) (z i)) +
        X ^ 2 * C (CWBoundary.deleted (x i) (y i) (z i))) := by
    rw [CWBoundary.scalingPolynomial_apply]
    ring
  simp [boundaryPolynomial, boundaryNormalized, hp, Finset.prod_mul_distrib]

theorem boundaryPolynomial_vanishes (x y z : Word) (j : ℕ) (hj : j < 3) :
    (boundaryPolynomial x y z).coeff j = 0 := by
  rw [boundaryPolynomial_factor]
  simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hj, ite_false, if_false]

theorem boundaryPolynomial_leading (x y z : Word) :
    (boundaryPolynomial x y z).coeff 3 = CW75Primitive.source x y z := by
  rw [boundaryPolynomial_factor]
  simp [Polynomial.coeff_X_pow_mul', boundaryNormalized,
    Polynomial.coeff_zero_prod, CW75Primitive.source, Tensor.power]

def completionPolynomial (x y z : Word) : Polynomial ℂ :=
  (if CW75Primitive.hasB x then X else 1) *
    (if CW75Primitive.hasC y then X else 1) *
      (if CW75Primitive.allA z then 0 else 1)

theorem boundary_one (x y z : Fin 3) (h : CWBoundary.tensor x y z ≠ 0) :
    CWBoundary.tensor x y z = 1 := by
  by_cases hd : x = 1 ∧ y = 0 ∧ z = 1
  · simp [CWBoundary.tensor, hd] at h
  · by_cases hs : x.val + y.val + z.val = 2
    · simp [CWBoundary.tensor, CoppersmithWinograd.tensor, hd, hs]
    · simp [CWBoundary.tensor, CoppersmithWinograd.tensor, hd, hs] at h

theorem boundarySource_one (x y z : Word) (h : CW75Primitive.source x y z ≠ 0) :
    CW75Primitive.source x y z = 1 := by
  unfold CW75Primitive.source Tensor.power
  apply Finset.prod_eq_one
  intro i hi
  exact boundary_one _ _ _ (CW75Primitive.source_factors x y z h i)

theorem retained_coefficient_one (x y z : Word) (h : CW75Primitive.tensor x y z ≠ 0) :
    CW75Primitive.tensor x y z = 1 := by
  by_cases hr : CW75Primitive.retained x y z
  · rw [CW75Primitive.tensor, ite_eq_left hr] at h ⊢
    exact boundarySource_one x y z h
  · simp [CW75Primitive.tensor, hr] at h

theorem completion_eq (x y z : Word) (h : CW75Primitive.source x y z ≠ 0) :
    completionPolynomial x y z = CW75Primitive.polynomial x y z := by
  have hone := boundarySource_one x y z h
  rw [CW75Primitive.polynomial_apply]
  by_cases hz : CW75Primitive.allA z <;> simp [completionPolynomial, hone, hz]

theorem source_mul_retained (x y z : Word) :
    CW75Primitive.source x y z * CW75Primitive.tensor x y z =
      CW75Primitive.tensor x y z := by
  by_cases hs : CW75Primitive.source x y z = 0
  · simp [CW75Primitive.tensor, hs]
  · rw [boundarySource_one x y z hs, one_mul]

def leftBlock (x : Word) : Polynomial ℂ :=
  Polynomial.expand ℂ 2 (∏ i, CWBoundary.outerWeight X (x i)) *
    (if CW75Primitive.hasB x then X else 1)

def middleBlock (y : Word) : Polynomial ℂ :=
  Polynomial.expand ℂ 2 (∏ i, CWBoundary.middleWeight X (y i)) *
    (if CW75Primitive.hasC y then X else 1)

def rightBlock (z : Word) : Polynomial ℂ :=
  Polynomial.expand ℂ 2 (∏ i, CWBoundary.outerWeight X (z i)) *
    (if CW75Primitive.allA z then 0 else 1)

def blockKernel (x y z : Word) : Polynomial ℂ := leftBlock x * middleBlock y * rightBlock z

theorem blockKernel_factor (x y z : Word)
    (hs : ∀ i, (x i).val + (y i).val + (z i).val = 2) :
    blockKernel x y z = Polynomial.expand ℂ 2 (boundaryPolynomial x y z) *
      completionPolynomial x y z := by
  have hpoint (i : Fin 3) :
      CWBoundary.outerWeight X (x i) * CWBoundary.middleWeight X (y i) *
        CWBoundary.outerWeight X (z i) = CWBoundary.scalingPolynomial (x i) (y i) (z i) := by
    unfold CWBoundary.scalingPolynomial
    rw [CWBoundary.outerMap, CWBoundary.middleMap, CWBoundary.restrict_diagonal_apply]
    simp [CoppersmithWinograd.tensor, hs i]
  have hprod : (∏ i, CWBoundary.outerWeight X (x i)) *
      (∏ i, CWBoundary.middleWeight X (y i)) * (∏ i, CWBoundary.outerWeight X (z i)) =
      boundaryPolynomial x y z := by
    simp only [boundaryPolynomial, ← hpoint, Finset.prod_mul_distrib]
  calc
    blockKernel x y z = Polynomial.expand ℂ 2
        ((∏ i, CWBoundary.outerWeight X (x i)) *
          (∏ i, CWBoundary.middleWeight X (y i)) * (∏ i, CWBoundary.outerWeight X (z i))) *
        completionPolynomial x y z := by
      simp only [blockKernel, leftBlock, middleBlock, rightBlock, completionPolynomial, map_mul]
      ring
    _ = _ := by rw [hprod]

theorem blockKernel_vanishes (x y z : Word)
    (hs : ∀ i, (x i).val + (y i).val + (z i).val = 2)
    (j : ℕ) (hj : j < 7) : (blockKernel x y z).coeff j = 0 := by
  rw [blockKernel_factor x y z hs]
  apply PolynomialControlledKernel.expanded_mul_vanishes_of_leading_support
    (boundaryPolynomial x y z) (completionPolynomial x y z) 3 1
    (CW75Primitive.source x y z)
    (boundaryPolynomial_vanishes x y z) (boundaryPolynomial_leading x y z) _ j hj
  intro hn k hk
  rw [completion_eq x y z hn]
  have hkzero : k = 0 := by omega
  subst k
  simp [CW75Primitive.polynomial_coeff]

theorem blockKernel_leading (x y z : Word)
    (hs : ∀ i, (x i).val + (y i).val + (z i).val = 2) :
    (blockKernel x y z).coeff 7 = CW75Primitive.tensor x y z := by
  rw [blockKernel_factor x y z hs]
  have h := PolynomialControlledKernel.expanded_mul_leading_of_leading_support
    (boundaryPolynomial x y z) (completionPolynomial x y z) 3 1
    (CW75Primitive.source x y z) (CW75Primitive.tensor x y z)
    (boundaryPolynomial_vanishes x y z) (boundaryPolynomial_leading x y z) (by
      intro hn
      rw [completion_eq x y z hn]
      simp [CW75Primitive.polynomial_coeff])
  exact h.trans (source_mul_retained x y z)

theorem degree_product {n D : ℕ} (f : Fin n → Polynomial ℂ)
    (h : ∀ i, (f i).degree ≤ D) : (∏ i, f i).degree ≤ D * n := by
  apply Polynomial.degree_le_of_natDegree_le
  calc
    (∏ i, f i).natDegree ≤ ∑ i, (f i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : Fin n, D := by
      apply Finset.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_le_of_degree_le (h i)
    _ = D * n := by simp [Nat.mul_comm]

theorem degree_expanded_product (P Q : Polynomial ℂ) {d e : ℕ}
    (hP : P.degree ≤ d) (hQ : Q.degree ≤ e) :
    (Polynomial.expand ℂ 2 P * Q).degree ≤ d * 2 + e := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_mul_le_of_le
  · rw [Polynomial.natDegree_expand]
    exact Nat.mul_le_mul_right 2 (Polynomial.natDegree_le_of_degree_le hP)
  · exact Polynomial.natDegree_le_of_degree_le hQ

theorem outerWeight_degree (a : Fin 3) :
    (CWBoundary.outerWeight (X : Polynomial ℂ) a).degree ≤ 1 := by
  by_cases h : a = 1 <;> simp [CWBoundary.outerWeight, h]

theorem middleWeight_degree (a : Fin 3) :
    (CWBoundary.middleWeight (X : Polynomial ℂ) a).degree ≤ 1 := by
  by_cases h : a = 1 <;> simp [CWBoundary.middleWeight, h]

theorem leftBlock_degree (x : Word) : (leftBlock x).degree ≤ 7 := by
  apply degree_expanded_product (d := 3) (e := 1)
    (∏ i, CWBoundary.outerWeight X (x i)) (if CW75Primitive.hasB x then X else 1)
    (degree_product _ (fun i => outerWeight_degree (x i)))
  by_cases h : CW75Primitive.hasB x <;> simp [h]

theorem middleBlock_degree (y : Word) : (middleBlock y).degree ≤ 7 := by
  apply degree_expanded_product (d := 3) (e := 1)
    (∏ i, CWBoundary.middleWeight X (y i)) (if CW75Primitive.hasC y then X else 1)
    (degree_product _ (fun i => middleWeight_degree (y i)))
  by_cases h : CW75Primitive.hasC y <;> simp [h]

theorem rightBlock_degree (z : Word) : (rightBlock z).degree ≤ 6 := by
  apply degree_expanded_product (d := 3) (e := 0)
    (∏ i, CWBoundary.outerWeight X (z i)) (if CW75Primitive.allA z then 0 else 1)
    (degree_product _ (fun i => outerWeight_degree (z i)))
  by_cases h : CW75Primitive.allA z <;> simp [h]

def auxiliary : Tensor ℂ PUnit.{1} PUnit.{1} PUnit.{1} := fun _ _ _ => 1

theorem auxiliary_rank : Tensor.RankAtMost auxiliary 1 := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext x y z
  simp [auxiliary, Tensor.rankOne]

def leftMap {N : ℕ} (x : Blocks N) (_ : PUnit.{1} × PUnit.{1}) (_ : PUnit.{1}) : Polynomial ℂ :=
  ∏ i, leftBlock (x i)

def middleMap {N : ℕ} (y : Blocks N) (_ : PUnit.{1} × PUnit.{1}) (_ : PUnit.{1}) : Polynomial ℂ :=
  ∏ i, middleBlock (y i)

def rightMap {N : ℕ} (z : Blocks N) (_ : PUnit.{1} × PUnit.{1}) (_ : PUnit.{1}) : Polynomial ℂ :=
  ∏ i, rightBlock (z i)

def value {N : ℕ} : Tensor ℂ (Blocks N × (PUnit.{1} × PUnit.{1}))
    (Blocks N × (PUnit.{1} × PUnit.{1})) (Blocks N × (PUnit.{1} × PUnit.{1})) :=
  fun x y z => ∏ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i)

theorem kernel_eq {N : ℕ} (x y z : Blocks N × (PUnit.{1} × PUnit.{1})) :
    PolynomialLocalConstruction.kernel auxiliary leftMap middleMap rightMap x y z =
      ∏ i, blockKernel (x.1 i) (y.1 i) (z.1 i) := by
  simp [PolynomialLocalConstruction.kernel, LocalMaps.fiberTransform,
    auxiliary, leftMap, middleMap, rightMap, blockKernel, Finset.prod_mul_distrib]

theorem kernel_coefficients {N : ℕ} (x y z : Blocks N × (PUnit.{1} × PUnit.{1}))
    (hs : support x.1 y.1 z.1) :
    (∀ j, j < 7 * N →
      (PolynomialLocalConstruction.kernel auxiliary leftMap middleMap rightMap x y z).coeff j = 0) ∧
    (PolynomialLocalConstruction.kernel auxiliary leftMap middleMap rightMap x y z).coeff (7 * N) =
      value x y z := by
  have hsites := (support_iff x.1 y.1 z.1).mp hs
  have hd (i : Fin N) : X ^ 7 ∣ blockKernel (x.1 i) (y.1 i) (z.1 i) :=
    Polynomial.X_pow_dvd_iff.mpr (blockKernel_vanishes _ _ _ (hsites i))
  let Q : Fin N → Polynomial ℂ := fun i => Classical.choose (hd i)
  have hQ (i : Fin N) : blockKernel (x.1 i) (y.1 i) (z.1 i) = X ^ 7 * Q i :=
    Classical.choose_spec (hd i)
  have hQzero (i : Fin N) : (Q i).coeff 0 = CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) := by
    have h := blockKernel_leading _ _ _ (hsites i)
    rw [hQ] at h
    simpa only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self] using h
  have hfactor : (∏ i, blockKernel (x.1 i) (y.1 i) (z.1 i)) =
      X ^ (7 * N) * ∏ i, Q i := by
    simp only [hQ, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← pow_mul]
  simp only [kernel_eq, hfactor]
  constructor
  · intro j hj
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hj, ite_false, if_false]
  · simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self,
      Polynomial.coeff_zero_prod, hQzero, value]

def execution (N : ℕ) : PolynomialKernelExecution.Execution
    (Blocks N) (Blocks N) (Blocks N) PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} PUnit.{1} support where
  auxiliary := auxiliary
  rankBound := 1
  auxiliary_rank := auxiliary_rank
  order := 7 * N
  leftDegree := 7 * N
  middleDegree := 7 * N
  rightDegree := 6 * N
  leftMap := leftMap
  middleMap := middleMap
  rightMap := rightMap
  left_degree := fun x _ _ => degree_product _ (fun i => leftBlock_degree (x i))
  middle_degree := fun y _ _ => degree_product _ (fun i => middleBlock_degree (y i))
  right_degree := fun z _ _ => degree_product _ (fun i => rightBlock_degree (z i))
  value := value
  vanishes := fun x y z hs => (kernel_coefficients x y z hs).1
  leading := fun x y z hs => (kernel_coefficients x y z hs).2
  synchronized := fun _ _ _ _ _ => ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

@[simp] theorem execution_value (N : ℕ) : (execution N).value = value := rfl

theorem value_ne_zero_iff {N : ℕ} (x y z : Blocks N × (PUnit.{1} × PUnit.{1})) :
    (execution N).value x y z ≠ 0 ↔
      ∀ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) ≠ 0 := by
  simp [execution_value, value, Finset.prod_ne_zero_iff]

theorem value_retained {N : ℕ} (x y z : Blocks N × (PUnit.{1} × PUnit.{1})) :
    (execution N).value x y z =
      if ∀ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) ≠ 0 then 1 else 0 := by
  by_cases h : ∀ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) ≠ 0
  · simp only [ite_eq_left h, execution_value, value]
    apply Finset.prod_eq_one
    intro i hi
    exact retained_coefficient_one _ _ _ (h i)
  · rw [ite_eq_right h]
    by_contra hn
    exact h ((value_ne_zero_iff x y z).mp hn)

end MatrixMultiplication.Foundation.CW75InitialExecution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexOrientedConditionalHierarchyStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation.OrientedConditionalHierarchyStage

open _root_.OAI.MatrixMultiplication.Foundation.Tensor PolynomialLocalConstruction PolynomialKernelExecution
open PrefixSeparationPolynomialStage PrefixSeparationOrientations LabelHierarchySeparation
open ConditionalHierarchyStage

variable {Prefix RawLabel X Y Z : Type*} [DecidableEq RawLabel]

section ExecutionStage

variable {PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}

theorem exists_rawPoolStage_XZ
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readX : Prefix → X → RawLabel) (readZ : Prefix → Z → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readZ p z) :
    ∃ S : Stage E (Fin k) (Fin k) PUnit (Fin k)
        (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k),
      S.auxiliary = auxiliaryXZ k ∧
      S.rankBound = poolAuxiliaryCost k ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeadingXZ pool k positive counts readX readZ := by
  classical
  obtain ⟨MX, MY, MZ, hMX, hMY, hMZ, hkernel⟩ :=
    exists_raw_pool_stage_XZ pool k positive counts readX readZ eligible agree
  let S : Stage E (Fin k) (Fin k) PUnit (Fin k)
      (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) := {
    auxiliary := auxiliaryXZ k
    rankBound := poolAuxiliaryCost k
    auxiliary_rank := auxiliaryXZ_rankAtMost k
    order := 0
    leftDegree := 0
    middleDegree := 0
    rightDegree := 0
    leftMap := MX
    middleMap := MY
    rightMap := MZ
    left_degree := hMX
    middle_degree := hMY
    right_degree := hMZ
    eligible := eligible
    previous_eligible := previous
    value := rawPoolLeadingXZ pool k positive counts readX readZ
    vanishes := by
      intro _ _ _ _ _ j hj
      exact (Nat.not_lt_zero j hj).elim
    leading := by
      intro p x y z he
      rw [hkernel p x y z he]
      exact Polynomial.coeff_C_zero
    synchronized := by
      intro p x y z he hn
      have hread := agree p x.1 y.1 z.1 he
      have hcodes : maskedPoolCode pool k positive counts p (readX p x.1) =
          maskedPoolCode pool k positive counts p (readZ p z.1) := congrArg _ hread
      have hsync := stageLeadingXZ_synchronized k _ _ _ _ _ p x y z hcodes hn
      exact ⟨hsync.1, hsync.2.1⟩
  }
  exact ⟨S, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem exists_rawPoolStage_YZ
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (pool : Prefix → Finset RawLabel) (k : ℕ) (positive : 0 < k)
    (counts : ∀ p, (pool p).card = k)
    (readY : Prefix → Y → RawLabel) (readZ : Prefix → Z → RawLabel)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readY p y = readZ p z) :
    ∃ S : Stage E (Fin k) PUnit (Fin k) (Fin k)
        (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k),
      S.auxiliary = auxiliaryYZ k ∧
      S.rankBound = poolAuxiliaryCost k ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeadingYZ pool k positive counts readY readZ := by
  classical
  obtain ⟨MX, MY, MZ, hMX, hMY, hMZ, hkernel⟩ :=
    exists_raw_pool_stage_YZ pool k positive counts readY readZ eligible agree
  let S : Stage E (Fin k) PUnit (Fin k) (Fin k)
      (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) (PoolAuxiliaryGroup k) := {
    auxiliary := auxiliaryYZ k
    rankBound := poolAuxiliaryCost k
    auxiliary_rank := auxiliaryYZ_rankAtMost k
    order := 0
    leftDegree := 0
    middleDegree := 0
    rightDegree := 0
    leftMap := MX
    middleMap := MY
    rightMap := MZ
    left_degree := hMX
    middle_degree := hMY
    right_degree := hMZ
    eligible := eligible
    previous_eligible := previous
    value := rawPoolLeadingYZ pool k positive counts readY readZ
    vanishes := by
      intro _ _ _ _ _ j hj
      exact (Nat.not_lt_zero j hj).elim
    leading := by
      intro p x y z he
      rw [hkernel p x y z he]
      exact Polynomial.coeff_C_zero
    synchronized := by
      intro p x y z he hn
      have hread := agree p x.1 y.1 z.1 he
      have hcodes : maskedPoolCode pool k positive counts p (readY p y.1) =
          maskedPoolCode pool k positive counts p (readZ p z.1) := congrArg _ hread
      have hsync := stageLeadingYZ_synchronized k _ _ _ _ _ p x y z hcodes hn
      exact ⟨hsync.1, hsync.2.1⟩
  }
  exact ⟨S, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ExecutionStage

section ExactConditionalPools

open ConditionalPrefixWords StageHierarchyResources LabelHierarchyCounts

variable {A Position : Type*} [Fintype A] [Fintype Position]
variable {Label : ℕ → Type*} [∀ n, Fintype (Label n)]
variable (counts : A → ℕ) (labels : ∀ n, A → Label n) (n t : ℕ)

local instance (priority := low) instDecidableEq_solutions {B : Type*} : DecidableEq B := Classical.decEq B

theorem exists_actualPoolStage_XZ
    {PX PY PZ AX AY AZ : Type*} [Fintype AX] [Fintype AY] [Fintype AZ]
    {support : X → Y → Z → Prop}
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (readX : Prefix → X → Position → Label n)
    (readZ : Prefix → Z → Position → Label n)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readX p x = readZ p z) :
    ∃ S : Stage E (Fin (stageRefinementCount counts labels n t))
        (Fin (stageRefinementCount counts labels n t)) PUnit
        (Fin (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t)),
      S.auxiliary = auxiliaryXZ (stageRefinementCount counts labels n t) ∧
      S.rankBound = stageCost counts labels n t ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeadingXZ (actualPool counts labels n t priorWord)
        (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
        (actualPool_card counts labels n t priorWord) readX readZ := by
  exact exists_rawPoolStage_XZ E (actualPool counts labels n t priorWord)
    (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
    (actualPool_card counts labels n t priorWord) readX readZ eligible previous agree

theorem exists_actualPoolStage_YZ
    {PX PY PZ AX AY AZ : Type*} [Fintype AX] [Fintype AY] [Fintype AZ]
    {support : X → Y → Z → Prop}
    (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
    (priorWord : Prefix → ExactPrefix counts labels n t Position)
    (readY : Prefix → Y → Position → Label n)
    (readZ : Prefix → Z → Position → Label n)
    (eligible : Prefix → X → Y → Z → Prop)
    (previous : ∀ x y z, support x.1 y.1 z.1 → E.value x y z ≠ 0 →
      eligible x.2.1 x.1 y.1 z.1)
    (agree : ∀ p x y z, eligible p x y z → readY p y = readZ p z) :
    ∃ S : Stage E (Fin (stageRefinementCount counts labels n t)) PUnit
        (Fin (stageRefinementCount counts labels n t))
        (Fin (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t))
        (PoolAuxiliaryGroup (stageRefinementCount counts labels n t)),
      S.auxiliary = auxiliaryYZ (stageRefinementCount counts labels n t) ∧
      S.rankBound = stageCost counts labels n t ∧ S.order = 0 ∧
      S.leftDegree = 0 ∧ S.middleDegree = 0 ∧ S.rightDegree = 0 ∧
      S.value = rawPoolLeadingYZ (actualPool counts labels n t priorWord)
        (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
        (actualPool_card counts labels n t priorWord) readY readZ := by
  exact exists_rawPoolStage_YZ E (actualPool counts labels n t priorWord)
    (stageRefinementCount counts labels n t) (stageRefinementCount_pos counts labels n t)
    (actualPool_card counts labels n t priorWord) readY readZ eligible previous agree

end ExactConditionalPools
end MatrixMultiplication.Foundation.OrientedConditionalHierarchyStage

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialExecutionReindex
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.InitialTargetExecution.initial_order _root_.OAI.MatrixMultiplication.Foundation.InitialTargetExecution.initial_rankBound _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution

open _root_.OAI.MatrixMultiplication.Foundation.Tensor LocalMaps PolynomialLocalConstruction

variable {X Y Z Prefix PX PY PZ AX AY AZ Prefix' PX' PY' PZ' : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)
variable (ePrefix : Prefix' ≃ Prefix) (eX : PX' ≃ PX) (eY : PY' ≃ PY) (eZ : PZ' ≃ PZ)

def reindexOutput : Execution X Y Z Prefix' PX' PY' PZ' AX AY AZ support where
  auxiliary := E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank
  order := E.order
  leftDegree := E.leftDegree
  middleDegree := E.middleDegree
  rightDegree := E.rightDegree
  leftMap := fun x output input => E.leftMap x (ePrefix output.1, eX output.2) input
  middleMap := fun y output input => E.middleMap y (ePrefix output.1, eY output.2) input
  rightMap := fun z output input => E.rightMap z (ePrefix output.1, eZ output.2) input
  left_degree := fun x output input =>
    E.left_degree x (ePrefix output.1, eX output.2) input
  middle_degree := fun y output input =>
    E.middle_degree y (ePrefix output.1, eY output.2) input
  right_degree := fun z output input =>
    E.right_degree z (ePrefix output.1, eZ output.2) input
  value := fun x y z => E.value
    (x.1, (ePrefix x.2.1, eX x.2.2))
    (y.1, (ePrefix y.2.1, eY y.2.2))
    (z.1, (ePrefix z.2.1, eZ z.2.2))
  vanishes := fun x y z hs j hj => E.vanishes
    (x.1, (ePrefix x.2.1, eX x.2.2))
    (y.1, (ePrefix y.2.1, eY y.2.2))
    (z.1, (ePrefix z.2.1, eZ z.2.2)) hs j hj
  leading := fun x y z hs => E.leading
    (x.1, (ePrefix x.2.1, eX x.2.2))
    (y.1, (ePrefix y.2.1, eY y.2.2))
    (z.1, (ePrefix z.2.1, eZ z.2.2)) hs
  synchronized := by
    intro x y z hs hn
    have h := E.synchronized
      (x.1, (ePrefix x.2.1, eX x.2.2))
      (y.1, (ePrefix y.2.1, eY y.2.2))
      (z.1, (ePrefix z.2.1, eZ z.2.2)) hs hn
    exact ⟨ePrefix.injective h.1, ePrefix.injective h.2⟩

@[simp] theorem reindexOutput_auxiliary :
    (E.reindexOutput ePrefix eX eY eZ).auxiliary = E.auxiliary := rfl

@[simp] theorem reindexOutput_rankBound :
    (E.reindexOutput ePrefix eX eY eZ).rankBound = E.rankBound := rfl

@[simp] theorem reindexOutput_order :
    (E.reindexOutput ePrefix eX eY eZ).order = E.order := rfl

@[simp] theorem reindexOutput_leftDegree :
    (E.reindexOutput ePrefix eX eY eZ).leftDegree = E.leftDegree := rfl

@[simp] theorem reindexOutput_middleDegree :
    (E.reindexOutput ePrefix eX eY eZ).middleDegree = E.middleDegree := rfl

@[simp] theorem reindexOutput_rightDegree :
    (E.reindexOutput ePrefix eX eY eZ).rightDegree = E.rightDegree := rfl

@[simp] theorem reindexOutput_leftMap (x : X) (output : Prefix' × PX') (input : AX) :
    (E.reindexOutput ePrefix eX eY eZ).leftMap x output input =
      E.leftMap x (ePrefix output.1, eX output.2) input := rfl

@[simp] theorem reindexOutput_middleMap (y : Y) (output : Prefix' × PY') (input : AY) :
    (E.reindexOutput ePrefix eX eY eZ).middleMap y output input =
      E.middleMap y (ePrefix output.1, eY output.2) input := rfl

@[simp] theorem reindexOutput_rightMap (z : Z) (output : Prefix' × PZ') (input : AZ) :
    (E.reindexOutput ePrefix eX eY eZ).rightMap z output input =
      E.rightMap z (ePrefix output.1, eZ output.2) input := rfl

@[simp] theorem reindexOutput_value
    (x : X × (Prefix' × PX')) (y : Y × (Prefix' × PY')) (z : Z × (Prefix' × PZ')) :
    (E.reindexOutput ePrefix eX eY eZ).value x y z = E.value
      (x.1, (ePrefix x.2.1, eX x.2.2))
      (y.1, (ePrefix y.2.1, eY y.2.2))
      (z.1, (ePrefix z.2.1, eZ z.2.2)) := rfl

@[simp] theorem reindexOutput_kernel
    (x : X × (Prefix' × PX')) (y : Y × (Prefix' × PY')) (z : Z × (Prefix' × PZ')) :
    kernel (E.reindexOutput ePrefix eX eY eZ).auxiliary
        (E.reindexOutput ePrefix eX eY eZ).leftMap
        (E.reindexOutput ePrefix eX eY eZ).middleMap
        (E.reindexOutput ePrefix eX eY eZ).rightMap x y z =
      kernel E.auxiliary E.leftMap E.middleMap E.rightMap
        (x.1, (ePrefix x.2.1, eX x.2.2))
        (y.1, (ePrefix y.2.1, eY y.2.2))
        (z.1, (ePrefix z.2.1, eZ z.2.2)) := rfl

end MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedExecution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedExecution

open MatrixMultiplication.Foundation
open CW75LabelHierarchy CW75ReorderedWords ConditionalPrefixWords ComplexWitness
open PolynomialKernelExecution ExecutionPairingBudget StageHierarchyResources
open scoped BigOperators Classical

attribute [local irreducible] CW75LabelHierarchy.retainedWords

abbrev Position (counts : Scalar → ℕ) (t : ℕ) := BlockPosition counts t
abbrev Coordinate (counts : Scalar → ℕ) (t : ℕ) := LongWord (Position counts t)
abbrev Prefix (counts : Scalar → ℕ) (t n : ℕ) :=
  ExactPrefix counts curveLabels n t (Position counts t)

def readerPair : ℕ → ReaderPair
  | 1 => .xz
  | 3 | 4 => .yz
  | _ => .xy

def pairingProduct (counts : Scalar → ℕ) (t : ℕ) (pair : ReaderPair) (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if readerPair i = pair then
    stageRefinementCount counts curveLabels i t else 1

@[simp] theorem pairingProduct_zero (counts : Scalar → ℕ) (t : ℕ) (pair : ReaderPair) :
    pairingProduct counts t pair 0 = 1 := by simp [pairingProduct]

theorem pairingProduct_succ (counts : Scalar → ℕ) (t : ℕ) (pair : ReaderPair) (n : ℕ) :
    pairingProduct counts t pair (n + 1) = pairingProduct counts t pair n *
      (if readerPair n = pair then stageRefinementCount counts curveLabels n t else 1) := by
  simp only [pairingProduct, Finset.prod_range_succ]

def prefixValue {PX PY PZ : Type*} (counts : Scalar → ℕ) (t n : ℕ)
    (pairing : Tensor ℂ PX PY PZ) :
    Tensor ℂ (Coordinate counts t × (Prefix counts t n × PX))
      (Coordinate counts t × (Prefix counts t n × PY))
      (Coordinate counts t × (Prefix counts t n × PZ)) :=
  fun x y z => if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
      eligible id x.2.1 x.1 y.1 z.1 then pairing x.2.2 y.2.2 z.2.2 else 0

structure Bundle (counts : Scalar → ℕ) (t n : ℕ) where
  PX : Type
  PY : Type
  PZ : Type
  AX : Type
  AY : Type
  AZ : Type
  [finitePX : Fintype PX]
  [finitePY : Fintype PY]
  [finitePZ : Fintype PZ]
  [finiteAX : Fintype AX]
  [finiteAY : Fintype AY]
  [finiteAZ : Fintype AZ]
  execution : Execution (Coordinate counts t) (Coordinate counts t) (Coordinate counts t)
    (Prefix counts t n) PX PY PZ AX AY AZ
      (CW75InitialExecution.support (N := t * ∑ a, counts a))
  shape : MatrixCoordinates PX PY PZ
  shape_positive : shape.Positive
  normal : execution.value = prefixValue counts t n shape.tensor
  rank_exact : execution.rankBound = stageAuxiliaryBudget counts curveLabels n t
  volume_exact : shape.volume = stagePairingProduct counts curveLabels n t
  rows_exact : shape.rows = pairingProduct counts t .xz n
  inner_exact : shape.inner = pairingProduct counts t .xy n
  columns_exact : shape.columns = pairingProduct counts t .yz n
  pairing_budget : shape.volume ≤ execution.rankBound

attribute [instance] Bundle.finitePX Bundle.finitePY Bundle.finitePZ
attribute [instance] Bundle.finiteAX Bundle.finiteAY Bundle.finiteAZ

theorem position_card (counts : Scalar → ℕ) (t : ℕ) :
    Fintype.card (Position counts t) = ∑ a, t * counts a := by
  simp [Position, BlockPosition, Finset.mul_sum]

theorem previous_eligible {counts : Scalar → ℕ} {t n : ℕ} (B : Bundle counts t n)
    (x : Coordinate counts t × (Prefix counts t n × B.PX))
    (y : Coordinate counts t × (Prefix counts t n × B.PY))
    (z : Coordinate counts t × (Prefix counts t n × B.PZ))
    (_hs : CW75InitialExecution.support (N := t * ∑ a, counts a) x.1 y.1 z.1)
    (hn : B.execution.value x y z ≠ 0) : eligible id x.2.1 x.1 y.1 z.1 := by
  rw [B.normal] at hn
  by_contra h
  exact hn (by simp [prefixValue, h])

section Successor

variable {counts : Scalar → ℕ} {t n : ℕ} (B : Bundle counts t n)
variable {NX NY NZ BX BY BZ : Type}
variable [Fintype BX] [Fintype BY] [Fintype BZ]

def refinedExecution
    (S : Stage B.execution (Fin (stageRefinementCount counts curveLabels n t))
      NX NY NZ BX BY BZ) :
    Execution (Coordinate counts t) (Coordinate counts t) (Coordinate counts t)
      (Prefix counts t (n + 1)) (B.PX × NX) (B.PY × NY) (B.PZ × NZ)
      (B.AX × BX) (B.AY × BY) (B.AZ × BZ)
      (CW75InitialExecution.support (N := t * ∑ a, counts a)) :=
  (B.execution.step S).reindexOutput
    (nextPrefixEquiv counts curveLabels n t (Position counts t))
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

theorem refinedExecution_normal
    (S : Stage B.execution (Fin (stageRefinementCount counts curveLabels n t))
      NX NY NZ BX BY BZ)
    (shape : MatrixCoordinates NX NY NZ)
    (hstage : ∀ p x y z, eligible id p x.1 y.1 z.1 →
      S.value p x y z = if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode p x.2.1) x.1 y.1 z.1
        then shape.tensor x.2.2 y.2.2 z.2.2 else 0) :
    (refinedExecution B S).value =
      prefixValue counts t (n + 1) (B.shape.product shape).tensor := by
  classical
  funext x y z
  let e := nextPrefixEquiv counts curveLabels n t (Position counts t)
  let px := e x.2.1
  let py := e y.2.1
  let pz := e z.2.1
  have hdecode (p : Prefix counts t (n + 1)) :
      appendCode (e p).1 (e p).2 = p := e.symm_apply_apply p
  change B.execution.value (x.1, (px.1, x.2.2.1))
      (y.1, (py.1, y.2.2.1)) (z.1, (pz.1, z.2.2.1)) *
    S.value px.1 (x.1, (px.2, x.2.2.2))
      (y.1, (py.2, y.2.2.2)) (z.1, (pz.2, z.2.2.2)) = _
  rw [B.normal]
  simp only [prefixValue]
  by_cases hold : px.1 = py.1 ∧ px.1 = pz.1 ∧ eligible id px.1 x.1 y.1 z.1
  · rw [ite_eq_left hold]
    have hguard :
        (px.2 = py.2 ∧ px.2 = pz.2 ∧ eligible id (appendCode px.1 px.2) x.1 y.1 z.1) ↔
        (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ eligible id x.2.1 x.1 y.1 z.1) := by
      constructor
      · rintro ⟨hxy, hxz, he⟩
        refine ⟨e.injective (Prod.ext hold.1 hxy),
          e.injective (Prod.ext hold.2.1 hxz), ?_⟩
        simpa only [px, hdecode] using he
      · rintro ⟨hxy, hxz, he⟩
        refine ⟨congrArg (fun p => (e p).2) hxy,
          congrArg (fun p => (e p).2) hxz, ?_⟩
        simpa only [px, hdecode] using he
    rw [hstage px.1 (x.1, (px.2, x.2.2.2))
      (y.1, (py.2, y.2.2.2)) (z.1, (pz.2, z.2.2.2)) hold.2.2]
    simp only [hguard,
      MatrixCoordinates.product_tensor, Tensor.product, mul_ite, mul_zero]
  · have hnext : ¬ (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible id x.2.1 x.1 y.1 z.1) := by
      rintro ⟨hxy, hxz, he⟩
      apply hold
      refine ⟨congrArg (fun p => (e p).1) hxy,
        congrArg (fun p => (e p).1) hxz, ?_⟩
      rw [← hdecode x.2.1] at he
      obtain ⟨word, hw, _⟩ :=
        (eligible_appendCode_iff px.1 px.2 x.1 y.1 z.1).mp he
      exact ⟨word, hw⟩
    rw [ite_eq_right hold, ite_eq_right hnext, zero_mul]

def extendBundle [Fintype NX] [Fintype NY] [Fintype NZ]
    (S : Stage B.execution (Fin (stageRefinementCount counts curveLabels n t))
      NX NY NZ BX BY BZ)
    (shape : MatrixCoordinates NX NY NZ) (hpositive : shape.Positive)
    (hvolume : shape.volume = stageRefinementCount counts curveLabels n t)
    (hrank : S.rankBound = stageCost counts curveLabels n t)
    (hrows : shape.rows = if readerPair n = .xz then
      stageRefinementCount counts curveLabels n t else 1)
    (hinner : shape.inner = if readerPair n = .xy then
      stageRefinementCount counts curveLabels n t else 1)
    (hcolumns : shape.columns = if readerPair n = .yz then
      stageRefinementCount counts curveLabels n t else 1)
    (hstage : ∀ p x y z, eligible id p x.1 y.1 z.1 →
      S.value p x y z = if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible id (appendCode p x.2.1) x.1 y.1 z.1
        then shape.tensor x.2.2 y.2.2 z.2.2 else 0) : Bundle counts t (n + 1) where
  PX := B.PX × NX
  PY := B.PY × NY
  PZ := B.PZ × NZ
  AX := B.AX × BX
  AY := B.AY × BY
  AZ := B.AZ × BZ
  execution := refinedExecution B S
  shape := B.shape.product shape
  shape_positive := B.shape.product_positive shape B.shape_positive hpositive
  normal := refinedExecution_normal B S shape hstage
  rank_exact := by
    simp only [refinedExecution, Execution.reindexOutput_rankBound,
      Execution.step_rankBound, B.rank_exact, hrank, stageAuxiliaryBudget_succ]
  volume_exact := by
    rw [MatrixCoordinates.product_volume, B.volume_exact, hvolume, stagePairingProduct_succ]
  rows_exact := by
    change B.shape.rows * shape.rows = _
    rw [B.rows_exact, hrows, pairingProduct_succ]
  inner_exact := by
    change B.shape.inner * shape.inner = _
    rw [B.inner_exact, hinner, pairingProduct_succ]
  columns_exact := by
    change B.shape.columns * shape.columns = _
    rw [B.columns_exact, hcolumns, pairingProduct_succ]
  pairing_budget := by
    change (B.shape.product shape).volume ≤ B.execution.rankBound * S.rankBound
    rw [MatrixCoordinates.product_volume]
    apply Nat.mul_le_mul B.pairing_budget
    rw [hvolume, hrank]
    exact LabelHierarchySeparation.population_le_poolAuxiliaryCost _

end Successor

section ConcreteStages

variable {counts : Scalar → ℕ} {t n : ℕ}

def extendXY (B : Bundle counts t n) (hn : n < 5)
    (hfirst : curveFirstSide n = .x) (hsecond : curveSecondSide n = .y) :
    Bundle counts t (n + 1) := Classical.choice (by
  have hpair : readerPair n = .xy := by
    interval_cases n <;> simp_all [curveFirstSide, curveSecondSide, readerPair]
  have hagree : ∀ (p : Prefix counts t n) (x y z : Coordinate counts t), eligible id p x y z →
      firstRead id p x = secondRead id p y := by
    intro p x y z he
    simpa only [hfirst, hsecond, coordinateOf] using
      readable_of_eligible id p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    ConditionalHierarchyStage.exists_actualPoolStage counts curveLabels n t B.execution id
      (firstRead id) (secondRead id) (eligible id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.xy _)
    (GeometricStageCoordinates.xy_positive (stageRefinementCount_pos counts curveLabels n t))
    (GeometricStageCoordinates.xy_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.xy])
    (by simp [hpair, GeometricStageCoordinates.xy])
    (by simp [hpair, GeometricStageCoordinates.xy]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CW75ReorderedGeometricValues.raw_XY_normal p hn hfirst hsecond x y z word hw)

def extendXZ (B : Bundle counts t n) (hn : n < 5)
    (hfirst : curveFirstSide n = .x) (hsecond : curveSecondSide n = .z) :
    Bundle counts t (n + 1) := Classical.choice (by
  have hpair : readerPair n = .xz := by
    interval_cases n <;> simp_all [curveFirstSide, curveSecondSide, readerPair]
  have hagree : ∀ (p : Prefix counts t n) (x y z : Coordinate counts t), eligible id p x y z →
      firstRead id p x = secondRead id p z := by
    intro p x y z he
    simpa only [hfirst, hsecond, coordinateOf] using
      readable_of_eligible id p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    OrientedConditionalHierarchyStage.exists_actualPoolStage_XZ counts curveLabels n t B.execution id
      (firstRead id) (secondRead id) (eligible id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.xz _)
    (GeometricStageCoordinates.xz_positive (stageRefinementCount_pos counts curveLabels n t))
    (GeometricStageCoordinates.xz_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.xz])
    (by simp [hpair, GeometricStageCoordinates.xz])
    (by simp [hpair, GeometricStageCoordinates.xz]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CW75ReorderedGeometricValues.raw_XZ_normal p hn hfirst hsecond x y z word hw)

def extendYZ (B : Bundle counts t n) (hn : n < 5)
    (hfirst : curveFirstSide n = .y) (hsecond : curveSecondSide n = .z) :
    Bundle counts t (n + 1) := Classical.choice (by
  have hpair : readerPair n = .yz := by
    interval_cases n <;> simp_all [curveFirstSide, curveSecondSide, readerPair]
  have hagree : ∀ (p : Prefix counts t n) (x y z : Coordinate counts t), eligible id p x y z →
      firstRead id p y = secondRead id p z := by
    intro p x y z he
    simpa only [hfirst, hsecond, coordinateOf] using
      readable_of_eligible id p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    OrientedConditionalHierarchyStage.exists_actualPoolStage_YZ counts curveLabels n t B.execution id
      (firstRead id) (secondRead id) (eligible id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.yz _)
    (GeometricStageCoordinates.yz_positive (stageRefinementCount_pos counts curveLabels n t))
    (GeometricStageCoordinates.yz_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.yz])
    (by simp [hpair, GeometricStageCoordinates.yz])
    (by simp [hpair, GeometricStageCoordinates.yz]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CW75ReorderedGeometricValues.raw_YZ_normal p hn hfirst hsecond x y z word hw)

end ConcreteStages

end MatrixMultiplication.CW75ReorderedExecution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_BaseTensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation
open scoped BigOperators Classical

namespace BaseTwo

def tensor : Tensor ℂ (Fin 2) (Fin 2) (Fin 2) :=
  fun x y z => if x.val + y.val + z.val = 1 then 1 else 0

def flagB (x : Fin 2) : Prop := x = 1
def flagA (z : Fin 2) : Prop := z = 1
def flagC (y : Fin 2) : Prop := y = 1

theorem one_hot (x y z : Fin 2) (hs : tensor x y z ≠ 0) :
    (if flagB x then 1 else 0) + (if flagA z then 1 else 0) +
      (if flagC y then 1 else 0) = (1 : ℕ) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB, flagA, flagC] at hs <;>
      (first | (simp [Fin.ext_iff, Prod.mk.injEq, tensor, flagB, flagA, flagC]; all_goals first | (norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB, flagA, flagC]; done) | rfl | decide) | (norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB, flagA, flagC]; done) | norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB, flagA, flagC])

theorem conditionalB (x y z : Fin 2) :
    tensor x y z ≠ 0 ∧ flagB x ↔ x = 1 ∧ y = 0 ∧ z = 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> (first | (simp [Fin.ext_iff, Prod.mk.injEq, tensor, flagB]; all_goals first | (norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB]; done) | rfl | decide) | (norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB]; done) | norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagB])

theorem conditionalA (x y z : Fin 2) :
    tensor x y z ≠ 0 ∧ flagA z ↔ x = 0 ∧ y = 0 ∧ z = 1 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> (first | (simp [Fin.ext_iff, Prod.mk.injEq, tensor, flagA]; all_goals first | (norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagA]; done) | rfl | decide) | (norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagA]; done) | norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagA])

theorem conditionalC (x y z : Fin 2) :
    tensor x y z ≠ 0 ∧ flagC y ↔ x = 0 ∧ y = 1 ∧ z = 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> (first | (simp [Fin.ext_iff, Prod.mk.injEq, tensor, flagC]; all_goals first | (norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagC]; done) | rfl | decide) | (norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagC]; done) | norm_num [Fin.ext_iff, Prod.mk.injEq, tensor, flagC])

end BaseTwo

end MatrixMultiplication

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_BaseTensorBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication

open MatrixMultiplication.Foundation Polynomial
open scoped BigOperators Classical

namespace BaseTwo

def first (i x : Fin 2) : Polynomial ℂ :=
  if i = 0 then X ^ x.val else if x = 0 then -1 else 0

def other (i x : Fin 2) : Polynomial ℂ :=
  if i = 0 then X ^ x.val else if x = 0 then 1 else 0

def polynomial : Tensor (Polynomial ℂ) (Fin 2) (Fin 2) (Fin 2) :=
  fun x y z => ∑ i, Tensor.rankOne (first i) (other i) (other i) x y z

theorem polynomial_rank : Tensor.RankAtMost polynomial 2 :=
  ⟨first, other, other, rfl⟩

theorem polynomial_difference (x y z : Fin 2) :
    polynomial x y z =
      X ^ x.val * X ^ y.val * X ^ z.val -
        (if x = 0 then 1 else 0) * (if y = 0 then 1 else 0) *
          (if z = 0 then 1 else 0) := by
  simp only [polynomial, Fin.sum_univ_two]
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    (first | (simp [Fin.ext_iff, first, other, Tensor.rankOne]; all_goals first | (norm_num [Fin.ext_iff, first, other, Tensor.rankOne]; done) | rfl | decide) | (norm_num [Fin.ext_iff, first, other, Tensor.rankOne]; done) | norm_num [Fin.ext_iff, first, other, Tensor.rankOne])

theorem polynomial_apply (x y z : Fin 2) :
    polynomial x y z =
      if x.val + y.val + z.val = 0 then 0 else X ^ (x.val + y.val + z.val) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    norm_num [Fin.ext_iff, polynomial_difference] <;> ring

theorem polynomial_leading (x y z : Fin 2) :
    (polynomial x y z).coeff 1 = tensor x y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    (first | (simp [Fin.ext_iff, polynomial_apply, tensor]; all_goals first | (norm_num [Fin.ext_iff, polynomial_apply, tensor]; done) | rfl | decide) | (norm_num [Fin.ext_iff, polynomial_apply, tensor]; done) | norm_num [Fin.ext_iff, polynomial_apply, tensor])

theorem polynomial_vanishes (x y z : Fin 2) (k : ℕ) (hk : k < 1) :
    (polynomial x y z).coeff k = 0 := by
  have hk0 : k = 0 := by omega
  subst k
  fin_cases x <;> fin_cases y <;> fin_cases z <;> (first | (simp [Fin.ext_iff, polynomial_apply]; all_goals first | (norm_num [Fin.ext_iff, polynomial_apply]; done) | rfl | decide) | (norm_num [Fin.ext_iff, polynomial_apply]; done) | norm_num [Fin.ext_iff, polynomial_apply])

theorem polynomial_degree (x y z : Fin 2) :
    (polynomial x y z).degree ≤ 3 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> (first | (simp [Fin.ext_iff, polynomial_apply]; all_goals first | (norm_num [Fin.ext_iff, polynomial_apply]; done) | rfl | decide) | (norm_num [Fin.ext_iff, polynomial_apply]; done) | norm_num [Fin.ext_iff, polynomial_apply])

def approximation : Tensor.PolynomialApproximation tensor 2 1 3 where
  polynomial := polynomial
  rank_bound := polynomial_rank
  vanishes := polynomial_vanishes
  leading := polynomial_leading
  degree_bound := polynomial_degree

def flagged : FlaggedTensor (Fin 2) (Fin 2) (Fin 2) where
  tensor := tensor
  flagB := flagB
  flagA := flagA
  flagC := flagC
  one_hot := one_hot

end BaseTwo

end MatrixMultiplication

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_BaseConditionalReaders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.BaseConditionalReaders

open MatrixMultiplication.Foundation CompletionLabels CompletionLabels.TopologicalFlatten
open scoped Classical

universe u

variable {X Y Z : Type u}

def ConditionalLeaf (S : FlaggedTensor X Y Z) (c : Color) :=
  {a : Leaf S // CompletionLabels.leafColor S a = c}

theorem conditional_flag (S : FlaggedTensor X Y Z) (c : Color)
    (a : ConditionalLeaf S c) : ownerFlag S c (coordinate a.val.val c) :=
  (leafColor_eq_iff S a.val c).mp a.property

theorem baseTwo_subsingleton (c : Color) :
    Subsingleton (ConditionalLeaf BaseTwo.flagged c) := by
  refine ⟨?_⟩
  intro a b
  have ha := conditional_flag BaseTwo.flagged c a
  have hb := conditional_flag BaseTwo.flagged c b
  have hsa := a.val.property
  have hsb := b.val.property
  apply Subtype.ext
  apply Subtype.ext
  cases c with
  | B =>
      obtain ⟨hax, hay, haz⟩ := (BaseTwo.conditionalB _ _ _).mp ⟨hsa, ha⟩
      obtain ⟨hbx, hby, hbz⟩ := (BaseTwo.conditionalB _ _ _).mp ⟨hsb, hb⟩
      exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))
  | A =>
      obtain ⟨hax, hay, haz⟩ := (BaseTwo.conditionalA _ _ _).mp ⟨hsa, ha⟩
      obtain ⟨hbx, hby, hbz⟩ := (BaseTwo.conditionalA _ _ _).mp ⟨hsb, hb⟩
      exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))
  | C =>
      obtain ⟨hax, hay, haz⟩ := (BaseTwo.conditionalC _ _ _).mp ⟨hsa, ha⟩
      obtain ⟨hbx, hby, hbz⟩ := (BaseTwo.conditionalC _ _ _).mp ⟨hsb, hb⟩
      exact Prod.ext (hax.trans hbx.symm) (Prod.ext (hay.trans hby.symm) (haz.trans hbz.symm))

def baseTwoProgram :
    Program (Leaf BaseTwo.flagged) (Coordinate (Fin 2) (Fin 2) (Fin 2))
      Color (Fin 2) 0 where
  context := CompletionLabels.leafColor BaseTwo.flagged
  view := fun side a => coordinate a.val side
  pair := fun _ => .xy
  labels := fun _ _ => 0
  read := fun _ _ _ _ _ => 0
  readable := by intro n hn; omega

theorem baseTwoProgram_complete : baseTwoProgram.Complete := by
  intro a b hc _
  change CompletionLabels.leafColor BaseTwo.flagged a =
    CompletionLabels.leafColor BaseTwo.flagged b at hc
  let aa : ConditionalLeaf BaseTwo.flagged (CompletionLabels.leafColor BaseTwo.flagged a) :=
    ⟨a, rfl⟩
  let bb : ConditionalLeaf BaseTwo.flagged (CompletionLabels.leafColor BaseTwo.flagged a) :=
    ⟨b, hc.symm⟩
  exact congrArg Subtype.val ((baseTwo_subsingleton _).allEq aa bb)

def baseTwoReadable : ReadableTensor BaseTwo.flagged where
  Code := Fin 2
  depth := 0
  program := baseTwoProgram
  context_eq _ := rfl
  view_eq _ _ := rfl
  complete := baseTwoProgram_complete

end MatrixMultiplication.BaseConditionalReaders

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Rectangular_Growth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rectangular matrix multiplication algorithms and their asymptotic exponents. -/

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

end OAI
end


