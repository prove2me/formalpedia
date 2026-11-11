-- Prove2me | Definitions.Def_Q235MM002
-- name    : Q235MM002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:26:57.067316+00:00
-- url     : https://prove2.me/theorems/0f9fe1b8-89dd-4cea-bd63-55dd85fbdf2d
-- title:
--   Definitions bundle Q235MM002 of the split of OpenAI, Complex Matrix Multiplication Below 2.258 and Rectangular Bounds
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MatrixMultiplication.complex_alpha_gt_93_div_200` and `OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250`, carved from OpenAI's openai/math development (OpenAI, *Complex Matrix Multiplication Below 2.258 and Rectangular Bounds*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 535 declarations of OpenAI's Lean: 229 definitions, 8 inductive types or structures, 5 instances and 293 theorems. The definitions and types are `OAI.MatrixMultiplication.CW75ReorderedBalanced.witness`, `OAI.MatrixMultiplication.CW75ReorderedExecution.initial`, `OAI.MatrixMultiplication.CW75ReorderedExecution.realize`, `OAI.MatrixMultiplication.CW75ReorderedFinite.approximation`, `OAI.MatrixMultiplication.CW75ReorderedFinite.blocks`, `OAI.MatrixMultiplication.CW75ReorderedFinite.columns`, `OAI.MatrixMultiplication.CW75ReorderedFinite.copies`, `OAI.MatrixMultiplication.CW75ReorderedFinite.degree`, `OAI.MatrixMultiplication.CW75ReorderedFinite.designatedX`, `OAI.MatrixMultiplication.CW75ReorderedFinite.designatedY`, `OAI.MatrixMultiplication.CW75ReorderedFinite.designatedZ`, `OAI.MatrixMultiplication.CW75ReorderedFinite.inner`, `OAI.MatrixMultiplication.CW75ReorderedFinite.labelEquiv`, `OAI.MatrixMultiplication.CW75ReorderedFinite.leftSelect`, `OAI.MatrixMultiplication.CW75ReorderedFinite.middleSelect`, `OAI.MatrixMultiplication.CW75ReorderedFinite.order`, `OAI.MatrixMultiplication.CW75ReorderedFinite.rankBudget`, `OAI.MatrixMultiplication.CW75ReorderedFinite.rightSelect`, `OAI.MatrixMultiplication.CW75ReorderedFinite.rows`, `OAI.MatrixMultiplication.CW75ReorderedFinite.sourceApproximation`, `OAI.MatrixMultiplication.CW75ReorderedWords.terminalWord`, `OAI.MatrixMultiplication.CompletionColorLaws.ColorSlice`, `OAI.MatrixMultiplication.CompletionColorLaws.centerCompletionEquiv`, `OAI.MatrixMultiplication.CompletionColorLaws.centerCompletionLaw`, `OAI.MatrixMultiplication.CompletionColorLaws.centerWordEquiv`, `OAI.MatrixMultiplication.CompletionColorLaws.colorMix`, `OAI.MatrixMultiplication.CompletionColorLaws.completionEvent`, `OAI.MatrixMultiplication.CompletionColorLaws.conditionalCompletionLaw`, `OAI.MatrixMultiplication.CompletionColorLaws.iidColorLaw`, `OAI.MatrixMultiplication.CompletionExecution.Bundle`, `OAI.MatrixMultiplication.CompletionExecution.Prefix`, `OAI.MatrixMultiplication.CompletionExecution.extend`, `OAI.MatrixMultiplication.CompletionExecution.extendBundle`, `OAI.MatrixMultiplication.CompletionExecution.extendXY`, `OAI.MatrixMultiplication.CompletionExecution.extendXZ`, `OAI.MatrixMultiplication.CompletionExecution.extendYZ`, `OAI.MatrixMultiplication.CompletionExecution.initial`, `OAI.MatrixMultiplication.CompletionExecution.pairingProduct`, `OAI.MatrixMultiplication.CompletionExecution.prefixValue`, `OAI.MatrixMultiplication.CompletionExecution.realize` and 197 more.
--
--   **Sources.** They come from these modules of lean/OAI/LinearAlgebra, in whole or in part: `MatrixMultiplication_Completion_CenterLaw`, `MatrixMultiplication_Completion_ColorLaws`, `MatrixMultiplication_Completion_Conditioning`, `MatrixMultiplication_Completion_Execution`, `MatrixMultiplication_Completion_FiniteRealization`, `MatrixMultiplication_Completion_GeometricValues`, `MatrixMultiplication_Completion_HierarchyPrograms`, `MatrixMultiplication_Completion_HierarchyWords`, `MatrixMultiplication_Completion_Labels`, `MatrixMultiplication_Completion_Partitions`, `MatrixMultiplication_Completion_ProductLaws`, `MatrixMultiplication_Completion_RecursiveCompletion`, `MatrixMultiplication_Completion_Scripts`, `MatrixMultiplication_Completion_Termination`, `MatrixMultiplication_Completion_TerminationLaw`, `MatrixMultiplication_ComplexArithmetic_Complexity`, `MatrixMultiplication_ComplexBounds_CW75ReorderedBalanced`, `MatrixMultiplication_ComplexBounds_CW75ReorderedExecution`, `MatrixMultiplication_ComplexBounds_CW75ReorderedFinite`, `MatrixMultiplication_ComplexBounds_CW75ReorderedWords`, `MatrixMultiplication_CoppersmithWinograd_ComplexCW75LabelHierarchy`, `MatrixMultiplication_CoppersmithWinograd_ComplexCW75Primitive`, `MatrixMultiplication_Duality_CompletionIndependence`, `MatrixMultiplication_Duality_CompletionLaws`, `MatrixMultiplication_Duality_ExponentConsumer`, `MatrixMultiplication_Duality_FamilyConstruction`, `MatrixMultiplication_Duality_FiniteRates`, `MatrixMultiplication_Duality_FiniteRealization`, `MatrixMultiplication_Duality_HiddenRates`, `MatrixMultiplication_Duality_Information`, `MatrixMultiplication_Duality_LawEntropy`, `MatrixMultiplication_Duality_ProgramIndependence`, `MatrixMultiplication_Duality_ScriptIndependence`, `MatrixMultiplication_Duality_Uniform`, `MatrixMultiplication_Duality_UniformInstances`, `MatrixMultiplication_Duality_Witness`, `MatrixMultiplication_Duality_WitnessProgram`, `MatrixMultiplication_Duality_WitnessRealization`, `MatrixMultiplication_Entropy_ComplexConditionalPrefixWords`, `MatrixMultiplication_Entropy_ComplexEntropyContinuity`, `MatrixMultiplication_Entropy_ComplexFiniteEntropy`, `MatrixMultiplication_Entropy_ComplexHierarchyEntropy`, `MatrixMultiplication_Entropy_ComplexHierarchySeparationRates`, `MatrixMultiplication_Entropy_ComplexSeparationAsymptotics`, `MatrixMultiplication_Entropy_ComplexTypeEntropy`, `MatrixMultiplication_Entropy_ConditionalLabels`, `MatrixMultiplication_Entropy_ConditionalRateBridge`, `MatrixMultiplication_Entropy_CurveLaws`, `MatrixMultiplication_Polynomial_ComplexPolynomialApproximation`, `MatrixMultiplication_Polynomial_ComplexPolynomialExecutionSymmetry`, `MatrixMultiplication_Polynomial_ComplexPolynomialWitnessProduct`, `MatrixMultiplication_Separation_ComplexFiniteMMRealization`, `MatrixMultiplication_Separation_ComplexHierarchyTypeCounting`, `MatrixMultiplication_Separation_ComplexRationalTypes`, `MatrixMultiplication_Separation_ComplexStageHierarchyResources`, `MatrixMultiplication_Separation_ExecutionApproximation`, `MatrixMultiplication_Tensor_ComplexExecutionPairingBudget`, `MatrixMultiplication_Tensor_ComplexLocalMaps`, `MatrixMultiplication_Tensor_ComplexMatrixTensor`, `MatrixMultiplication_Tensor_ComplexTensor`, `MatrixMultiplication_Tensor_ComplexTensorBatching`, `MatrixMultiplication_Tensor_ComplexTensorSymmetrization`, `MatrixMultiplication_Tensor_ComplexWitness`, `MatrixMultiplication_Tensor_MatrixBalancing`, `MatrixMultiplication_Tensor_UniformCoordinate`.
--
--   **Imports.** It imports the bundles `Q235MM000` and `Q235MM001` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.MatrixMultiplication.complex_alpha_gt_93_div_200` and `OAI.MatrixMultiplication.complex_rectangular_omega_lt_523_div_250`.
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
import Definitions.Def_Q235MM000
import Definitions.Def_Q235MM001

section
-- module Solutions.Q235_MM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
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
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexFiniteEntropy
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.Foundation

open scoped BigOperators

namespace FiniteLaw

variable {A B : Type*} [Fintype A] [Fintype B]

theorem map_mass_apply (p : FiniteLaw A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f).mass (f a) = p.mass a := by
  classical
  simp [map_mass, hf.eq_iff]

theorem joint_entropy (p : FiniteLaw A) (q : A → FiniteLaw B) :
    finiteEntropy (p.joint q).mass =
      finiteEntropy p.mass + ∑ a, p.mass a * finiteEntropy (q a).mass :=
  finiteEntropy_chain p.mass (fun a => (q a).mass) (fun a => (q a).total)

theorem mass_le_map_mass (p : FiniteLaw A) (f : A → B) (a : A) :
    p.mass a ≤ (p.map f).mass (f a) := by
  classical
  rw [map_mass]
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset A))
    (f := fun a' => if f a' = f a then p.mass a' else 0)
    (fun a' _ => by
      split_ifs
      · exact p.nonneg a'
      · exact le_rfl)
    (Finset.mem_univ a)
  simpa using h

def conditional (p : FiniteLaw A) (f : A → B) (b : B) : FiniteLaw A := by
  classical
  exact if hzero : (p.map f).mass b = 0 then p else
    { mass := fun a => (if f a = b then p.mass a else 0) / (p.map f).mass b
      nonneg := fun a => div_nonneg
        (by split_ifs; exact p.nonneg a; exact le_rfl) ((p.map f).nonneg b)
      total := by
        rw [← Finset.sum_div, ← map_mass p f b, div_self hzero] }

theorem map_mass_mul_conditional [DecidableEq B]
    (p : FiniteLaw A) (f : A → B) (b : B) (a : A) :
    (p.map f).mass b * (p.conditional f b).mass a =
      if f a = b then p.mass a else 0 := by
  classical
  by_cases hzero : (p.map f).mass b = 0
  · have ha : f a = b → p.mass a = 0 := by
      intro hab
      have hle := p.mass_le_map_mass f a
      rw [hab, hzero] at hle
      exact le_antisymm hle (p.nonneg a)
    rw [hzero, zero_mul]
    by_cases hab : f a = b
    · rw [ite_eq_left hab, ha hab]
    · rw [ite_eq_right hab]
  · simp only [conditional, hzero, ↓reduceDIte]
    by_cases hab : f a = b
    · simpa only [hab, ite_true, if_true] using (mul_div_cancel₀ (p.mass a) hzero)
    · simp only [hab, ite_false, if_false, zero_div, mul_zero]

end FiniteLaw
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexEntropyContinuity
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass
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

namespace FiniteLaw

variable {A : Type*} [Fintype A]

def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteLaw A where
  mass _a := (Fintype.card A : ℝ)⁻¹
  nonneg _a := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card A : ℝ) ≠ 0 :=
      (Nat.cast_pos.mpr (Fintype.card_pos : 0 < Fintype.card A)).ne'
    simp [Finset.sum_const, nsmul_eq_mul, hn]

@[simp] theorem uniform_mass [Nonempty A] (a : A) :
    (uniform A).mass a = (Fintype.card A : ℝ)⁻¹ := rfl

def pure (a : A) : FiniteLaw A := by
  classical
  exact
    { mass := fun b => if b = a then 1 else 0
      nonneg := fun b => by split_ifs <;> norm_num
      total := by simp }

end FiniteLaw
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

def eventMass (p : FiniteLaw A) (P : A → Prop) : ℝ :=
  ∑ a : {a // P a}, p.mass a.val

def condition (p : FiniteLaw A) (P : A → Prop) (h : 0 < eventMass p P) :
    FiniteLaw {a // P a} where
  mass a := p.mass a.val / eventMass p P
  nonneg a := div_nonneg (p.nonneg a.val) h.le
  total := by rw [← Finset.sum_div]; exact div_self h.ne'

def transport {B : Type*} [Fintype B] (e : A ≃ B) (p : FiniteLaw A) : FiniteLaw B :=
  p.map e

end MatrixMultiplication.CompletionLaws

end

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

namespace Tensor

section Algebra

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def contract (T : Tensor K X Y Z) [Fintype X] [Fintype Y]
    (a : X → K) (b : Y → K) : Z → K :=
  fun z => ∑ x, ∑ y, T x y z * a x * b y

theorem RankAtMost.power {T : Tensor K X Y Z} {r : ℕ}
    (h : RankAtMost T r) (n : ℕ) : RankAtMost (Tensor.power T n) (r ^ n) := by
  rcases h with ⟨a, b, c, rfl⟩
  let aa : (Fin n → Fin r) → (Fin n → X) → K := fun f x => ∏ i, a (f i) (x i)
  let bb : (Fin n → Fin r) → (Fin n → Y) → K := fun f y => ∏ i, b (f i) (y i)
  let cc : (Fin n → Fin r) → (Fin n → Z) → K := fun f z => ∏ i, c (f i) (z i)
  have heq : Tensor.power (fun x y z => ∑ j, rankOne (a j) (b j) (c j) x y z) n =
      fun x y z => ∑ f, rankOne (aa f) (bb f) (cc f) x y z := by
    funext x y z
    simp only [Tensor.power, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f hf
    simp only [rankOne, aa, bb, cc, Finset.prod_mul_distrib]
  rw [heq]
  simpa only [Fintype.card_pi_const, Fintype.card_fin] using rankAtMost_sum_rankOne aa bb cc

end Algebra

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialApproximation
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff _root_.OAI.MatrixMultiplication.RecursiveCompletion.complete_tensor
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

namespace PolynomialApproximation

variable {T : Tensor F X Y Z} {r d D : ℕ}

theorem power_polynomial_eq (A : PolynomialApproximation T r d D) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
    Tensor.power A.polynomial n x y z =
      Polynomial.X ^ (d * n) * Tensor.power A.normalized n x y z := by
  simp [Tensor.power, A.polynomial_eq, Finset.prod_mul_distrib, ← pow_mul]

def power (A : PolynomialApproximation T r d D) (n : ℕ) :
    PolynomialApproximation (Tensor.power T n) (r ^ n) (d * n) (D * n) where
  polynomial := Tensor.power A.polynomial n
  rank_bound := A.rank_bound.power n
  vanishes := by
    intro x y z k hk
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', Nat.not_le_of_lt hk, ite_false, if_false]
  leading := by
    intro x y z
    rw [A.power_polynomial_eq]
    simp only [Polynomial.coeff_X_pow_mul', le_refl, ite_true, if_true, Nat.sub_self,
      Tensor.power, Polynomial.coeff_zero_prod, A.normalized_constant]
  degree_bound := by
    intro x y z
    apply Polynomial.degree_le_of_natDegree_le
    calc
      (Tensor.power A.polynomial n x y z).natDegree ≤
          ∑ i, (A.polynomial (x i) (y i) (z i)).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : Fin n, D := by
        apply Finset.sum_le_sum
        intro i hi
        exact Polynomial.natDegree_le_of_degree_le (A.degree_bound (x i) (y i) (z i))
      _ = D * n := by simp [Nat.mul_comm]

end PolynomialApproximation

end Tensor
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexArithmetic_Complexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex arithmetic programs and asymptotic matrix multiplication costs. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Foundation

namespace Tensor

def matrixMultiplication (a b c : ℕ) :
    Tensor ℂ (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

end Tensor
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexTensorBatching
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

def diagonal (ι : Type*) [DecidableEq ι] : Tensor K ι ι ι :=
  fun i j k => if i = j ∧ i = k then 1 else 0

end Tensor
end MatrixMultiplication.Foundation

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

theorem matrixMultiplication_eq_matrixCoefficients (a b c : ℕ) :
    matrixMultiplication a b c = matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c) := rfl

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexTensorSymmetrization
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
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

theorem directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (T : ι → Tensor K X Y Z) (S : κ → Tensor K U V W) :
    pullback (directSumProductEquiv ι κ X U)
      (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
      (product (directSum T) (directSum S)) =
      directSum (fun i : ι × κ => product (T i.1) (S i.2)) := by
  funext x y z
  change
    (if x.1.1 = y.1.1 ∧ x.1.1 = z.1.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 else 0) *
    (if x.1.2 = y.1.2 ∧ x.1.2 = z.1.2 then
      S x.1.2 x.2.2 y.2.2 z.2.2 else 0) =
    if x.1 = y.1 ∧ x.1 = z.1 then
      T x.1.1 x.2.1 y.2.1 z.2.1 * S x.1.2 x.2.2 y.2.2 z.2.2 else 0
  have hguard : (x.1 = y.1 ∧ x.1 = z.1) ↔
      (x.1.1 = y.1.1 ∧ x.1.1 = z.1.1) ∧
      (x.1.2 = y.1.2 ∧ x.1.2 = z.1.2) := by
    constructor
    · intro h
      exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
        ⟨congrArg Prod.snd h.1, congrArg Prod.snd h.2⟩⟩
    · intro h
      exact ⟨Prod.ext h.1.1 h.2.1, Prod.ext h.1.2 h.2.2⟩
  by_cases hi : x.1.1 = y.1.1 ∧ x.1.1 = z.1.1
  · by_cases hk : x.1.2 = y.1.2 ∧ x.1.2 = z.1.2
    · simp only [ite_eq_left hi, ite_eq_left hk, ite_eq_left (hguard.mpr ⟨hi, hk⟩)]
    · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hk (hguard.mp h).2
      simp only [ite_eq_left hi, ite_eq_right hk, ite_eq_right hfull, mul_zero]
  · have hfull : ¬ (x.1 = y.1 ∧ x.1 = z.1) := fun h => hi (hguard.mp h).1
    simp only [ite_eq_right hi, ite_eq_right hfull, zero_mul]

theorem cyclic_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    cyclic (directSum T) = directSum (fun i => cyclic (T i)) := by
  funext x y z
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [cyclic, directSum]
    · simp [cyclic, directSum, hik, Ne.symm hik]
  · by_cases hki : k = i
    · subst k
      simp [cyclic, directSum, hij]
    · simp [cyclic, directSum, hij, hki]

end Tensor
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialWitnessProduct
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

def productExact (A : PolynomialApproximation T r d D)
    (S : Tensor F U V W) (s : ℕ) (hS : RankAtMost S s) :
    PolynomialApproximation (Tensor.product T S) (r * s) d D := by
  simpa only [Nat.add_zero] using A.product (ofRankAtMost S s hS)

def directSum_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {T : ι → Tensor F X Y Z} {S : κ → Tensor F U V W}
    (A : PolynomialApproximation (Tensor.directSum T) r d D)
    (B : PolynomialApproximation (Tensor.directSum S) s e E) :
    PolynomialApproximation
      (Tensor.directSum (fun i : ι × κ => Tensor.product (T i.1) (S i.2)))
      (r * s) (d + e) (D + E) := by
  have h := (A.product B).pullback (directSumProductEquiv ι κ X U)
    (directSumProductEquiv ι κ Y V) (directSumProductEquiv ι κ Z W)
  simpa only [Tensor.directSum_product] using h

def directSum_pullback {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor F X Y Z}
    (A : PolynomialApproximation (Tensor.directSum T) r d D)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    PolynomialApproximation
      (Tensor.directSum (fun i => Tensor.pullback fx fy fz (T i))) r d D :=
  A.pullback (fun x : ι × X' => (x.1, fx x.2))
    (fun y : ι × Y' => (y.1, fy y.2)) (fun z : ι × Z' => (z.1, fz z.2))

def directSum_cyclic {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor F X Y Z}
    (A : PolynomialApproximation (Tensor.directSum T) r d D) :
    PolynomialApproximation (Tensor.directSum (fun i => Tensor.cyclic (T i))) r d D := by
  simpa only [Tensor.cyclic_directSum] using A.cyclic

end PolynomialApproximation
end Tensor
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_RecursiveCompletion
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionLabels.rootColor_rootIndex _root_.OAI.MatrixMultiplication.CompletionLabels.slot_packLeaf _root_.OAI.MatrixMultiplication.CompletionLabels.terminationProgram_context _root_.OAI.MatrixMultiplication.CompletionLabels.terminationProgram_view _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero
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

instance instFintypeColor : Fintype Color where
  elems := {.B, .A, .C}
  complete color := by cases color <;> simp

namespace RecursiveCompletion

variable {X Y Z : Type*}

theorem weight_pos (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z)
    (hs : Tensor.power S.tensor m x y z ≠ 0) :
    0 < weight S center m x y z := by
  classical
  have hold (i : Fin m) :
      (if S.flagB (x i) then 1 else 0) +
        (if S.flagA (z i) then 1 else 0) +
        (if S.flagC (y i) then 1 else 0) = (1 : ℕ) := by
    apply S.one_hot
    exact (Finset.prod_ne_zero_iff.mp hs) i (Finset.mem_univ i)
  by_contra h
  have hw : weight S center m x y z = 0 := Nat.eq_zero_of_not_pos h
  have hb : ¬ flagB S center m x := by
    intro hb
    simp only [weight, ite_eq_left hb] at hw
    omega
  have ha : ¬ flagA S center m z := by
    intro ha
    simp only [weight, ite_eq_left ha] at hw
    omega
  have hc : ¬ flagC S center m y := by
    intro hc
    simp only [weight, ite_eq_left hc] at hw
    omega
  cases center with
  | B =>
      change ¬ (∀ i, S.flagB (x i)) at hb
      change ¬ (∃ i, S.flagA (z i)) at ha
      change ¬ (∃ i, S.flagC (y i)) at hc
      obtain ⟨i, hi⟩ := not_forall.mp hb
      simpa [hi, not_exists.mp ha i, not_exists.mp hc i] using hold i
  | A =>
      change ¬ (∃ i, S.flagB (x i)) at hb
      change ¬ (∀ i, S.flagA (z i)) at ha
      change ¬ (∃ i, S.flagC (y i)) at hc
      obtain ⟨i, hi⟩ := not_forall.mp ha
      simpa [not_exists.mp hb i, hi, not_exists.mp hc i] using hold i
  | C =>
      change ¬ (∃ i, S.flagB (x i)) at hb
      change ¬ (∃ i, S.flagA (z i)) at ha
      change ¬ (∀ i, S.flagC (y i)) at hc
      obtain ⟨i, hi⟩ := not_forall.mp hc
      simpa [not_exists.mp hb i, not_exists.mp ha i, hi] using hold i

theorem restrict_diagonal {K U V W : Type*} [CommSemiring K]
    [Fintype U] [Fintype V] [Fintype W]
    [DecidableEq U] [DecidableEq V] [DecidableEq W]
    (a : U → K) (b : V → K) (c : W → K) (T : Tensor K U V W)
    (x : U) (y : V) (z : W) :
    Tensor.restrict (diagonalMap a) (diagonalMap b) (diagonalMap c) T x y z =
      a x * b y * c z * T x y z := by
  simp [Tensor.restrict, diagonalMap, ite_mul, mul_ite]

theorem flagPolynomial_eq (p : Prop) :
    flagPolynomial p = (Polynomial.X : Polynomial ℂ) ^ (if p then 1 else 0 : ℕ) := by
  classical
  by_cases hp : p <;> simp [flagPolynomial, hp]

theorem flagPolynomial_degree (p : Prop) : (flagPolynomial p).degree ≤ 1 := by
  classical
  by_cases hp : p <;> simp [flagPolynomial, hp]

variable [Fintype X] [Fintype Y] [Fintype Z]

def leftMap (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → X) → (Fin m → X) → Polynomial ℂ :=
  diagonalMap (fun x => flagPolynomial (flagB S center m x))

def middleMap (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → Y) → (Fin m → Y) → Polynomial ℂ :=
  diagonalMap (fun y => flagPolynomial (flagC S center m y))

def rightMap (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → Z) → (Fin m → Z) → Polynomial ℂ :=
  diagonalMap (fun z => flagPolynomial (flagA S center m z))

theorem diagonalMap_flag_degree {U : Type*} [DecidableEq U] (p : U → Prop)
    (u v : U) : (diagonalMap (fun u => flagPolynomial (p u)) u v).degree ≤ 1 := by
  classical
  by_cases h : v = u
  · simpa [diagonalMap, h] using flagPolynomial_degree (p u)
  · simp [diagonalMap, h]

theorem scalingPolynomial (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z) :
    Tensor.restrict (leftMap S center m) (middleMap S center m) (rightMap S center m)
      (fun x y z => Polynomial.C (Tensor.power S.tensor m x y z)) x y z =
      Polynomial.C (Tensor.power S.tensor m x y z) *
        Polynomial.X ^ weight S center m x y z := by
  classical
  rw [leftMap, middleMap, rightMap, restrict_diagonal]
  simp only [flagPolynomial_eq, weight, pow_add]
  ring

def completionDegeneration (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    Tensor.PolynomialRestrictionDegeneration (Tensor.power S.tensor m)
      (complete S center m).tensor 1 1 1 1 where
  leftMap := leftMap S center m
  middleMap := middleMap S center m
  rightMap := rightMap S center m
  left_degree := diagonalMap_flag_degree _
  middle_degree := diagonalMap_flag_degree _
  right_degree := diagonalMap_flag_degree _
  vanishes := by
    intro x y z j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [scalingPolynomial, Polynomial.coeff_C_mul_X_pow]
    by_cases hs : Tensor.power S.tensor m x y z = 0
    · simp [hs]
    · have hw := weight_pos S center m x y z hs
      simp [Ne.symm (Nat.ne_of_gt hw)]
  leading := by
    intro x y z
    rw [scalingPolynomial, Polynomial.coeff_C_mul_X_pow, complete_tensor]
    simp only [eq_comm]

end RecursiveCompletion
end MatrixMultiplication

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Scripts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.RecursiveCompletion

open MatrixMultiplication.Foundation

inductive Script where
  | base
  | step (prior : Script) (center : Color) (size : ℕ)

namespace Script

def factors : Script → ℕ
  | .base => 1
  | .step prior _ m => prior.factors * m

def Coord (U : Type*) : Script → Type _
  | .base => U
  | .step prior _ m => Fin m → Coord U prior

instance coordFintype (U : Type*) [Fintype U] (s : Script) : Fintype (Coord U s) := by
  induction s with
  | base => exact inferInstanceAs (Fintype U)
  | step prior center m ih =>
      letI := ih
      exact inferInstanceAs (Fintype (Fin m → Coord U prior))

def tensor {X Y Z : Type*} (S : FlaggedTensor X Y Z) :
    (s : Script) → FlaggedTensor (Coord X s) (Coord Y s) (Coord Z s)
  | .base => S
  | .step prior center m => complete (tensor S prior) center m

def order (d : ℕ) : Script → ℕ
  | .base => d
  | .step prior _ m => order d prior * m * 2 + 1

def degree (D : ℕ) : Script → ℕ
  | .base => D
  | .step prior _ m => degree D prior * m * 2 + 1 + 1 + 1

def approximation {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) {R d D : ℕ}
    (A : Tensor.PolynomialApproximation S.tensor R d D) (s : Script) :
    Tensor.PolynomialApproximation (tensor S s).tensor
      (R ^ s.factors) (order d s) (degree D s) := by
  induction s with
  | base => simpa only [tensor, Coord, factors, order, degree, pow_one] using A
  | step prior center m ih =>
      have next := (completionDegeneration (tensor S prior) center m).compose (ih.power m)
      simpa only [tensor, Coord, factors, order, degree, pow_mul] using next

def dual : Script :=
  step (step (step (step (step (step (step base .B 2) .A 2) .C 2) .B 3) .C 2) .B 2) .A 3

@[simp] theorem dual_factors : dual.factors = 288 := by rfl

end Script
end MatrixMultiplication.RecursiveCompletion

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexHierarchyEntropy
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_mass
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

namespace FiniteLaw

theorem map_mass_mul_conditional_map {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (p : FiniteLaw A) (f : A → B) (g : A → C) (b : B) (c : C) :
    (p.map f).mass b * ((p.conditional f b).map g).mass c =
      (p.map (fun a => (f a, g a))).mass (b, c) := by
  classical
  rw [map_mass (p.conditional f b) g c, Finset.mul_sum,
    map_mass p (fun a => (f a, g a)) (b, c)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hgc : g a = c
  · rw [ite_eq_left hgc, map_mass_mul_conditional]
    simp only [Prod.mk.injEq, hgc, and_true]
  · rw [ite_eq_right hgc, mul_zero]
    have hpair : (f a, g a) ≠ (b, c) :=
      fun he => hgc (congrArg Prod.snd he)
    rw [ite_eq_right hpair]

end FiniteLaw

namespace FiniteLabelHierarchy

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)] {depth : ℕ}

def refinementEntropy (h : FiniteLabelHierarchy Label depth) (n : ℕ) : ℝ :=
  if hn : n < depth then
    ∑ r, (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
      finiteEntropy (h.conditional n hn r).mass
  else 0

theorem refinementEntropy_eq (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n < depth) :
    h.refinementEntropy n =
      ∑ r, (h.prefixLaw n (Nat.le_of_lt hn)).mass r *
        finiteEntropy (h.conditional n hn r).mass := by
  simp only [refinementEntropy, dite_eq_left hn]

@[simp] theorem refinementEntropy_eq_zero_of_le
    (h : FiniteLabelHierarchy Label depth) {n : ℕ} (hn : depth ≤ n) :
    h.refinementEntropy n = 0 := by
  simp only [refinementEntropy, dite_eq_right (Nat.not_lt.mpr hn)]

theorem prefixLaw_entropy_succ (h : FiniteLabelHierarchy Label depth)
    (n : ℕ) (hn : n + 1 ≤ depth) :
    finiteEntropy (h.prefixLaw (n + 1) hn).mass =
      finiteEntropy (h.prefixLaw n (Nat.le_of_succ_le hn)).mass +
        h.refinementEntropy n := by
  rw [refinementEntropy_eq h n (Nat.lt_of_succ_le hn)]
  exact FiniteLaw.joint_entropy (h.prefixLaw n (Nat.le_of_succ_le hn))
    (h.conditional n (Nat.lt_of_succ_le hn))

def recordLaw (h : FiniteLabelHierarchy Label depth) :
    FiniteLaw (LabelRecord Label depth) := h.prefixLaw depth le_rfl

def ofLawLabels {A : Type v} [Fintype A] (p : FiniteLaw A)
    (labels : ∀ n, A → Label n) (depth : ℕ) : FiniteLabelHierarchy Label depth where
  conditional n _ r := (p.conditional (labelRecordOf labels n) r).map (labels n)

theorem ofLawLabels_prefixLaw_mass {A : Type v} [Fintype A]
    (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth n : ℕ) (hn : n ≤ depth) :
    ((ofLawLabels p labels depth).prefixLaw n hn).mass =
      (p.map (labelRecordOf labels n)).mass := by
  classical
  induction n with
  | zero =>
      funext r
      rw [prefixLaw_zero_mass, FiniteLaw.map_mass]
      refine p.total.symm.trans ?_
      apply Finset.sum_congr rfl
      intro a _
      rw [ite_eq_left (show labelRecordOf labels 0 a = r by cases r; rfl)]
  | succ n ih =>
      funext rs
      rcases rs with ⟨r, s⟩
      rw [prefixLaw_succ_mass]
      change ((ofLawLabels p labels depth).prefixLaw n
          (Nat.le_of_succ_le hn)).mass r *
        ((p.conditional (labelRecordOf labels n) r).map (labels n)).mass s =
          (p.map (labelRecordOf labels (n + 1))).mass (r, s)
      rw [ih (Nat.le_of_succ_le hn)]
      exact p.map_mass_mul_conditional_map
        (labelRecordOf labels n) (labels n) r s

end FiniteLabelHierarchy

end
end MatrixMultiplication.Foundation

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

theorem previous_scale_lt_population {K : ℕ} (hn : 0 < gridScale K) :
    2 ^ ((gridScale K - 1) ^ 2) < K := by
  exact lt_of_not_ge (Nat.find_min (scale_exists K) (Nat.sub_lt hn (by decide)))

theorem scale_pos {K : ℕ} (hK : 1 < K) : 0 < gridScale K := by
  have h := population_le_scale K
  by_contra hn
  have hz : gridScale K = 0 := Nat.eq_zero_of_not_pos hn
  simp only [hz, zero_pow (by decide : 2 ≠ 0), pow_zero] at h
  exact (not_le_of_gt hK) h

theorem scale_gt_of_population_gt {K n : ℕ} (hK : 2 ^ (n ^ 2) < K) :
    n < gridScale K := by
  by_contra hn
  have hscale : gridScale K ≤ n := Nat.le_of_not_gt hn
  have hp : 2 ^ ((gridScale K) ^ 2) ≤ 2 ^ (n ^ 2) :=
    Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_left hscale 2)
  exact (not_le_of_gt hK) ((population_le_scale K).trans hp)

theorem gridScale_monotone : Monotone gridScale := by
  intro K L hKL
  exact Nat.find_min' (scale_exists K) (hKL.trans (population_le_scale L))

theorem gridGroupOrder_pos (K : ℕ) : 0 < gridGroupOrder K := by
  rw [gridGroupOrder_eq]
  positivity

theorem gridGroupOrder_monotone : Monotone gridGroupOrder := by
  intro K L hKL
  rw [gridGroupOrder_eq, gridGroupOrder_eq]
  exact Nat.pow_le_pow_right (by decide)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (gridScale_monotone hKL) 4) 2)

theorem log_gridGroupOrder (K : ℕ) :
    Real.log (gridGroupOrder K : ℝ) = ((gridScale K : ℝ) + 4) ^ 2 * Real.log 2 := by
  rw [gridGroupOrder_eq, Nat.cast_pow, Real.log_pow]
  norm_cast

theorem log_population_le_log_gridGroupOrder {K : ℕ} (hK : 0 < K) :
    Real.log (K : ℝ) ≤ Real.log (gridGroupOrder K : ℝ) := by
  exact Real.log_le_log (by exact_mod_cast hK)
    (by exact_mod_cast population_le_gridGroupOrder K)

theorem previous_scale_log_lt {K : ℕ} (hK : 1 < K) :
    ((gridScale K : ℝ) - 1) ^ 2 * Real.log 2 < Real.log (K : ℝ) := by
  have hn : 1 ≤ gridScale K := scale_pos hK
  have hp : (0 : ℝ) < (2 : ℝ) ^ ((gridScale K - 1) ^ 2) := by positivity
  have hc : (2 : ℝ) ^ ((gridScale K - 1) ^ 2) < (K : ℝ) := by
    exact_mod_cast previous_scale_lt_population (scale_pos hK)
  have h := Real.log_lt_log hp hc
  simpa only [Real.log_pow, Nat.cast_pow, Nat.cast_sub hn, Nat.cast_one] using h

theorem log_gridGroupOrder_le_of_scale {K : ℕ} {ε : ℝ}
    (hK : 1 < K) (hε : 0 ≤ ε)
    (hscale : 10 * (gridScale K : ℝ) + 15 ≤
      ε * ((gridScale K : ℝ) - 1) ^ 2) :
    Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoly : ((gridScale K : ℝ) + 4) ^ 2 ≤
      (1 + ε) * ((gridScale K : ℝ) - 1) ^ 2 := by nlinarith
  calc
    Real.log (gridGroupOrder K : ℝ) =
        ((gridScale K : ℝ) + 4) ^ 2 * Real.log 2 := log_gridGroupOrder K
    _ ≤ ((1 + ε) * ((gridScale K : ℝ) - 1) ^ 2) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hpoly hlog2.le
    _ = (1 + ε) * (((gridScale K : ℝ) - 1) ^ 2 * Real.log 2) := by ring
    _ ≤ (1 + ε) * Real.log (K : ℝ) :=
      mul_le_mul_of_nonneg_left (previous_scale_log_lt hK).le (by positivity)

theorem eventually_log_gridGroupOrder_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop,
      Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) := by
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (max 2 (72 / ε))
  refine eventually_atTop.2 ⟨2 ^ (m ^ 2) + 1, ?_⟩
  intro K hK
  have hKm : 2 ^ (m ^ 2) < K := by omega
  have hn := scale_gt_of_population_gt hKm
  have hnR : (m : ℝ) < (gridScale K : ℝ) := by exact_mod_cast hn
  have hm2 : 2 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmε : 72 / ε < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hnε : 72 ≤ ε * (gridScale K : ℝ) := by
    have hdiv : 72 / ε < (gridScale K : ℝ) := hmε.trans hnR
    have hmul := (div_lt_iff₀ hε).1 hdiv
    nlinarith
  have hKone : 1 < K := by
    have hp : 1 ≤ 2 ^ (m ^ 2) := Nat.one_le_pow _ _ (by decide)
    omega
  exact log_gridGroupOrder_le_of_scale hKone hε.le
    (scale_error_bound (by linarith) hε.le hnε)

theorem uniform_log_gridGroupOrder_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ,
      Real.log (gridGroupOrder K : ℝ) ≤ (1 + ε) * Real.log (K : ℝ) + C := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 (eventually_log_gridGroupOrder_le hε)
  refine ⟨Real.log (gridGroupOrder K₀ : ℝ), Real.log_natCast_nonneg _, ?_⟩
  intro K
  by_cases hK : K₀ ≤ K
  · exact (hK₀ K hK).trans (le_add_of_nonneg_right (Real.log_natCast_nonneg _))
  · have horder : gridGroupOrder K ≤ gridGroupOrder K₀ :=
      gridGroupOrder_monotone (Nat.le_of_lt (Nat.lt_of_not_ge hK))
    have hpos : (0 : ℝ) < (gridGroupOrder K : ℝ) := by
      rw [gridGroupOrder_eq, Nat.cast_pow]
      positivity
    have hcast : (gridGroupOrder K : ℝ) ≤ (gridGroupOrder K₀ : ℝ) := by
      exact_mod_cast horder
    have hlog := Real.log_le_log hpos hcast
    have hnonneg : 0 ≤ (1 + ε) * Real.log (K : ℝ) :=
      mul_nonneg (by linarith) (Real.log_natCast_nonneg K)
    linarith

theorem tendsto_log_gridGroupOrder_div_nat {K : ℕ → ℕ} {H : ℝ}
    (hK : ∀ N, 0 < K N) (hH : 0 ≤ H)
    (hpop : Tendsto (fun N => Real.log (K N : ℝ) / (N : ℝ)) atTop (nhds H)) :
    Tendsto (fun N => Real.log (gridGroupOrder (K N) : ℝ) / (N : ℝ))
      atTop (nhds H) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [(tendsto_order.1 hpop).1 a ha,
      (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N haN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact haN.trans_le (div_le_div_of_nonneg_right
      (log_population_le_log_gridGroupOrder (hK N)) hNpos.le)
  · intro b hb
    let ε := (b - H) / (2 * (H + 1))
    have hdenom : 0 < 2 * (H + 1) := by linarith
    have hε : 0 < ε := div_pos (by linarith) hdenom
    obtain ⟨C, hC, hbound⟩ := uniform_log_gridGroupOrder_le hε
    have hεeq : ε * (2 * (H + 1)) = b - H := div_mul_cancel₀ _ hdenom.ne'
    have hlimitlt : (1 + ε) * H < b := by nlinarith
    have hconstant : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hupper : Tendsto
        (fun N : ℕ => (1 + ε) * (Real.log (K N : ℝ) / (N : ℝ)) + C / (N : ℝ))
        atTop (nhds ((1 + ε) * H)) := by
      simpa using (hpop.const_mul (1 + ε)).add hconstant
    filter_upwards [(tendsto_order.1 hupper).2 b hlimitlt,
      (eventually_atTop.2 ⟨1, fun N (hN : 1 ≤ N) => hN⟩)] with N hbN hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hle := div_le_div_of_nonneg_right (hbound (K N)) hNpos.le
    have heq : ((1 + ε) * Real.log (K N : ℝ) + C) / (N : ℝ) =
        (1 + ε) * (Real.log (K N : ℝ) / (N : ℝ)) + C / (N : ℝ) := by ring
    rw [heq] at hle
    exact hle.trans_lt hbN

end MatrixMultiplication.Foundation.Separation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexRationalTypes
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLaw.uniform_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

namespace MatrixMultiplication.Foundation

open scoped BigOperators

namespace RationalLaw

variable {A B : Type*} [Fintype A] [Fintype B]

def toFiniteLaw (p : RationalLaw A) : FiniteLaw A where
  mass a := p.mass a
  nonneg a := by exact_mod_cast p.nonneg a
  total := by exact_mod_cast p.total

@[simp] theorem toFiniteLaw_mass (p : RationalLaw A) (a : A) :
    p.toFiniteLaw.mass a = (p.mass a : ℝ) := rfl

end RationalLaw

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

theorem tendsto_log_exactWords_card_mul [DecidableEq A] (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) :
    Tendsto
      (fun t : ℕ => Real.log (Fintype.card (ExactWords (fun a => t * counts a)) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop
      (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  simpa only [exactWords_card] using tendsto_log_multinomial_mul counts hD

end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexHierarchyTypeCounting
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
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

theorem pushforwardCounts_sum {A B : Type*} [Fintype A] [Fintype B]
    (counts : A → ℕ) (label : A → B) :
    (∑ b, pushforwardCounts counts label b) = ∑ a, counts a := by
  classical
  unfold pushforwardCounts
  rw [Finset.sum_comm]
  simp

theorem pushforwardCounts_factorial_prod_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    (∏ b, (pushforwardCounts counts label b).factorial) =
      ∏ a, (counts a).factorial := by
  classical
  have hfactor (b : B) : (pushforwardCounts counts label b).factorial =
      ∏ a, if label a = b then (counts a).factorial else 1 := by
    by_cases hb : ∃ a, label a = b
    · obtain ⟨a, rfl⟩ := hb
      rw [pushforwardCounts_apply counts label hinjective]
      simp [hinjective.eq_iff]
    · simp [pushforwardCounts, not_exists.mp hb]
  simp_rw [hfactor]
  rw [Finset.prod_comm]
  simp

theorem multinomial_pushforwardCounts_of_injective {A B : Type*}
    [Fintype A] [Fintype B] (counts : A → ℕ) (label : A → B)
    (hinjective : Function.Injective label) :
    Nat.multinomial Finset.univ (pushforwardCounts counts label) =
      Nat.multinomial Finset.univ counts := by
  simp only [Nat.multinomial, pushforwardCounts_sum,
    pushforwardCounts_factorial_prod_of_injective counts label hinjective]

namespace LabelHierarchyCounts

variable {Label : ℕ → Type u} [∀ n, Fintype (Label n)]

theorem multinomial_succ (counts : ∀ n, LabelRecord Label n → ℕ) (n : ℕ)
    (compatible : ∀ r, counts n r = ∑ s : Label n, counts (n + 1) (r, s)) :
    Nat.multinomial Finset.univ (counts (n + 1)) =
      Nat.multinomial Finset.univ (counts n) * refinementCount counts n := by
  classical
  have hrows : (fun r => ∑ s : Label n, counts (n + 1) (r, s)) = counts n :=
    funext fun r => (compatible r).symm
  exact (multinomial_prod_counts
    (A := LabelRecord Label n) (B := Label n) (counts (n + 1))).trans
      (congrArg (fun rows : LabelRecord Label n → ℕ =>
        Nat.multinomial Finset.univ rows * refinementCount counts n) hrows)

theorem multinomial_eq_refinementCount_product
    (counts : ∀ n, LabelRecord Label n → ℕ) (depth : ℕ)
    (compatible : ∀ n < depth, ∀ r,
      counts n r = ∑ s : Label n, counts (n + 1) (r, s)) :
    Nat.multinomial Finset.univ (counts depth) =
      ∏ n ∈ Finset.range depth, refinementCount counts n := by
  classical
  induction depth with
  | zero =>
      exact Nat.multinomial_singleton (PUnit.unit : LabelRecord Label 0) (counts 0)
  | succ depth ih =>
      rw [multinomial_succ counts depth (compatible depth (Nat.lt_succ_self depth))]
      rw [ih (fun n hn => compatible n (Nat.lt_trans hn (Nat.lt_succ_self depth))),
        Finset.prod_range_succ]

theorem source_refinementCount_product {A : Type v} [Fintype A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
      Nat.multinomial Finset.univ counts := by
  calc
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
        Nat.multinomial Finset.univ (sourcePrefixCounts counts labels depth) :=
      (multinomial_eq_refinementCount_product (sourcePrefixCounts counts labels) depth
        (fun n _ r => sourcePrefixCounts_compatible counts labels n r)).symm
    _ = Nat.multinomial Finset.univ counts :=
      multinomial_pushforwardCounts_of_injective counts
        (labelRecordOf labels depth) hinjective

theorem source_refinementCount_product_eq_exactWords_card
    {A : Type v} [Fintype A] [DecidableEq A]
    (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∏ n ∈ Finset.range depth, refinementCount (sourcePrefixCounts counts labels) n) =
      Fintype.card (ExactWords counts) := by
  rw [source_refinementCount_product counts labels depth hinjective, exactWords_card]

end LabelHierarchyCounts
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexLocalMaps
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.cyclic_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.ofRankAtMost_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.product_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.pullback_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialApproximation.restrict_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.PolynomialRestrictionDegeneration.compose_polynomial _root_.OAI.MatrixMultiplication.Foundation.Tensor.restrictPolynomial_coeff
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

def originalScale (coefficient : X → Y → Z → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    Tensor K (X × A) (Y × B) (Z × C) :=
  fun x y z => coefficient x.1 y.1 z.1 * T x y z

theorem fiberTransform_originalScale (MX : X → A' → A → K)
    (MY : Y → B' → B → K) (MZ : Z → C' → C → K)
    (coefficient : X → Y → Z → K)
    (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform MX MY MZ (originalScale coefficient T) =
      originalScale coefficient (fiberTransform MX MY MZ T) := by
  funext x y z
  simp only [fiberTransform, originalScale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ac_rfl

theorem fiberTransform_eq_restrict [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (MX : X → A' → A → K) (MY : Y → B' → B → K)
    (MZ : Z → C' → C → K) (T : Tensor K (X × A) (Y × B) (Z × C)) :
    fiberTransform MX MY MZ T =
      Tensor.restrict (fiberMatrix MX) (fiberMatrix MY) (fiberMatrix MZ) T := by
  funext x y z
  simp [fiberTransform, Tensor.restrict, fiberMatrix, Fintype.sum_prod_type,
    ite_mul, mul_ite]

end LocalMaps
end MatrixMultiplication.Foundation

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ComplexHierarchySeparationRates
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
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

theorem poolAuxiliaryCost_pos (k : ℕ) : 0 < poolAuxiliaryCost k := by
  unfold poolAuxiliaryCost
  split_ifs
  · exact Nat.zero_lt_one
  · exact Separation.gridGroupOrder_pos k

theorem poolAuxiliaryCost_le_gridGroupOrder (k : ℕ) :
    poolAuxiliaryCost k ≤ Separation.gridGroupOrder k := by
  unfold poolAuxiliaryCost
  split_ifs with hk
  · simpa only [hk] using Separation.population_le_gridGroupOrder k
  · exact le_rfl

theorem tendsto_log_poolAuxiliaryCost_div_nat {K : ℕ → ℕ} {H : ℝ}
    (hK : ∀ n, 0 < K n) (hH : 0 ≤ H)
    (hpop : Tendsto (fun n => Real.log (K n : ℝ) / (n : ℝ)) atTop (𝓝 H)) :
    Tendsto (fun n => Real.log (poolAuxiliaryCost (K n) : ℝ) / (n : ℝ))
      atTop (𝓝 H) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hpop
    (Separation.tendsto_log_gridGroupOrder_div_nat hK hH hpop) ?_ ?_
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log (Nat.cast_pos.mpr (hK n))
      (by exact_mod_cast population_le_poolAuxiliaryCost (K n))
  · intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.log_le_log (Nat.cast_pos.mpr (poolAuxiliaryCost_pos (K n)))
      (by exact_mod_cast poolAuxiliaryCost_le_gridGroupOrder (K n))

end LabelHierarchySeparation

namespace HierarchySeparationRates

universe u v w

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem pushforwardCounts_mul {B : Type*} (counts : A → ℕ) (label : A → B)
    (t : ℕ) (b : B) :
    pushforwardCounts (fun a => t * counts a) label b =
      t * pushforwardCounts counts label b := by
  classical
  unfold pushforwardCounts
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : label a = b <;> simp [h]

omit [∀ n, Fintype (Label n)] in
theorem sourcePrefixCounts_mul (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (t n : ℕ) (r : LabelRecord Label n) :
    LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a) labels n r =
      t * LabelHierarchyCounts.sourcePrefixCounts counts labels n r :=
  pushforwardCounts_mul counts (labelRecordOf labels n) t r

abbrev PrefixPool (Label : ℕ → Type v) (depth : ℕ) :=
  Σ n : Fin depth, LabelRecord Label n.val

def sourcePoolCounts (counts : A → ℕ) (labels : ∀ n, A → Label n) (depth : ℕ)
    (j : PrefixPool Label depth) (s : Label j.1.val) : ℕ :=
  LabelHierarchyCounts.sourcePrefixCounts counts labels (j.1.val + 1) (j.2, s)

theorem pairingProduct_source_eq (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    pairingProduct (sourcePoolCounts counts labels depth) t =
      Nat.multinomial Finset.univ (fun a => t * counts a) := by
  classical
  unfold pairingProduct
  rw [Fintype.prod_sigma]
  have hpool (n : Fin depth) :
      (∏ r : LabelRecord Label n.val,
        poolTypeCount (sourcePoolCounts counts labels depth) ⟨n, r⟩ t) =
      LabelHierarchyCounts.refinementCount
        (LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a) labels) n.val := by
    apply Finset.prod_congr rfl
    intro r _
    change Nat.multinomial Finset.univ
        (fun s : Label n.val => t *
          LabelHierarchyCounts.sourcePrefixCounts counts labels (n.val + 1) (r, s)) =
      Nat.multinomial Finset.univ
        (fun s : Label n.val =>
          LabelHierarchyCounts.sourcePrefixCounts (fun a => t * counts a)
            labels (n.val + 1) (r, s))
    apply Nat.multinomial_congr
    intro s _
    exact (sourcePrefixCounts_mul counts labels t (n.val + 1) (r, s)).symm
  simp_rw [hpool]
  rw [Fin.prod_univ_eq_prod_range]
  exact LabelHierarchyCounts.source_refinementCount_product
    (fun a => t * counts a) labels depth hinjective

theorem source_poolEntropyTotal_eq (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (hinjective : Function.Injective (labelRecordOf labels depth)) :
    poolEntropyTotal (sourcePoolCounts counts labels depth) = populationEntropyRate counts := by
  have hsource : Tendsto
      (fun t : ℕ => Real.log (pairingProduct (sourcePoolCounts counts labels depth) t : ℝ) /
        (t : ℝ)) atTop (𝓝 (populationEntropyRate counts)) := by
    simpa only [pairingProduct_source_eq counts labels depth hinjective] using
      tendsto_log_multinomial_mul_div_repetition counts
  exact tendsto_nhds_unique
    (tendsto_log_pairingProduct_div (sourcePoolCounts counts labels depth)) hsource

end SourceHierarchy

end HierarchySeparationRates
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexStageHierarchyResources
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation.StageHierarchyResources

open Filter HierarchySeparationRates LabelHierarchyCounts
open scoped BigOperators Topology

universe u v

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

local instance (priority := low) instDecidableEq_solutions_r12cdad_1 {B : Type*} : DecidableEq B := Classical.decEq B
def stageNodeCounts (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ)
    (r : LabelRecord Label n) (s : Label n) : ℕ :=
  sourcePrefixCounts counts labels (n + 1) (r, s)

theorem stageRefinementCount_eq_nodeProduct (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n t : ℕ) :
    stageRefinementCount counts labels n t = pairingProduct (stageNodeCounts counts labels n) t := by
  unfold stageRefinementCount refinementCount pairingProduct
  apply Finset.prod_congr rfl
  intro r hr
  change Nat.multinomial Finset.univ
      (fun s : Label n => sourcePrefixCounts (fun a => t * counts a) labels (n + 1) (r, s)) =
    Nat.multinomial Finset.univ
      (fun s : Label n => t * sourcePrefixCounts counts labels (n + 1) (r, s))
  apply Nat.multinomial_congr
  intro s hs
  exact sourcePrefixCounts_mul counts labels t (n + 1) (r, s)

def stageEntropyRate (counts : A → ℕ) (labels : ∀ n, A → Label n) (n : ℕ) : ℝ :=
  poolEntropyTotal (stageNodeCounts counts labels n)

theorem stageEntropyRate_nonneg (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (n : ℕ) : 0 ≤ stageEntropyRate counts labels n := by
  exact Finset.sum_nonneg (fun r _ => populationEntropyRate_nonneg
    (stageNodeCounts counts labels n r))

theorem tendsto_log_stageRefinementCount_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log (stageRefinementCount counts labels n t : ℝ) / (t : ℝ))
      atTop (𝓝 (stageEntropyRate counts labels n)) := by
  simpa only [stageRefinementCount_eq_nodeProduct, stageEntropyRate] using
    tendsto_log_pairingProduct_div (stageNodeCounts counts labels n)

theorem tendsto_log_stageCost_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log (stageCost counts labels n t : ℝ) / (t : ℝ))
      atTop (𝓝 (stageEntropyRate counts labels n)) :=
  LabelHierarchySeparation.tendsto_log_poolAuxiliaryCost_div_nat
    (stageRefinementCount_pos counts labels n) (stageEntropyRate_nonneg counts labels n)
    (tendsto_log_stageRefinementCount_div counts labels n)

theorem stagePairingProduct_eq_exactWords_card (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) (t : ℕ) :
    stagePairingProduct counts labels depth t =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  unfold stagePairingProduct stageRefinementCount
  rw [Fin.prod_univ_eq_prod_range]
  exact source_refinementCount_product_eq_exactWords_card
    (fun a => t * counts a) labels depth hinjective

theorem sum_stageEntropyRate_eq_nodeEntropyTotal (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ) :
    (∑ n : Fin depth, stageEntropyRate counts labels n.val) =
      poolEntropyTotal (sourcePoolCounts counts labels depth) := by
  simp only [stageEntropyRate, poolEntropyTotal, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro r hr
  rfl

theorem sum_stageEntropyRate_eq_source (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    (∑ n : Fin depth, stageEntropyRate counts labels n.val) = populationEntropyRate counts := by
  rw [sum_stageEntropyRate_eq_nodeEntropyTotal]
  exact source_poolEntropyTotal_eq counts labels depth hinjective

theorem tendsto_log_stageAuxiliaryBudget_div (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) / (t : ℝ))
      atTop (𝓝 (populationEntropyRate counts)) := by
  have h := Separation.tendsto_log_nat_prod_div_nat (I := Fin depth) Finset.univ
    (fun n _ t => LabelHierarchySeparation.poolAuxiliaryCost_pos
      (stageRefinementCount counts labels n.val t))
    (fun n _ => tendsto_log_stageCost_div counts labels n.val)
  simpa only [stageAuxiliaryBudget, stageCost,
    sum_stageEntropyRate_eq_source counts labels depth hinjective] using h

theorem tendsto_log_stageAuxiliaryBudget (counts : A → ℕ) (hD : 0 < ∑ a, counts a)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (hinjective : Function.Injective (labelRecordOf labels depth)) :
    Tendsto
      (fun t : ℕ => Real.log (stageAuxiliaryBudget counts labels depth t : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ)))
      atTop (𝓝 (finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)))) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have hmain : populationEntropyRate counts / (∑ a, counts a : ℕ) =
      finiteEntropy (fun a => (counts a : ℝ) / (∑ a, counts a : ℕ)) := by
    unfold populationEntropyRate
    exact mul_div_cancel_left₀ _ hD'
  simpa only [div_div, hmain] using
    (tendsto_log_stageAuxiliaryBudget_div counts labels depth hinjective).div_const
      ((∑ a, counts a : ℕ) : ℝ)

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

namespace ConditionalLabels

universe u v

section PairAccounting

variable {I : Type u} [Fintype I]

def pairingSize (population : I → ℕ) (reader : I → ReaderPair)
    (pair : ReaderPair) : ℕ :=
  ∏ i, if reader i = pair then population i else 1

def pairingRate (rate : I → ℝ) (reader : I → ReaderPair)
    (pair : ReaderPair) : ℝ :=
  ∑ i, if reader i = pair then rate i else 0

theorem pairingSize_pos (population : I → ℕ) (reader : I → ReaderPair)
    (pair : ReaderPair) (positive : ∀ i, 0 < population i) :
    0 < pairingSize population reader pair := by
  apply Finset.prod_pos
  intro i _
  split_ifs
  · exact positive i
  · exact Nat.zero_lt_one

theorem tendsto_log_pairingSize (population : I → ℕ → ℕ)
    (rate : I → ℝ) (reader : I → ReaderPair) (pair : ReaderPair)
    (positive : ∀ i n, 0 < population i n)
    (growth : ∀ i, Tendsto (fun n => Real.log (population i n : ℝ) / (n : ℝ))
      atTop (𝓝 (rate i))) :
    Tendsto (fun n => Real.log (pairingSize (fun i => population i n) reader pair : ℝ) /
      (n : ℝ)) atTop (𝓝 (pairingRate rate reader pair)) := by
  apply Separation.tendsto_log_nat_prod_div_nat Finset.univ
  · intro i _ n
    split_ifs
    · exact positive i n
    · exact Nat.zero_lt_one
  · intro i _
    by_cases h : reader i = pair
    · simpa only [h, ite_true, if_true] using growth i
    · simpa only [h, ite_false, if_false, Nat.cast_one, Real.log_one, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end PairAccounting

section SourceHierarchy

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

open StageHierarchyResources HierarchySeparationRates

def stagePairingSize (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) (t : ℕ) : ℕ :=
  pairingSize (fun n : Fin depth => stageRefinementCount counts labels n.val t) reader pair

def stagePairingRate (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) : ℝ :=
  pairingRate (fun n : Fin depth => stageEntropyRate counts labels n.val) reader pair

theorem tendsto_log_stagePairingSize (counts : A → ℕ) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      (t : ℝ)) atTop (𝓝 (stagePairingRate counts labels depth reader pair)) := by
  exact tendsto_log_pairingSize _ _ reader pair
    (fun n => stageRefinementCount_pos counts labels n.val)
    (fun n => tendsto_log_stageRefinementCount_div counts labels n.val)

theorem tendsto_log_stagePairingSize_normalized (counts : A → ℕ)
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (stagePairingRate counts labels depth reader pair / (∑ a, counts a : ℕ))) := by
  simpa only [div_div] using
    (tendsto_log_stagePairingSize counts labels depth reader pair).div_const
      ((∑ a, counts a : ℕ) : ℝ)

def lawPairingRate (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (depth : ℕ) (reader : Fin depth → ReaderPair) (pair : ReaderPair) : ℝ :=
  pairingRate (fun n : Fin depth =>
    (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n.val) reader pair

end SourceHierarchy
end ConditionalLabels
end MatrixMultiplication

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Labels
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
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

instance leafFintype [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) : Fintype (Leaf S) :=
  inferInstanceAs (Fintype {p : X × Y × Z // S.tensor p.1 p.2.1 p.2.2 ≠ 0})

def pattern (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) : Fin m → Color :=
  fun i => leafColor S (slot S center m a i)

theorem slot_injective (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    Function.Injective (slot S center m) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact congrArg (fun w : Leaf S => w.val.1) (congrFun h i)
  · apply Prod.ext
    · funext i
      exact congrArg (fun w : Leaf S => w.val.2.1) (congrFun h i)
    · funext i
      exact congrArg (fun w : Leaf S => w.val.2.2) (congrFun h i)

theorem completed_color_iff (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) (c : Color) :
    leafColor (complete S center m) a = c ↔
      raisedFlag center c (fun i => pattern S center m a i = c) := by
  rw [leafColor_eq_iff]
  have hold (i : Fin m) := leafColor_eq_iff S (slot S center m a i) c
  have heq : (fun i => pattern S center m a i = c) =
      (fun i => ownerFlag S c (coordinate (slot S center m a i).val c)) := by
    funext i
    exact propext (hold i)
  rw [heq]
  cases c <;> rfl

theorem pattern_mem (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) (i : Fin m) :
    pattern S center m a i = center ∨
      pattern S center m a i = leafColor (complete S center m) a := by
  by_cases hc : pattern S center m a i = center
  · exact Or.inl hc
  · right
    have hn : center ≠ pattern S center m a i := Ne.symm hc
    have hnew : leafColor (complete S center m) a = pattern S center m a i := by
      apply (completed_color_iff S center m a _).mpr
      simp only [raisedFlag, ite_eq_right hn]
      exact ⟨i, rfl⟩
    exact hnew.symm

theorem pattern_eq_center (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m))
    (h : leafColor (complete S center m) a = center) :
    pattern S center m a = fun _ => center := by
  funext i
  have hi := pattern_mem S center m a i
  simpa only [h, or_self] using hi

def centerRead (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (u : Fin m → Coordinate X Y Z center) : Fin m → Color :=
  fun i => if ownerFlag S center (u i) then center else output

def outputRead (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (u : Fin m → Coordinate X Y Z output) : Fin m → Color :=
  fun i => if ownerFlag S output (u i) then output else center

theorem centerRead_pattern (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) :
    centerRead S center (leafColor (complete S center m) a) m
      (fun i => coordinate (slot S center m a i).val center) = pattern S center m a := by
  funext i
  have hc := leafColor_eq_iff S (slot S center m a i) center
  change (if ownerFlag S center _ then center else _) = _
  by_cases h : pattern S center m a i = center
  · rw [ite_eq_left (hc.mp h), h]
  · rw [ite_eq_right (fun hf => h (hc.mpr hf))]
    exact (Or.resolve_left (pattern_mem S center m a i) h).symm

theorem outputRead_pattern (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) :
    outputRead S center (leafColor (complete S center m) a) m
      (fun i => coordinate (slot S center m a i).val
        (leafColor (complete S center m) a)) = pattern S center m a := by
  funext i
  have hc := leafColor_eq_iff S (slot S center m a i)
    (leafColor (complete S center m) a)
  change (if ownerFlag S _ _ then _ else center) = _
  by_cases h : pattern S center m a i = leafColor (complete S center m) a
  · rw [ite_eq_left (hc.mp h), h]
  · rw [ite_eq_right (fun hf => h (hc.mpr hf))]
    exact (Or.resolve_right (pattern_mem S center m a i) h).symm

theorem packLeaf_color (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (w : Fin m → Leaf S) (active) (allowed) :
    leafColor (complete S center m) (packLeaf S center output m w active allowed) = output := by
  apply (completed_color_iff S center m _ output).mpr
  simpa only [pattern, slot_packLeaf] using active

def conditionalLeafEquiv (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ) :
    {a : Leaf (complete S center m) // leafColor (complete S center m) a = output} ≃
      {w : Fin m → Leaf S //
        raisedFlag center output (fun i => leafColor S (w i) = output) ∧
        ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output} where
  toFun a := ⟨slot S center m a.val,
    (completed_color_iff S center m a.val output).mp a.property,
    fun i => by simpa only [pattern, ← a.property] using pattern_mem S center m a.val i⟩
  invFun w := ⟨packLeaf S center output m w.val w.property.1 w.property.2,
    packLeaf_color S center output m w.val w.property.1 w.property.2⟩
  left_inv a := by
    apply Subtype.ext
    apply slot_injective S center m
    simp only [slot_packLeaf]
  right_inv w := by
    apply Subtype.ext
    simp only [slot_packLeaf]

instance retainedLeafFintype [Fintype X] [Fintype Y] [Fintype Z]
    (S : FlaggedTensor X Y Z) (first second : Color) :
    Fintype (RetainedLeaf S first second) :=
  inferInstanceAs (Fintype {a : Leaf S // leafColor S a = first ∨ leafColor S a = second})

end MatrixMultiplication.CompletionLabels

namespace MatrixMultiplication.CompletionLabels

open RecursiveCompletion TopologicalFlatten
attribute [local instance] Classical.propDecidable Classical.decEq

variable {X Y Z : Type uCoord}

def patternSideRead (S : FlaggedTensor X Y Z) (center output side : Color) (m : ℕ)
    (u : Fin m → Coordinate X Y Z side) : Fin m → Color :=
  if center = output then fun _ => center
  else if side = center then fun i => if ownerFlag S side (u i) then center else output
  else fun i => if ownerFlag S side (u i) then output else center

theorem patternSideRead_correct (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (a : Leaf (complete S center m))
    (ha : leafColor (complete S center m) a = output) (side : Color)
    (hs : center ≠ output → side = center ∨ side = output) :
    patternSideRead S center output side m
      (fun i => coordinate (slot S center m a i).val side) = pattern S center m a := by
  by_cases h : center = output
  · simp only [patternSideRead, ite_eq_left h]
    exact (pattern_eq_center S center m a (ha.trans h.symm)).symm
  · rcases hs h with heq | heq
    · subst side
      simp only [patternSideRead, ite_eq_right h, ite_true, if_true]
      have hr := centerRead_pattern S center m a
      rw [ha] at hr
      unfold centerRead at hr
      exact hr
    · subst side
      simp only [patternSideRead, ite_eq_right h, ite_eq_right (Ne.symm h)]
      have hr := outputRead_pattern S center m a
      rw [ha] at hr
      exact hr

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten

open MatrixMultiplication.Foundation RecursiveCompletion

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v w z u' v' w'

namespace Program

variable {A : Type u} {Coord : Color → Type v}
  {Context : Type z} {Code : Type w} {depth : ℕ}

theorem pullback_complete {B : Type u'} {NewCoord : Color → Type v'}
    (p : Program A Coord Context Code depth) (source : B → A)
    (view : (side : Color) → B → NewCoord side)
    (project : (side : Color) → NewCoord side → Coord side)
    (projects : ∀ side b, project side (view side b) = p.view side (source b))
    (complete : p.Complete) (injective : Function.Injective source) :
    (p.pullback source view project projects).Complete := by
  intro a b hc hl
  apply injective
  exact complete (source a) (source b) hc hl

theorem recode_complete {NewCode : Type w'} (p : Program A Coord Context Code depth)
    (encode : Code → NewCode) (decode : NewCode → Code)
    (roundtrip : Function.LeftInverse decode encode) (complete : p.Complete) :
    (p.recode encode decode roundtrip).Complete := by
  intro a b hc hl
  apply complete a b hc
  intro n hn
  exact roundtrip.injective (hl n hn)

theorem append_labels_left {OtherContext : Type z} {d e : ℕ}
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a)
    (n : ℕ) (hn : n < d) (a : A) :
    (p.append q sameView derive derive_correct).labels n a = p.labels n a := by
  simp [append, appendLabel, hn]

theorem append_labels_right {OtherContext : Type z} {d e : ℕ}
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a)
    (n : ℕ) (a : A) :
    (p.append q sameView derive derive_correct).labels (d + n) a = q.labels n a := by
  have h : ¬d + n < d := by omega
  simp [append, appendLabel, h]

theorem append_complete {OtherContext : Type z} {d e : ℕ}
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a)
    (complete : q.Complete) :
    (p.append q sameView derive derive_correct).Complete := by
  intro a b hc hl
  change p.context a = p.context b at hc
  have hhead : (fun j : Fin d => p.labels j.val a) =
      (fun j : Fin d => p.labels j.val b) := by
    funext j
    have h := hl j.val (by omega)
    simpa only [append_labels_left p q sameView derive derive_correct j.val j.isLt] using h
  have hctx : q.context a = q.context b := by
    rw [← derive_correct a, ← derive_correct b, hc, hhead]
  apply complete a b hctx
  intro n hn
  have h := hl (d + n) (by omega)
  simpa only [append_labels_right] using h

def recordArray {Code : Type w} :
    (n : ℕ) → LabelRecord (fun _ => Code) n → Fin n → Code
  | 0, _, i => Fin.elim0 i
  | n + 1, prior, i =>
      if h : i.val < n then recordArray n prior.1 ⟨i.val, h⟩ else prior.2

theorem recordArray_labelRecordOf {B : Type u'} (labels : ℕ → B → Code)
    (n : ℕ) (a : B) :
    recordArray n (labelRecordOf labels n a) = (fun i => labels i.val a) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      funext i
      by_cases h : i.val < n
      · simp only [recordArray, dite_eq_left h]
        exact congrFun ih ⟨i.val, h⟩
      · have hi : i.val = n := by omega
        simp [recordArray, hi, labelRecordOf]

end Program
end MatrixMultiplication.CompletionLabels.TopologicalFlatten

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten
attribute [local instance] Classical.propDecidable Classical.decEq

variable {X Y Z : Type uCoord}

def completionView (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (side : Color) (a : Leaf (complete S center m)) : Fin m → Coordinate X Y Z side :=
  fun i => coordinate (slot S center m a i).val side

def patternProgram (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    Program (Leaf (complete S center m)) (fun side => Fin m → Coordinate X Y Z side)
      Color (Option (Fin m → Color)) 3 where
  context := leafColor (complete S center m)
  view := completionView S center m
  pair n := ownerPair center (rootColor n)
  labels n a := if leafColor (complete S center m) a = rootColor n then
    some (pattern S center m a) else none
  read n side ctx _ own := if ctx = rootColor n then
    some (patternSideRead S center ctx side m own) else none
  readable := by
    intro n hn a side hs
    by_cases h : leafColor (complete S center m) a = rootColor n
    · simp only [ite_eq_left h]
      congr 1
      apply patternSideRead_correct S center _ m a rfl side
      intro hne
      have hmem : side = center ∨ side = rootColor n := by
        rcases hs with rfl | rfl
        · exact ownerPair_first_mem center (rootColor n) (by simpa only [h] using hne)
        · exact ownerPair_second_mem center (rootColor n) (by simpa only [h] using hne)
      simpa only [h] using hmem
    · simp only [ite_eq_right h]

def decodePattern (center : Color) (m : ℕ) (output : Color)
    (prior : Fin 3 → Option (Fin m → Color)) : Fin m → Color :=
  (prior (rootIndex output)).getD (fun _ => center)

theorem decodePattern_correct (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a : Leaf (complete S center m)) :
    decodePattern center m ((patternProgram S center m).context a)
      (fun j => (patternProgram S center m).labels j.val a) = pattern S center m a := by
  simp [decodePattern, patternProgram]

end MatrixMultiplication.CompletionLabels
namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v w z

variable {A : Type u} {Coord : Color → Type v}
  {Context : Type z} {Code : Type w} {depth : ℕ}

def powLabel [Inhabited Code]
    (p : Program A Coord Context Code depth) (m n : ℕ) (a : Fin m → A) : Code :=
  if hi : n / depth < m then
    p.labels (n % depth) (a ⟨n / depth, hi⟩)
  else default

theorem powLabel_at [Inhabited Code]
    (p : Program A Coord Context Code depth) (m : ℕ)
    (a : Fin m → A) (i : Fin m) {k : ℕ} (hk : k < depth) :
    powLabel p m (i.val * depth + k) a = p.labels k (a i) := by
  have hd : 0 < depth := lt_of_le_of_lt (Nat.zero_le k) hk
  have hquot : (i.val * depth + k) / depth = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd,
      Nat.div_eq_of_lt hk, Nat.zero_add]
  have hrem : (i.val * depth + k) % depth = k := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hk]
  simp only [powLabel, hquot, hrem, dite_eq_left i.isLt]

def pow [Inhabited Code] (p : Program A Coord Context Code depth) (m : ℕ) :
    Program (Fin m → A) (fun side => Fin m → Coord side)
      (Fin m → Context) Code (m * depth) where
  context a i := p.context (a i)
  view side a i := p.view side (a i)
  pair n := p.pair (n % depth)
  labels := powLabel p m
  read n side ctx prior own :=
    if hi : n / depth < m then
      p.read (n % depth) side (ctx ⟨n / depth, hi⟩)
        (fun j => prior (powPast depth n j)) (own ⟨n / depth, hi⟩)
    else default
  readable := by
    intro n hn a side hs
    have hd : 0 < depth := by
      by_contra h
      have hzero : depth = 0 := by omega
      simp [hzero] at hn
    have hi : n / depth < m := (Nat.div_lt_iff_lt_mul hd).2 hn
    let i : Fin m := ⟨n / depth, hi⟩
    have hlocal : n % depth < depth := Nat.mod_lt n hd
    have hprior :
        (fun j : Fin (n % depth) => powLabel p m (powPast depth n j).val a) =
        (fun j : Fin (n % depth) => p.labels j.val (a i)) := by
      funext j
      change powLabel p m (i.val * depth + j.val) a = p.labels j.val (a i)
      exact powLabel_at p m a i (lt_trans j.isLt hlocal)
    simp only [dite_eq_left hi]
    change p.read (n % depth) side (p.context (a i))
      (fun j : Fin (n % depth) => powLabel p m (powPast depth n j).val a)
      (p.view side (a i)) = powLabel p m n a
    rw [hprior]
    simpa only [powLabel, dite_eq_left hi] using
      p.readable (n % depth) hlocal (a i) side hs

theorem pow_complete [Inhabited Code]
    (p : Program A Coord Context Code depth) (m : ℕ) (complete : p.Complete) :
    (p.pow m).Complete := by
  intro a b hc hl
  funext i
  apply complete (a i) (b i)
  · exact congrFun hc i
  · intro k hk
    have hindex : i.val * depth + k < m * depth := by
      calc
        i.val * depth + k < i.val * depth + depth := Nat.add_lt_add_left hk _
        _ = (i.val + 1) * depth := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ m * depth := Nat.mul_le_mul_right depth (Nat.succ_le_of_lt i.isLt)
    have h := hl (i.val * depth + k) hindex
    change powLabel p m (i.val * depth + k) a =
      powLabel p m (i.val * depth + k) b at h
    rw [powLabel_at p m a i hk, powLabel_at p m b i hk] at h
    exact h

end MatrixMultiplication.CompletionLabels.TopologicalFlatten.Program

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

universe w
variable {X Y Z : Type uCoord} {Code : Type w} {depth : ℕ}

abbrev CompletionCode (m : ℕ) (Code : Type w) := Option ((Fin m → Color) ⊕ Code)

def encodePattern {m : ℕ} : Option (Fin m → Color) → CompletionCode m Code
  | none => none
  | some pattern => some (.inl pattern)

def decodePatternCode {m : ℕ} : CompletionCode m Code → Option (Fin m → Color)
  | some (.inl pattern) => some pattern
  | _ => none

theorem patternCode_roundtrip {m : ℕ} :
    Function.LeftInverse (decodePatternCode (Code := Code)) (encodePattern (m := m)) := by
  intro c
  cases c <;> rfl

def encodeOld {m : ℕ} (c : Code) : CompletionCode m Code := some (.inr c)

def decodeOld [Inhabited Code] {m : ℕ} : CompletionCode m Code → Code
  | some (.inr c) => c
  | _ => default

theorem oldCode_roundtrip [Inhabited Code] {m : ℕ} :
    Function.LeftInverse (decodeOld (Code := Code) (m := m)) encodeOld := by
  intro c
  rfl

def inheritedProgram (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (Leaf (complete S center m)) (fun side => Fin m → Coordinate X Y Z side)
      (Fin m → Color) (CompletionCode m Code) (m * depth) :=
  let old := p.recode encodeOld decodeOld oldCode_roundtrip
  (old.pow m).pullback (slot S center m) (completionView S center m)
    (fun _ => id) (by
      intro side a
      funext i
      exact (view_eq side (slot S center m a i)).symm)

theorem inheritedProgram_complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (inheritedProgram S center m p view_eq).Complete := by
  exact Program.pullback_complete
    ((p.recode encodeOld decodeOld oldCode_roundtrip).pow m)
    (slot S center m) (completionView S center m) (fun _ => id)
    (by intro side a; funext i; exact (view_eq side (slot S center m a i)).symm)
    (Program.pow_complete _ m
      (Program.recode_complete p encodeOld decodeOld oldCode_roundtrip complete))
    (slot_injective S center m)

def completionContextDecoder (center : Color) (m : ℕ) (output : Color)
    (prior : Fin 3 → CompletionCode m Code) : Fin m → Color :=
  decodePattern center m output (fun i => decodePatternCode (prior i))

theorem completionContextDecoder_correct
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (a : Leaf (complete S center m)) :
    completionContextDecoder (Code := Code) center m
      (((patternProgram S center m).recode (encodePattern (Code := Code)) decodePatternCode
        patternCode_roundtrip).context a)
      (fun j => ((patternProgram S center m).recode (encodePattern (Code := Code)) decodePatternCode
        patternCode_roundtrip).labels j.val a) =
      (inheritedProgram S center m p view_eq).context a := by
  change decodePattern center m (leafColor (complete S center m) a)
    (fun j => decodePatternCode (Code := Code)
      (encodePattern ((patternProgram S center m).labels j.val a))) =
      (fun i => p.context (slot S center m a i))
  have hr (c : Option (Fin m → Color)) :
      decodePatternCode (encodePattern c : CompletionCode m Code) = c := patternCode_roundtrip c
  simp only [hr]
  exact (decodePattern_correct S center m a).trans (by
    funext i
    exact (context_eq (slot S center m a i)).symm)

def completionProgram (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (Leaf (complete S center m)) (fun side => Fin m → Coordinate X Y Z side)
      Color (CompletionCode m Code) (3 + m * depth) :=
  ((patternProgram S center m).recode encodePattern decodePatternCode patternCode_roundtrip).append
    (inheritedProgram S center m p view_eq) (fun _ _ => rfl)
    (completionContextDecoder center m)
    (completionContextDecoder_correct S center m p context_eq view_eq)

theorem completionProgram_complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (completionProgram S center m p context_eq view_eq).Complete := by
  exact Program.append_complete
    ((patternProgram S center m).recode encodePattern decodePatternCode patternCode_roundtrip)
    (inheritedProgram S center m p view_eq) (fun _ _ => rfl)
    (completionContextDecoder center m)
    (completionContextDecoder_correct S center m p context_eq view_eq)
    (inheritedProgram_complete S center m p view_eq complete)

def coordinateWord (m : ℕ) (side : Color) :
    Coordinate (Fin m → X) (Fin m → Y) (Fin m → Z) side →
      (Fin m → Coordinate X Y Z side) := by
  cases side <;> exact id

theorem coordinateWord_coordinate (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (side : Color) (a : Leaf (complete S center m)) :
    coordinateWord m side (coordinate a.val side) = completionView S center m side a := by
  cases side <;> rfl

def completionLocalProgram (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side) :
    Program (Leaf (complete S center m))
      (Coordinate (Fin m → X) (Fin m → Y) (Fin m → Z))
      Color (CompletionCode m Code) (3 + m * depth) :=
  (completionProgram S center m p context_eq view_eq).pullback id
    (fun side a => coordinate a.val side) (coordinateWord m)
    (coordinateWord_coordinate S center m)

theorem completionLocalProgram_complete (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    [Inhabited Code]
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (complete : p.Complete) :
    (completionLocalProgram S center m p context_eq view_eq).Complete := by
  exact Program.pullback_complete (completionProgram S center m p context_eq view_eq)
    id (fun side a => coordinate a.val side) (coordinateWord m)
    (coordinateWord_coordinate S center m)
    (completionProgram_complete S center m p context_eq view_eq complete)
    Function.injective_id

namespace ReadableTensor

def raise (S : FlaggedTensor X Y Z) (r : ReadableTensor S) (center : Color) (m : ℕ) :
    ReadableTensor (RecursiveCompletion.complete S center m) where
  Code := CompletionCode m r.Code
  depth := 3 + m * r.depth
  program := completionLocalProgram S center m r.program r.context_eq r.view_eq
  context_eq _ := rfl
  view_eq _ _ := rfl
  complete := completionLocalProgram_complete S center m r.program r.context_eq r.view_eq r.complete

def script (S : FlaggedTensor X Y Z) (r : ReadableTensor S) :
    (s : Script) → ReadableTensor (Script.tensor S s)
  | .base => r
  | .step prior center m => raise _ (script S r prior) center m

end ReadableTensor

end MatrixMultiplication.CompletionLabels

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_ProductLaws
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_succ_mass _root_.OAI.MatrixMultiplication.Foundation.FiniteLabelHierarchy.prefixLaw_zero_mass _root_.OAI.MatrixMultiplication.Foundation.RationalLaw.toFiniteLaw_mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionProductLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*} [∀ i, Fintype (A i)]

def independentProduct (p : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) := by
  classical
  exact
    { mass := fun x => ∏ i, (p i).mass (x i)
      nonneg := fun x => Finset.prod_nonneg fun i _ => (p i).nonneg (x i)
      total := by rw [← Fintype.prod_sum]; simp only [(p _).total, Finset.prod_const_one] }

@[simp] theorem independentProduct_mass (p : ∀ i, FiniteLaw (A i)) (x : ∀ i, A i) :
    (independentProduct p).mass x = ∏ i, (p i).mass (x i) := rfl

def sigmaJoint (p : FiniteLaw I) (q : ∀ i, FiniteLaw (A i)) : FiniteLaw (Sigma A) where
  mass x := p.mass x.1 * (q x.1).mass x.2
  nonneg x := mul_nonneg (p.nonneg x.1) ((q x.1).nonneg x.2)
  total := by simp [Fintype.sum_sigma, ← Finset.mul_sum, (q _).total, p.total]

omit [DecidableEq I] in
@[simp] theorem sigmaJoint_mass (p : FiniteLaw I) (q : ∀ i, FiniteLaw (A i)) (x : Sigma A) :
    (sigmaJoint p q).mass x = p.mass x.1 * (q x.1).mass x.2 := rfl

end MatrixMultiplication.CompletionProductLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_ColorLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionColorLaws

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionProductLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

abbrev ColorSlice (S : FlaggedTensor X Y Z) (c : Color) :=
  {a : Leaf S // leafColor S a = c}

def colorMix (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) : FiniteLaw (Leaf S) where
  mass a := α * (pc.map Subtype.val).mass a + (1 - α) * (po.map Subtype.val).mass a
  nonneg a := add_nonneg (mul_nonneg hα ((pc.map Subtype.val).nonneg a))
    (mul_nonneg (sub_nonneg.mpr hα') ((po.map Subtype.val).nonneg a))
  total := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      (pc.map Subtype.val).total, (po.map Subtype.val).total]
    ring

theorem colorMix_mass (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (a : Leaf S) :
    (colorMix S center output pc po α hα hα').mass a =
      α * (pc.map Subtype.val).mass a + (1 - α) * (po.map Subtype.val).mass a := rfl

theorem colorSlice_map_mass_zero (S : FlaggedTensor X Y Z) (c : Color)
    (p : FiniteLaw (ColorSlice S c)) (a : Leaf S) (ha : leafColor S a ≠ c) :
    (p.map Subtype.val).mass a = 0 := by
  rw [FiniteLaw.map_mass]
  apply Finset.sum_eq_zero
  intro b _
  apply ite_eq_right
  intro hb
  exact ha ((congrArg (leafColor S) hb).symm.trans b.property)

theorem colorMix_mass_zero (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) (a : Leaf S)
    (hc : leafColor S a ≠ center) (ho : leafColor S a ≠ output) :
    (colorMix S center output pc po α hα hα').mass a = 0 := by
  rw [colorMix_mass, colorSlice_map_mass_zero S center pc a hc,
    colorSlice_map_mass_zero S output po a ho]
  ring

theorem exists_mass_pos {A : Type*} [Fintype A] (p : FiniteLaw A) :
    ∃ a, 0 < p.mass a := by
  by_contra h
  have hz : ∀ a, p.mass a = 0 := by
    intro a
    exact le_antisymm (le_of_not_gt (fun ha => h ⟨a, ha⟩)) (p.nonneg a)
  have ht := p.total
  simp only [hz, Finset.sum_const_zero] at ht
  exact zero_ne_one ht

theorem colorMix_output_mass_pos (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) (a : ColorSlice S output)
    (ha : 0 < po.mass a) :
    0 < (colorMix S center output pc po α hα hα'.le).mass a.val := by
  rw [colorMix_mass, po.map_mass_apply Subtype.val Subtype.val_injective]
  exact add_pos_of_nonneg_of_pos
    (mul_nonneg hα ((pc.map Subtype.val).nonneg a.val))
    (mul_pos (sub_pos.mpr hα') ha)

abbrev completionEvent (S : FlaggedTensor X Y Z) (center output : Color) (m : ℕ)
    (w : Fin m → Leaf S) : Prop :=
  raisedFlag center output (fun i => leafColor S (w i) = output) ∧
    ∀ i, leafColor S (w i) = center ∨ leafColor S (w i) = output

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem completionEvent_constant (S : FlaggedTensor X Y Z) (center output : Color)
    (m : ℕ) (hm : 0 < m) (a : ColorSlice S output) :
    completionEvent S center output m (fun _ => a.val) := by
  constructor
  · by_cases h : center = output
    · simp [raisedFlag, h, a.property]
    · simpa only [raisedFlag, ite_eq_right h] using
        (show ∃ _i : Fin m, leafColor S a.val = output from ⟨⟨0, hm⟩, a.property⟩)
  · exact fun _ => Or.inr a.property

def iidColorLaw (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1) :
    FiniteLaw (Fin m → Leaf S) :=
  independentProduct (I := Fin m) (A := fun _ => Leaf S)
    (fun _ : Fin m => colorMix S center output pc po α hα hα')

theorem completionEvent_mass_pos (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) :
    0 < eventMass (iidColorLaw S center output pc po m α hα hα'.le)
      (completionEvent S center output m) := by
  obtain ⟨a, ha⟩ := exists_mass_pos po
  let w : {w : Fin m → Leaf S // completionEvent S center output m w} :=
    ⟨fun _ => a.val, completionEvent_constant S center output m hm a⟩
  have hw : 0 < (iidColorLaw S center output pc po m α hα hα'.le).mass w.val := by
    change 0 < ∏ _i : Fin m, (colorMix S center output pc po α hα hα'.le).mass a.val
    exact Finset.prod_pos fun _ _ => colorMix_output_mass_pos S center output pc po α hα hα' a ha
  exact lt_of_lt_of_le hw (Finset.single_le_sum
    (fun v _ => (iidColorLaw S center output pc po m α hα hα'.le).nonneg v.val)
    (Finset.mem_univ w))

def conditionalCompletionLaw (S : FlaggedTensor X Y Z) (center output : Color)
    (pc : FiniteLaw (ColorSlice S center)) (po : FiniteLaw (ColorSlice S output))
    (m : ℕ) (hm : 0 < m) (α : ℝ) (hα : 0 ≤ α) (hα' : α < 1) :
    FiniteLaw (ColorSlice (complete S center m) output) :=
  transport (conditionalLeafEquiv S center output m).symm
    (condition (iidColorLaw S center output pc po m α hα hα'.le)
      (completionEvent S center output m)
      (completionEvent_mass_pos S center output pc po m hm α hα hα'))

end MatrixMultiplication.CompletionColorLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_CenterLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

universe uCoord

namespace MatrixMultiplication.CompletionColorLaws

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionProductLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

def centerWordEquiv (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → ColorSlice S center) ≃
      {w : Fin m → Leaf S // completionEvent S center center m w} where
  toFun w := ⟨fun i => (w i).val, by
    constructor
    · simpa [raisedFlag] using (fun i => (w i).property)
    · exact fun i => Or.inl (w i).property⟩
  invFun w := fun i => ⟨w.val i, by
    have hall : ∀ j, leafColor S (w.val j) = center := by
      simpa [raisedFlag] using w.property.1
    exact hall i⟩
  left_inv w := by
    funext i
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl

def centerCompletionEquiv (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    (Fin m → ColorSlice S center) ≃ ColorSlice (complete S center m) center :=
  (centerWordEquiv S center m).trans (conditionalLeafEquiv S center center m).symm

def centerCompletionLaw (S : FlaggedTensor X Y Z) (center : Color)
    (p : FiniteLaw (ColorSlice S center)) (m : ℕ) :
    FiniteLaw (ColorSlice (complete S center m) center) :=
  transport (centerCompletionEquiv S center m)
    (independentProduct (fun _ : Fin m => p))

end MatrixMultiplication.CompletionColorLaws

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

variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

variable {Position : Type w} [Fintype Position]
variable {counts : A → ℕ} {labels : ∀ n, A → Label n} {n t : ℕ}

section Root

omit [∀ n, Fintype (Label n)]

local instance (priority := low) instDecidableEq_solutions_r12cdad_2 {B : Type*} : DecidableEq B := Classical.decEq B
def rootPrefixEquiv (counts : A → ℕ) (labels : ∀ n, A → Label n) (t : ℕ)
    (Position : Type w) [Fintype Position]
    (hN : Fintype.card Position = ∑ a, t * counts a) :
    ExactPrefix counts labels 0 t Position ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := rootPrefixWord counts labels t Position hN
  left_inv word := by
    apply Subtype.ext
    funext i
    exact Subsingleton.elim _ _
  right_inv point := by cases point; rfl

end Root

end MatrixMultiplication.Foundation.ConditionalPrefixWords

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_HierarchyWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionHierarchyWords

open MatrixMultiplication.Foundation ConditionalPrefixWords
open scoped BigOperators Classical

universe u v x y z p q

structure ReadableHierarchy (A : Type u) (X : Type x) (Y : Type y) (Z : Type z) where
  Label : ℕ → Type v
  fintypeLabel : ∀ n, Fintype (Label n)
  labels : ∀ n, A → Label n
  depth : ℕ
  pair : ℕ → ReaderPair
  x : A → X
  y : A → Y
  z : A → Z
  coordinates_injective : Function.Injective (fun a => (x a, y a, z a))
  readXYX : (n : ℕ) → pair n = .xy → LabelRecord Label n → X → Label n
  readXYY : (n : ℕ) → pair n = .xy → LabelRecord Label n → Y → Label n
  readXZX : (n : ℕ) → pair n = .xz → LabelRecord Label n → X → Label n
  readXZZ : (n : ℕ) → pair n = .xz → LabelRecord Label n → Z → Label n
  readYZY : (n : ℕ) → pair n = .yz → LabelRecord Label n → Y → Label n
  readYZZ : (n : ℕ) → pair n = .yz → LabelRecord Label n → Z → Label n
  readXYX_readable : ∀ n, n < depth → ∀ (hp : pair n = .xy) (a : A),
    readXYX n hp (labelRecordOf labels n a) (x a) = labels n a
  readXYY_readable : ∀ n, n < depth → ∀ (hp : pair n = .xy) (a : A),
    readXYY n hp (labelRecordOf labels n a) (y a) = labels n a
  readXZX_readable : ∀ n, n < depth → ∀ (hp : pair n = .xz) (a : A),
    readXZX n hp (labelRecordOf labels n a) (x a) = labels n a
  readXZZ_readable : ∀ n, n < depth → ∀ (hp : pair n = .xz) (a : A),
    readXZZ n hp (labelRecordOf labels n a) (z a) = labels n a
  readYZY_readable : ∀ n, n < depth → ∀ (hp : pair n = .yz) (a : A),
    readYZY n hp (labelRecordOf labels n a) (y a) = labels n a
  readYZZ_readable : ∀ n, n < depth → ∀ (hp : pair n = .yz) (a : A),
    readYZZ n hp (labelRecordOf labels n a) (z a) = labels n a

attribute [instance] ReadableHierarchy.fintypeLabel

variable {A : Type u} {X : Type x} {Y : Type y} {Z : Type z}
variable (H : ReadableHierarchy A X Y Z)
variable {Position : Type p} [Fintype Position]

def longX (word : Position → A) : Position → X := fun i => H.x (word i)
def longY (word : Position → A) : Position → Y := fun i => H.y (word i)
def longZ (word : Position → A) : Position → Z := fun i => H.z (word i)

omit [Fintype Position] in
theorem longCoordinates_injective : Function.Injective
    (fun word : Position → A => (longX H word, longY H word, longZ H word)) := by
  intro word other h
  funext i
  apply H.coordinates_injective
  exact Prod.ext (congrFun (congrArg Prod.fst h) i)
    (Prod.ext (congrFun (congrArg (fun q => q.2.1) h) i)
      (congrFun (congrArg (fun q => q.2.2) h) i))

variable [Fintype A] {Prefix : Type q} {counts : A → ℕ} {n t : ℕ}

def Represents (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (prior : Prefix) (u : Position → X) (v : Position → Y) (w : Position → Z)
    (word : Position → A) : Prop :=
  u = longX H word ∧ v = longY H word ∧ w = longZ H word ∧
    ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)

def eligible (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (prior : Prefix) (u : Position → X) (v : Position → Y) (w : Position → Z) : Prop :=
  ∃ word : Position → A, Represents H priorWord prior u v w word

def readXYX (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix) (own : Position → X) : Position → H.Label n :=
  fun i => H.readXYX n hp ((priorWord prior).val i) (own i)

theorem readXYX_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readXYX H priorWord hp prior (longX H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readXYX n hp ((priorWord prior).val i) (H.x (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readXYX_readable n hn hp (word i)

def readXYY (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix) (own : Position → Y) : Position → H.Label n :=
  fun i => H.readXYY n hp ((priorWord prior).val i) (own i)

theorem readXYY_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readXYY H priorWord hp prior (longY H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readXYY n hp ((priorWord prior).val i) (H.y (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readXYY_readable n hn hp (word i)

def readXZX (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix) (own : Position → X) : Position → H.Label n :=
  fun i => H.readXZX n hp ((priorWord prior).val i) (own i)

theorem readXZX_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readXZX H priorWord hp prior (longX H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readXZX n hp ((priorWord prior).val i) (H.x (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readXZX_readable n hn hp (word i)

def readXZZ (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix) (own : Position → Z) : Position → H.Label n :=
  fun i => H.readXZZ n hp ((priorWord prior).val i) (own i)

theorem readXZZ_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readXZZ H priorWord hp prior (longZ H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readXZZ n hp ((priorWord prior).val i) (H.z (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readXZZ_readable n hn hp (word i)

def readYZY (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix) (own : Position → Y) : Position → H.Label n :=
  fun i => H.readYZY n hp ((priorWord prior).val i) (own i)

theorem readYZY_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readYZY H priorWord hp prior (longY H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readYZY n hp ((priorWord prior).val i) (H.y (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readYZY_readable n hn hp (word i)

def readYZZ (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix) (own : Position → Z) : Position → H.Label n :=
  fun i => H.readYZZ n hp ((priorWord prior).val i) (own i)

theorem readYZZ_on_original_word
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix) (word : Position → A)
    (hn : n < H.depth)
    (hprior : ∀ i, (priorWord prior).val i = labelRecordOf H.labels n (word i)) :
    readYZZ H priorWord hp prior (longZ H word) = fun i => H.labels n (word i) := by
  funext i
  change H.readYZZ n hp ((priorWord prior).val i) (H.z (word i)) = H.labels n (word i)
  rw [hprior i]
  exact H.readYZZ_readable n hn hp (word i)

theorem readable_XY
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xy) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (hn : n < H.depth) (h : eligible H priorWord prior u v w) :
    readXYX H priorWord hp prior u =
      readXYY H priorWord hp prior v := by
  obtain ⟨word, hu, hv, hw, hprior⟩ := h
  rw [hu, hv]
  rw [readXYX_on_original_word H priorWord hp prior word hn hprior,
    readXYY_on_original_word H priorWord hp prior word hn hprior]

theorem readable_XZ
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .xz) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (hn : n < H.depth) (h : eligible H priorWord prior u v w) :
    readXZX H priorWord hp prior u =
      readXZZ H priorWord hp prior w := by
  obtain ⟨word, hu, hv, hw, hprior⟩ := h
  rw [hu, hw]
  rw [readXZX_on_original_word H priorWord hp prior word hn hprior,
    readXZZ_on_original_word H priorWord hp prior word hn hprior]

theorem readable_YZ
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position)
    (hp : H.pair n = .yz) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (hn : n < H.depth) (h : eligible H priorWord prior u v w) :
    readYZY H priorWord hp prior v =
      readYZZ H priorWord hp prior w := by
  obtain ⟨word, hu, hv, hw, hprior⟩ := h
  rw [hv, hw]
  rw [readYZY_on_original_word H priorWord hp prior word hn hprior,
    readYZZ_on_original_word H priorWord hp prior word hn hprior]

theorem represented_word_unique
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z) {word other : Position → A}
    (hword : Represents H priorWord prior u v w word)
    (hother : Represents H priorWord prior u v w other) : word = other := by
  apply longCoordinates_injective H
  exact Prod.ext (hword.1.symm.trans hother.1)
    (Prod.ext (hword.2.1.symm.trans hother.2.1)
      (hword.2.2.1.symm.trans hother.2.2.1))

theorem eligible_appendCode_iff
    (old : ExactPrefix counts H.labels n t Position)
    (code : Fin (StageHierarchyResources.stageRefinementCount counts H.labels n t))
    (u : Position → X) (v : Position → Y) (w : Position → Z) :
    eligible H id (appendCode old code) u v w ↔
      ∃ word : Position → A, Represents H id old u v w word ∧
        ((conditionalPoolEquivFin old).symm code).val =
          (fun i => H.labels n (word i)) := by
  constructor
  · rintro ⟨word, hu, hv, hw, hprior⟩
    refine ⟨word, ⟨hu, hv, hw, ?_⟩, ?_⟩
    · intro i
      have hi := hprior i
      change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
        (labelRecordOf H.labels n (word i), H.labels n (word i)) at hi
      exact congrArg Prod.fst hi
    · funext i
      have hi := hprior i
      change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
        (labelRecordOf H.labels n (word i), H.labels n (word i)) at hi
      exact congrArg Prod.snd hi
  · rintro ⟨word, ⟨hu, hv, hw, hprior⟩, hfine⟩
    refine ⟨word, hu, hv, hw, ?_⟩
    intro i
    change (old.val i, ((conditionalPoolEquivFin old).symm code).val i) =
      (labelRecordOf H.labels n (word i), H.labels n (word i))
    exact Prod.ext (hprior i) (congrFun hfine i)

theorem represented_fine_eq
    (priorWord : Prefix → ExactPrefix counts H.labels n t Position) (prior : Prefix)
    (u : Position → X) (v : Position → Y) (w : Position → Z) {word other : Position → A}
    (hword : Represents H priorWord prior u v w word)
    (hother : Represents H priorWord prior u v w other) :
    (fun i => H.labels n (word i)) = (fun i => H.labels n (other i)) := by
  rw [represented_word_unique H priorWord prior u v w hword hother]

theorem eligible_appendCode_iff_of_represents
    (old : ExactPrefix counts H.labels n t Position)
    (code : Fin (StageHierarchyResources.stageRefinementCount counts H.labels n t))
    (u : Position → X) (v : Position → Y) (w : Position → Z) (word : Position → A)
    (hword : Represents H id old u v w word) :
    eligible H id (appendCode old code) u v w ↔
      ((conditionalPoolEquivFin old).symm code).val = (fun i => H.labels n (word i)) := by
  rw [eligible_appendCode_iff]
  constructor
  · rintro ⟨other, hother, hfine⟩
    exact hfine.trans (represented_fine_eq H id old u v w hother hword)
  · intro hfine
    exact ⟨word, hword, hfine⟩

theorem root_eligible_iff
    (old : ExactPrefix counts H.labels 0 t Position)
    (u : Position → X) (v : Position → Y) (w : Position → Z) :
    eligible H id old u v w ↔ ∀ i, ∃ a : A,
      H.x a = u i ∧ H.y a = v i ∧ H.z a = w i := by
  constructor
  · rintro ⟨word, hu, hv, hw, _⟩ i
    refine ⟨word i, ?_, ?_, ?_⟩
    · exact (congrFun hu i).symm
    · exact (congrFun hv i).symm
    · exact (congrFun hw i).symm
  · intro h
    choose word hx hy hz using h
    refine ⟨word, ?_, ?_, ?_, ?_⟩
    · funext i
      exact (hx i).symm
    · funext i
      exact (hy i).symm
    · funext i
      exact (hz i).symm
    · intro i
      exact Subsingleton.elim _ _

def terminalWord (complete : Function.Injective (labelRecordOf H.labels H.depth))
    (last : ExactPrefix counts H.labels H.depth t Position) :
    PopulationWords Position (fun a => t * counts a) := by
  let source := sourcePrefixEquiv counts H.labels H.depth t Position complete last
  refine ⟨source.val, ?_⟩
  intro a
  refine Eq.trans ?_ (source.property a)
  unfold wordPopulation
  exact congrArg
    (fun inst : Fintype {i : Position // source.val i = a} => @Fintype.card _ inst)
    (Subsingleton.elim _ _)

theorem terminalWord_record
    (complete : Function.Injective (labelRecordOf H.labels H.depth))
    (last : ExactPrefix counts H.labels H.depth t Position) (i : Position) :
    labelRecordOf H.labels H.depth ((terminalWord H complete last).val i) = last.val i :=
  sourceSymbol_record last i

theorem terminalWord_of_represents
    (complete : Function.Injective (labelRecordOf H.labels H.depth))
    (last : ExactPrefix counts H.labels H.depth t Position)
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (word : Position → A) (hword : Represents H id last u v w word) :
    (terminalWord H complete last).val = word := by
  funext i
  exact (sourceSymbol_eq_iff complete last i (word i)).2 (hword.2.2.2 i)

theorem terminal_eligible_iff
    (complete : Function.Injective (labelRecordOf H.labels H.depth))
    (last : ExactPrefix counts H.labels H.depth t Position)
    (u : Position → X) (v : Position → Y) (w : Position → Z) :
    eligible H id last u v w ↔
      u = longX H (terminalWord H complete last).val ∧
      v = longY H (terminalWord H complete last).val ∧
      w = longZ H (terminalWord H complete last).val := by
  constructor
  · rintro ⟨word, hword⟩
    rw [terminalWord_of_represents H complete last u v w word hword]
    exact ⟨hword.1, hword.2.1, hword.2.2.1⟩
  · rintro ⟨hu, hv, hw⟩
    refine ⟨(terminalWord H complete last).val, hu, hv, hw, ?_⟩
    intro i
    exact (terminalWord_record H complete last i).symm

end MatrixMultiplication.CompletionHierarchyWords

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_ComplexExecutionPairingBudget
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

namespace MatrixCoordinates

variable {PX PY PZ NX NY NZ : Type*}

theorem scalar_positive : scalar.Positive := by
  exact ⟨Nat.zero_lt_one, Nat.zero_lt_one, Nat.zero_lt_one⟩

end MatrixCoordinates

end MatrixMultiplication.Foundation.ExecutionPairingBudget

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_GeometricValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionGeometricValues

open MatrixMultiplication.Foundation
open CompletionHierarchyWords ConditionalPrefixWords
open ConditionalHierarchyStage PrefixSeparationPolynomialStage PrefixSeparationOrientations
open StageHierarchyResources
open scoped Classical

variable {A X Y Z : Type*} [Fintype A] (H : ReadableHierarchy A X Y Z)
variable {Position : Type*} [Fintype Position] {counts : A → ℕ} {n t : ℕ}

abbrev size (counts : A → ℕ) (n t : ℕ) := stageRefinementCount counts H.labels n t

theorem actualPool_decode (old : ExactPrefix counts H.labels n t Position)
    (code : Fin (size H counts n t)) :
    decodePool (actualPool counts H.labels n t id) (size H counts n t)
      (actualPool_card counts H.labels n t id) old code =
        ((conditionalPoolEquivFin old).symm code).val := rfl

theorem decode_eq_iff_eligible (old : ExactPrefix counts H.labels n t Position)
    (code : Fin (size H counts n t))
    (u : Position → X) (v : Position → Y) (w : Position → Z)
    (word : Position → A) (hword : Represents H id old u v w word) :
    decodePool (actualPool counts H.labels n t id) (size H counts n t)
      (actualPool_card counts H.labels n t id) old code = (fun i => H.labels n (word i)) ↔
        eligible H id (appendCode old code) u v w := by
  rw [actualPool_decode]
  exact (eligible_appendCode_iff_of_represents H old code u v w word hword).symm

theorem raw_XY_normal
    (old : ExactPrefix counts H.labels n t Position) (hn : n < H.depth)
    (hp : H.pair n = .xy)
    (x : (Position → X) × InformedOutput (size H counts n t))
    (y : (Position → Y) × InformedOutput (size H counts n t))
    (z : (Position → Z) × MissingOutput (size H counts n t))
    (word : Position → A) (hword : Represents H id old x.1 y.1 z.1 word) :
    rawPoolLeading (actualPool counts H.labels n t id) (size H counts n t)
      (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
      (readXYX H id hp) (readXYY H id hp) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.xy (size H counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hx : readXYX H id hp old x.1 = fun i => H.labels n (word i) := by
    rw [hword.1]
    exact readXYX_on_original_word H id hp old word hn hword.2.2.2
  have hy : readXYY H id hp old y.1 = fun i => H.labels n (word i) := by
    rw [hword.2.1]
    exact readXYY_on_original_word H id hp old word hn hword.2.2.2
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts H.labels n t id) (size H counts n t)
    (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
    (readXYX H id hp) (readXYY H id hp) (fun _ _ _ _ => fun i => H.labels n (word i))
    old x y z hx hy]
  unfold decodedLeading
  simp only [decode_eq_iff_eligible H old x.2.1 x.1 y.1 z.1 word hword,
    GeometricStageCoordinates.xy_tensor_apply]
  simp only [ite_and]

theorem raw_XZ_normal
    (old : ExactPrefix counts H.labels n t Position) (hn : n < H.depth)
    (hp : H.pair n = .xz)
    (x : (Position → X) × InformedOutput (size H counts n t))
    (y : (Position → Y) × MissingOutput (size H counts n t))
    (z : (Position → Z) × InformedOutput (size H counts n t))
    (word : Position → A) (hword : Represents H id old x.1 y.1 z.1 word) :
    rawPoolLeadingXZ (actualPool counts H.labels n t id) (size H counts n t)
      (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
      (readXZX H id hp) (readXZZ H id hp) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.xz (size H counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hx : readXZX H id hp old x.1 = fun i => H.labels n (word i) := by
    rw [hword.1]
    exact readXZX_on_original_word H id hp old word hn hword.2.2.2
  have hz : readXZZ H id hp old z.1 = fun i => H.labels n (word i) := by
    rw [hword.2.2.1]
    exact readXZZ_on_original_word H id hp old word hn hword.2.2.2
  unfold rawPoolLeadingXZ
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts H.labels n t id) (size H counts n t)
    (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
    (readXZX H id hp) (readXZZ H id hp) (fun _ _ _ _ => fun i => H.labels n (word i))
    old x z y hx hz]
  unfold decodedLeading
  simp only [decode_eq_iff_eligible H old x.2.1 x.1 y.1 z.1 word hword,
    GeometricStageCoordinates.xz_tensor_apply]
  have hswap :
      (x.2.1 = z.2.1 ∧ x.2.1 = y.2.1 ∧
        eligible H id (appendCode old x.2.1) x.1 y.1 z.1 ∧ x.2.2 = z.2.2) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible H id (appendCode old x.2.1) x.1 y.1 z.1 ∧ x.2.2 = z.2.2) :=
    and_left_comm
  simp only [hswap, ite_and]

theorem raw_YZ_normal
    (old : ExactPrefix counts H.labels n t Position) (hn : n < H.depth)
    (hp : H.pair n = .yz)
    (x : (Position → X) × MissingOutput (size H counts n t))
    (y : (Position → Y) × InformedOutput (size H counts n t))
    (z : (Position → Z) × InformedOutput (size H counts n t))
    (word : Position → A) (hword : Represents H id old x.1 y.1 z.1 word) :
    rawPoolLeadingYZ (actualPool counts H.labels n t id) (size H counts n t)
      (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
      (readYZY H id hp) (readYZZ H id hp) old x y z =
        if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode old x.2.1) x.1 y.1 z.1 then
            (GeometricStageCoordinates.yz (size H counts n t)).tensor x.2.2 y.2.2 z.2.2
        else 0 := by
  have hy : readYZY H id hp old y.1 = fun i => H.labels n (word i) := by
    rw [hword.2.1]
    exact readYZY_on_original_word H id hp old word hn hword.2.2.2
  have hz : readYZZ H id hp old z.1 = fun i => H.labels n (word i) := by
    rw [hword.2.2.1]
    exact readYZZ_on_original_word H id hp old word hn hword.2.2.2
  unfold rawPoolLeadingYZ
  rw [rawPoolLeading_eq_decodedLeading
    (actualPool counts H.labels n t id) (size H counts n t)
    (stageRefinementCount_pos counts H.labels n t) (actualPool_card counts H.labels n t id)
    (readYZY H id hp) (readYZZ H id hp) (fun _ _ _ _ => fun i => H.labels n (word i))
    old y z x hy hz]
  have hguard :
      (y.2.1 = z.2.1 ∧ y.2.1 = x.2.1 ∧
        decodePool (actualPool counts H.labels n t id) (size H counts n t)
          (actualPool_card counts H.labels n t id) old y.2.1 = (fun i => H.labels n (word i)) ∧
        y.2.2 = z.2.2) ↔
      (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible H id (appendCode old x.2.1) x.1 y.1 z.1 ∧ y.2.2 = z.2.2) := by
    constructor
    · rintro ⟨hyz, hyx, hdecode, hpair⟩
      refine ⟨hyx.symm, hyx.symm.trans hyz, ?_, hpair⟩
      apply (decode_eq_iff_eligible H old x.2.1 x.1 y.1 z.1 word hword).mp
      simpa only [hyx] using hdecode
    · rintro ⟨hxy, hxz, he, hpair⟩
      refine ⟨hxy.symm.trans hxz, hxy.symm, ?_, hpair⟩
      have hdecode := (decode_eq_iff_eligible H old x.2.1 x.1 y.1 z.1 word hword).mpr he
      simpa only [hxy] using hdecode
  unfold decodedLeading
  simp only [hguard, GeometricStageCoordinates.yz_tensor_apply]
  simp only [ite_and]

end MatrixMultiplication.CompletionGeometricValues

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Execution
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionExecution

open MatrixMultiplication.Foundation CompletionHierarchyWords ConditionalPrefixWords
open PolynomialKernelExecution ExecutionPairingBudget StageHierarchyResources
open scoped BigOperators Classical

variable {A X Y Z : Type} [Fintype A]
variable (H : ReadableHierarchy A X Y Z)

abbrev Prefix (counts : A → ℕ) (t n : ℕ) :=
  ExactPrefix counts H.labels n t (Position counts t)

def support (counts : A → ℕ) (t : ℕ)
    (x : Coordinate X counts t) (y : Coordinate Y counts t)
    (z : Coordinate Z counts t) : Prop :=
  ∀ i, ∃ a : A, H.x a = x i ∧ H.y a = y i ∧ H.z a = z i

def pairingProduct (counts : A → ℕ) (t : ℕ) (pair : ReaderPair) (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if H.pair i = pair then
    stageRefinementCount counts H.labels i t else 1

@[simp] theorem pairingProduct_zero (counts : A → ℕ) (t : ℕ) (pair : ReaderPair) :
    pairingProduct H counts t pair 0 = 1 := by simp [pairingProduct]

theorem pairingProduct_succ (counts : A → ℕ) (t : ℕ) (pair : ReaderPair) (n : ℕ) :
    pairingProduct H counts t pair (n + 1) = pairingProduct H counts t pair n *
      (if H.pair n = pair then stageRefinementCount counts H.labels n t else 1) := by
  simp only [pairingProduct, Finset.prod_range_succ]

def prefixValue {PX PY PZ : Type*} (counts : A → ℕ) (t n : ℕ)
    (pairing : Tensor ℂ PX PY PZ) :
    Tensor ℂ (Coordinate X counts t × (Prefix H counts t n × PX))
      (Coordinate Y counts t × (Prefix H counts t n × PY))
      (Coordinate Z counts t × (Prefix H counts t n × PZ)) :=
  fun x y z => if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
      eligible H id x.2.1 x.1 y.1 z.1 then pairing x.2.2 y.2.2 z.2.2 else 0

structure Bundle (counts : A → ℕ) (t n : ℕ) where
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
  execution : Execution (Coordinate X counts t) (Coordinate Y counts t) (Coordinate Z counts t)
    (Prefix H counts t n) PX PY PZ AX AY AZ
      (support H counts t)
  shape : MatrixCoordinates PX PY PZ
  shape_positive : shape.Positive
  normal : execution.value = prefixValue H counts t n shape.tensor
  rank_exact : execution.rankBound = stageAuxiliaryBudget counts H.labels n t
  volume_exact : shape.volume = stagePairingProduct counts H.labels n t
  rows_exact : shape.rows = pairingProduct H counts t .xz n
  inner_exact : shape.inner = pairingProduct H counts t .xy n
  columns_exact : shape.columns = pairingProduct H counts t .yz n
  pairing_budget : shape.volume ≤ execution.rankBound

attribute [instance] Bundle.finitePX Bundle.finitePY Bundle.finitePZ
attribute [instance] Bundle.finiteAX Bundle.finiteAY Bundle.finiteAZ

def scalarAuxiliary : Tensor ℂ PUnit PUnit PUnit := fun _ _ _ => 1

theorem scalarAuxiliary_rank : Tensor.RankAtMost scalarAuxiliary 1 := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, ?_⟩
  funext x y z
  simp [scalarAuxiliary, Tensor.rankOne]

def initial (counts : A → ℕ) (t : ℕ) : Bundle H counts t 0 := by
  let E : Execution (Coordinate X counts t) (Coordinate Y counts t)
      (Coordinate Z counts t) (Prefix H counts t 0) PUnit PUnit PUnit
      PUnit PUnit PUnit (support H counts t) := {
    auxiliary := scalarAuxiliary
    rankBound := 1
    auxiliary_rank := scalarAuxiliary_rank
    order := 0
    leftDegree := 0
    middleDegree := 0
    rightDegree := 0
    leftMap := fun _ _ _ => 1
    middleMap := fun _ _ _ => 1
    rightMap := fun _ _ _ => 1
    left_degree := by intros; simp
    middle_degree := by intros; simp
    right_degree := by intros; simp
    value := prefixValue H counts t 0 MatrixCoordinates.scalar.tensor
    vanishes := by intro _ _ _ _ j hj; omega
    leading := by
      intro x y z hs
      have hxy : x.2.1 = y.2.1 := Subsingleton.elim _ _
      have hxz : x.2.1 = z.2.1 := Subsingleton.elim _ _
      have he : eligible H id x.2.1 x.1 y.1 z.1 :=
        (root_eligible_iff H x.2.1 x.1 y.1 z.1).mpr hs
      change _ = (if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible H id x.2.1 x.1 y.1 z.1 then
          MatrixCoordinates.scalar.tensor x.2.2 y.2.2 z.2.2 else 0)
      rw [ite_eq_left ⟨hxy, hxz, he⟩, MatrixCoordinates.scalar_tensor]
      simp [PolynomialLocalConstruction.kernel, LocalMaps.fiberTransform, scalarAuxiliary]
    synchronized := by intro _ _ _ _ _; exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  }
  exact {
    PX := PUnit
    PY := PUnit
    PZ := PUnit
    AX := PUnit
    AY := PUnit
    AZ := PUnit
    execution := E
    shape := MatrixCoordinates.scalar
    shape_positive := MatrixCoordinates.scalar_positive
    normal := rfl
    rank_exact := by simp [E, stageAuxiliaryBudget]
    volume_exact := by simp [stagePairingProduct]
    rows_exact := by simp [MatrixCoordinates.scalar]
    inner_exact := by simp [MatrixCoordinates.scalar]
    columns_exact := by simp [MatrixCoordinates.scalar]
    pairing_budget := le_rfl
  }

variable {H}

theorem previous_eligible {counts : A → ℕ} {t n : ℕ} (B : Bundle H counts t n)
    (x : Coordinate X counts t × (Prefix H counts t n × B.PX))
    (y : Coordinate Y counts t × (Prefix H counts t n × B.PY))
    (z : Coordinate Z counts t × (Prefix H counts t n × B.PZ))
    (_hs : support H counts t x.1 y.1 z.1)
    (hn : B.execution.value x y z ≠ 0) : eligible H id x.2.1 x.1 y.1 z.1 := by
  rw [B.normal] at hn
  by_contra h
  exact hn (by simp [prefixValue, h])

section Successor

variable {counts : A → ℕ} {t n : ℕ} (B : Bundle H counts t n)
variable {NX NY NZ BX BY BZ : Type}
variable [Fintype BX] [Fintype BY] [Fintype BZ]

def refinedExecution
    (S : Stage B.execution (Fin (stageRefinementCount counts H.labels n t))
      NX NY NZ BX BY BZ) :
    Execution (Coordinate X counts t) (Coordinate Y counts t) (Coordinate Z counts t)
      (Prefix H counts t (n + 1)) (B.PX × NX) (B.PY × NY) (B.PZ × NZ)
      (B.AX × BX) (B.AY × BY) (B.AZ × BZ)
      (support H counts t) :=
  (B.execution.step S).reindexOutput
    (nextPrefixEquiv counts H.labels n t (Position counts t))
    (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

theorem refinedExecution_normal
    (S : Stage B.execution (Fin (stageRefinementCount counts H.labels n t))
      NX NY NZ BX BY BZ)
    (shape : MatrixCoordinates NX NY NZ)
    (hstage : ∀ p x y z, eligible H id p x.1 y.1 z.1 →
      S.value p x y z = if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode p x.2.1) x.1 y.1 z.1
        then shape.tensor x.2.2 y.2.2 z.2.2 else 0) :
    (refinedExecution B S).value =
      prefixValue H counts t (n + 1) (B.shape.product shape).tensor := by
  classical
  funext x y z
  let e := nextPrefixEquiv counts H.labels n t (Position counts t)
  let px := e x.2.1
  let py := e y.2.1
  let pz := e z.2.1
  have hdecode (p : Prefix H counts t (n + 1)) :
      appendCode (e p).1 (e p).2 = p := e.symm_apply_apply p
  change B.execution.value (x.1, (px.1, x.2.2.1))
      (y.1, (py.1, y.2.2.1)) (z.1, (pz.1, z.2.2.1)) *
    S.value px.1 (x.1, (px.2, x.2.2.2))
      (y.1, (py.2, y.2.2.2)) (z.1, (pz.2, z.2.2.2)) = _
  rw [B.normal]
  simp only [prefixValue]
  by_cases hold : px.1 = py.1 ∧ px.1 = pz.1 ∧ eligible H id px.1 x.1 y.1 z.1
  · rw [ite_eq_left hold]
    have hguard :
        (px.2 = py.2 ∧ px.2 = pz.2 ∧ eligible H id (appendCode px.1 px.2) x.1 y.1 z.1) ↔
        (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧ eligible H id x.2.1 x.1 y.1 z.1) := by
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
        eligible H id x.2.1 x.1 y.1 z.1) := by
      rintro ⟨hxy, hxz, he⟩
      apply hold
      refine ⟨congrArg (fun p => (e p).1) hxy,
        congrArg (fun p => (e p).1) hxz, ?_⟩
      rw [← hdecode x.2.1] at he
      obtain ⟨word, hw, _⟩ :=
        (eligible_appendCode_iff H px.1 px.2 x.1 y.1 z.1).mp he
      exact ⟨word, hw⟩
    rw [ite_eq_right hold, ite_eq_right hnext, zero_mul]

def extendBundle [Fintype NX] [Fintype NY] [Fintype NZ]
    (S : Stage B.execution (Fin (stageRefinementCount counts H.labels n t))
      NX NY NZ BX BY BZ)
    (shape : MatrixCoordinates NX NY NZ) (hpositive : shape.Positive)
    (hvolume : shape.volume = stageRefinementCount counts H.labels n t)
    (hrank : S.rankBound = stageCost counts H.labels n t)
    (hrows : shape.rows = if H.pair n = .xz then
      stageRefinementCount counts H.labels n t else 1)
    (hinner : shape.inner = if H.pair n = .xy then
      stageRefinementCount counts H.labels n t else 1)
    (hcolumns : shape.columns = if H.pair n = .yz then
      stageRefinementCount counts H.labels n t else 1)
    (hstage : ∀ p x y z, eligible H id p x.1 y.1 z.1 →
      S.value p x y z = if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
          eligible H id (appendCode p x.2.1) x.1 y.1 z.1
        then shape.tensor x.2.2 y.2.2 z.2.2 else 0) : Bundle H counts t (n + 1) where
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
    change B.execution.rankBound * S.rankBound = _
    rw [B.rank_exact, hrank, stageAuxiliaryBudget_succ]
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

variable {counts : A → ℕ} {t n : ℕ}

def extendXY (B : Bundle H counts t n) (hn : n < H.depth)
    (hpair : H.pair n = .xy) : Bundle H counts t (n + 1) := Classical.choice (by
  have hagree : ∀ (p : Prefix H counts t n)
      (x : Coordinate X counts t) (y : Coordinate Y counts t)
      (z : Coordinate Z counts t), eligible H id p x y z →
      readXYX H id hpair p x = readXYY H id hpair p y := by
    intro p x y z he
    exact readable_XY H id hpair p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    ConditionalHierarchyStage.exists_actualPoolStage counts H.labels n t B.execution id
      (readXYX H id hpair) (readXYY H id hpair)
      (eligible H id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.xy _)
    (GeometricStageCoordinates.xy_positive (stageRefinementCount_pos counts H.labels n t))
    (GeometricStageCoordinates.xy_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.xy])
    (by simp [hpair, GeometricStageCoordinates.xy])
    (by simp [hpair, GeometricStageCoordinates.xy]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CompletionGeometricValues.raw_XY_normal H p hn hpair x y z word hw)

def extendXZ (B : Bundle H counts t n) (hn : n < H.depth)
    (hpair : H.pair n = .xz) : Bundle H counts t (n + 1) := Classical.choice (by
  have hagree : ∀ (p : Prefix H counts t n)
      (x : Coordinate X counts t) (y : Coordinate Y counts t)
      (z : Coordinate Z counts t), eligible H id p x y z →
      readXZX H id hpair p x = readXZZ H id hpair p z := by
    intro p x y z he
    exact readable_XZ H id hpair p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    OrientedConditionalHierarchyStage.exists_actualPoolStage_XZ counts H.labels n t B.execution id
      (readXZX H id hpair) (readXZZ H id hpair)
      (eligible H id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.xz _)
    (GeometricStageCoordinates.xz_positive (stageRefinementCount_pos counts H.labels n t))
    (GeometricStageCoordinates.xz_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.xz])
    (by simp [hpair, GeometricStageCoordinates.xz])
    (by simp [hpair, GeometricStageCoordinates.xz]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CompletionGeometricValues.raw_XZ_normal H p hn hpair x y z word hw)

def extendYZ (B : Bundle H counts t n) (hn : n < H.depth)
    (hpair : H.pair n = .yz) : Bundle H counts t (n + 1) := Classical.choice (by
  have hagree : ∀ (p : Prefix H counts t n)
      (x : Coordinate X counts t) (y : Coordinate Y counts t)
      (z : Coordinate Z counts t), eligible H id p x y z →
      readYZY H id hpair p y = readYZZ H id hpair p z := by
    intro p x y z he
    exact readable_YZ H id hpair p x y z hn he
  obtain ⟨S, _, hrank, _, _, _, _, hvalue⟩ :=
    OrientedConditionalHierarchyStage.exists_actualPoolStage_YZ counts H.labels n t B.execution id
      (readYZY H id hpair) (readYZZ H id hpair)
      (eligible H id) (previous_eligible B) hagree
  refine ⟨extendBundle B S (GeometricStageCoordinates.yz _)
    (GeometricStageCoordinates.yz_positive (stageRefinementCount_pos counts H.labels n t))
    (GeometricStageCoordinates.yz_volume _) hrank
    (by simp [hpair, GeometricStageCoordinates.yz])
    (by simp [hpair, GeometricStageCoordinates.yz])
    (by simp [hpair, GeometricStageCoordinates.yz]) ?_⟩
  intro p x y z he
  rw [hvalue]
  obtain ⟨word, hw⟩ := he
  exact CompletionGeometricValues.raw_YZ_normal H p hn hpair x y z word hw)

def extend (B : Bundle H counts t n) (hn : n < H.depth) :
    Bundle H counts t (n + 1) :=
  match hp : H.pair n with
  | .xy => extendXY B hn hp
  | .xz => extendXZ B hn hp
  | .yz => extendYZ B hn hp

end ConcreteStages

variable (H)

def run (counts : A → ℕ) (t : ℕ) : (n : ℕ) → n ≤ H.depth → Bundle H counts t n
  | 0, _ => initial H counts t
  | n + 1, hn => extend (run counts t n (by omega)) (by omega)

def realize (counts : A → ℕ) (t : ℕ) : Bundle H counts t H.depth :=
  run H counts t H.depth le_rfl

theorem realize_dimensions (counts : A → ℕ) (t : ℕ) :
    (realize H counts t).shape.rows =
        ConditionalLabels.stagePairingSize counts H.labels H.depth
          (fun n => H.pair n.val) .xz t ∧
    (realize H counts t).shape.inner =
        ConditionalLabels.stagePairingSize counts H.labels H.depth
          (fun n => H.pair n.val) .xy t ∧
    (realize H counts t).shape.columns =
        ConditionalLabels.stagePairingSize counts H.labels H.depth
          (fun n => H.pair n.val) .yz t := by
  have h (pair : ReaderPair) : pairingProduct H counts t pair H.depth =
      ConditionalLabels.stagePairingSize counts H.labels H.depth
        (fun n => H.pair n.val) pair t := by
    simp only [pairingProduct, ConditionalLabels.stagePairingSize,
      ConditionalLabels.pairingSize, ← Fin.prod_univ_eq_prod_range]
  exact ⟨(realize H counts t).rows_exact.trans (h .xz),
    (realize H counts t).inner_exact.trans (h .xy),
    (realize H counts t).columns_exact.trans (h .yz)⟩

theorem realize_rankBound (counts : A → ℕ) (t : ℕ) :
    (realize H counts t).execution.rankBound =
      stageAuxiliaryBudget counts H.labels H.depth t :=
  (realize H counts t).rank_exact

theorem realize_volume (counts : A → ℕ) (t : ℕ)
    (complete : Function.Injective (labelRecordOf H.labels H.depth)) :
    (realize H counts t).shape.volume =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [(realize H counts t).volume_exact]
  exact stagePairingProduct_eq_exactWords_card counts H.labels H.depth complete t

theorem realize_label_card (counts : A → ℕ) (t : ℕ)
    (complete : Function.Injective (labelRecordOf H.labels H.depth)) :
    Fintype.card (Prefix H counts t H.depth) =
      Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [exactWords_card]
  calc
    Fintype.card (Prefix H counts t H.depth) =
        Fintype.card (PopulationWords (Position counts t) (fun a => t * counts a)) :=
      Fintype.card_congr
        (sourcePrefixEquiv counts H.labels H.depth t (Position counts t) complete)
    _ = Nat.multinomial Finset.univ (fun a => t * counts a) :=
      populationWords_card (I := Position counts t)
        (fun a => t * counts a) (position_card counts t)

end MatrixMultiplication.CompletionExecution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ComplexFiniteMMRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.Foundation

structure FiniteMMRealization where
  occurrences : ℕ
  multiplicity : ℕ
  auxiliaryRank : ℕ
  rows : ℕ
  inner : ℕ
  columns : ℕ
  occurrences_pos : 0 < occurrences
  multiplicity_pos : 0 < multiplicity
  auxiliaryRank_pos : 0 < auxiliaryRank
  rows_pos : 0 < rows
  inner_pos : 0 < inner
  columns_pos : 0 < columns
  order : ℕ
  degree : ℕ
  approximation : Tensor.PolynomialApproximation
    (Tensor.directSum (fun _ : Fin multiplicity =>
      Tensor.matrixMultiplication rows inner columns))
    (3 ^ occurrences * auxiliaryRank) order degree

end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Separation_ExecutionApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite type counts, hierarchy separation and tensor execution bounds. -/

noncomputable section

namespace MatrixMultiplication.ExecutionApproximation

open MatrixMultiplication.Foundation
open _root_.OAI.MatrixMultiplication.Foundation.Tensor LocalMaps PolynomialLocalConstruction PolynomialKernelExecution

variable {X Y Z Prefix PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)

theorem polynomial_substitution (original : Tensor ℂ X Y Z) :
    fiberTransform E.leftMap E.middleMap E.rightMap
      (fun x y z => Polynomial.C (Tensor.product original E.auxiliary x y z)) =
      originalScale (fun x y z => Polynomial.C (original x y z))
        (kernel E.auxiliary E.leftMap E.middleMap E.rightMap) := by
  have h := fiberTransform_originalScale E.leftMap E.middleMap E.rightMap
    (fun x y z => Polynomial.C (original x y z))
    (fun x y z => Polynomial.C (E.auxiliary x.2 y.2 z.2))
  have hinput :
      (fun x y z => Polynomial.C (Tensor.product original E.auxiliary x y z)) =
        originalScale (fun x y z => Polynomial.C (original x y z))
          (fun x y z => Polynomial.C (E.auxiliary x.2 y.2 z.2)) := by
    funext x y z
    simp only [Tensor.product, originalScale, map_mul]
  rw [hinput]
  simpa only [kernel] using h

variable [Fintype X] [Fintype Y] [Fintype Z]

def degeneration (original : Tensor ℂ X Y Z)
    (supported : ∀ x y z, ¬ support x y z → original x y z = 0) :
    PolynomialRestrictionDegeneration (Tensor.product original E.auxiliary)
      (originalScale original E.value) E.order E.leftDegree E.middleDegree E.rightDegree := by
  classical
  refine {
    leftMap := fiberMatrix E.leftMap
    middleMap := fiberMatrix E.middleMap
    rightMap := fiberMatrix E.rightMap
    left_degree := ?_
    middle_degree := ?_
    right_degree := ?_
    vanishes := ?_
    leading := ?_
  }
  · intro x i
    by_cases h : x.1 = i.1
    · simpa only [fiberMatrix, ite_eq_left h] using E.left_degree x.1 x.2 i.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro y j
    by_cases h : y.1 = j.1
    · simpa only [fiberMatrix, ite_eq_left h] using E.middle_degree y.1 y.2 j.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro z k
    by_cases h : z.1 = k.1
    · simpa only [fiberMatrix, ite_eq_left h] using E.right_degree z.1 z.2 k.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro x y z j hj
    rw [← fiberTransform_eq_restrict, polynomial_substitution E original]
    simp only [originalScale, Polynomial.coeff_C_mul]
    by_cases hs : support x.1 y.1 z.1
    · rw [E.vanishes x y z hs j hj, mul_zero]
    · rw [supported x.1 y.1 z.1 hs, zero_mul]
  · intro x y z
    rw [← fiberTransform_eq_restrict, polynomial_substitution E original]
    simp only [originalScale, Polynomial.coeff_C_mul]
    by_cases hs : support x.1 y.1 z.1
    · rw [E.leading x y z hs]
    · rw [supported x.1 y.1 z.1 hs]
      simp only [zero_mul]

def approximation {original : Tensor ℂ X Y Z} {r d D : ℕ}
    (source : PolynomialApproximation original r d D)
    (supported : ∀ x y z, ¬ support x y z → original x y z = 0) :
    PolynomialApproximation (originalScale original E.value)
      (r * E.rankBound) (d * (E.order + 1) + E.order)
      (D * (E.order + 1) + E.leftDegree + E.middleDegree + E.rightDegree) := by
  have combined := source.productExact E.auxiliary E.rankBound E.auxiliary_rank
  exact (degeneration E original supported).compose combined

end MatrixMultiplication.ExecutionApproximation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_FiniteRealization
attribute [-simp] _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial
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

open CompletionHierarchyWords CompletionExecution ExecutionPairingBudget

variable {A X Y Z : Type} [Fintype A]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ) (t : ℕ)

def copies : ℕ := Fintype.card (Prefix H counts t H.depth)

def rows : ℕ := (realize H counts t).shape.rows
def inner : ℕ := (realize H counts t).shape.inner
def columns : ℕ := (realize H counts t).shape.columns

def order (d : ℕ) : ℕ :=
  d * blocks counts t * ((realize H counts t).execution.order + 1) +
    (realize H counts t).execution.order

def degree (D : ℕ) : ℕ :=
  D * blocks counts t * ((realize H counts t).execution.order + 1) +
    (realize H counts t).execution.leftDegree +
    (realize H counts t).execution.middleDegree +
    (realize H counts t).execution.rightDegree

def labelEquiv : Fin (copies H counts t) ≃ Prefix H counts t H.depth :=
  (Fintype.equivFin _).symm

variable (complete : Function.Injective (labelRecordOf H.labels H.depth))

def designatedX (p : Prefix H counts t H.depth) : Coordinate X counts t :=
  longX H (terminalWord H complete p).val

def designatedY (p : Prefix H counts t H.depth) : Coordinate Y counts t :=
  longY H (terminalWord H complete p).val

def designatedZ (p : Prefix H counts t H.depth) : Coordinate Z counts t :=
  longZ H (terminalWord H complete p).val

theorem leading_shape
    (x : Coordinate X counts t × (Prefix H counts t H.depth × (realize H counts t).PX))
    (y : Coordinate Y counts t × (Prefix H counts t H.depth × (realize H counts t).PY))
    (z : Coordinate Z counts t × (Prefix H counts t H.depth × (realize H counts t).PZ)) :
    (realize H counts t).execution.value x y z =
      if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        x.1 = designatedX H counts t complete x.2.1 ∧
        y.1 = designatedY H counts t complete x.2.1 ∧
        z.1 = designatedZ H counts t complete x.2.1
      then (realize H counts t).shape.tensor x.2.2 y.2.2 z.2.2 else 0 := by
  rw [(realize H counts t).normal]
  simp only [prefixValue, terminal_eligible_iff H complete,
    designatedX, designatedY, designatedZ]
  rfl

def leftSelect
    (u : Fin (copies H counts t) × (Fin (rows H counts t) × Fin (inner H counts t))) :
    Coordinate X counts t × (Prefix H counts t H.depth × (realize H counts t).PX) :=
  (designatedX H counts t complete (labelEquiv H counts t u.1),
    (labelEquiv H counts t u.1, (realize H counts t).shape.left.symm u.2))

def middleSelect
    (v : Fin (copies H counts t) × (Fin (inner H counts t) × Fin (columns H counts t))) :
    Coordinate Y counts t × (Prefix H counts t H.depth × (realize H counts t).PY) :=
  (designatedY H counts t complete (labelEquiv H counts t v.1),
    (labelEquiv H counts t v.1, (realize H counts t).shape.middle.symm v.2))

def rightSelect
    (w : Fin (copies H counts t) × (Fin (columns H counts t) × Fin (rows H counts t))) :
    Coordinate Z counts t × (Prefix H counts t H.depth × (realize H counts t).PZ) :=
  (designatedZ H counts t complete (labelEquiv H counts t w.1),
    (labelEquiv H counts t w.1, (realize H counts t).shape.right.symm w.2))

theorem designated_coefficient_one (T : Tensor ℂ X Y Z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)
    (p : Prefix H counts t H.depth) :
    Tensor.power T (blocks counts t) (designatedX H counts t complete p)
      (designatedY H counts t complete p) (designatedZ H counts t complete p) = 1 := by
  apply Finset.prod_eq_one
  intro i _
  exact unit ((terminalWord H complete p).val i)

theorem selected_output (T : Tensor ℂ X Y Z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1) :
    Tensor.pullback (leftSelect H counts t complete) (middleSelect H counts t complete)
      (rightSelect H counts t complete)
      (LocalMaps.originalScale (Tensor.power T (blocks counts t))
        (realize H counts t).execution.value) =
      Tensor.directSum (fun _ : Fin (copies H counts t) =>
        Tensor.matrixMultiplication (rows H counts t) (inner H counts t) (columns H counts t)) := by
  funext u v w
  simp only [Tensor.pullback, LocalMaps.originalScale, leftSelect, middleSelect, rightSelect]
  rw [leading_shape H counts t complete]
  simp only [MatrixCoordinates.tensor, Tensor.pullback]
  by_cases h : u.1 = v.1 ∧ u.1 = w.1
  · have hv : v.1 = u.1 := h.1.symm
    have hw : w.1 = u.1 := h.2.symm
    simp only [hv, hw, designated_coefficient_one H counts t complete T unit,
      Tensor.directSum, true_and, ite_true, if_true, one_mul,
      Tensor.matrixMultiplication_eq_matrixCoefficients, rows, inner, columns]
    rw [(realize H counts t).shape.left.apply_symm_apply u.2,
      (realize H counts t).shape.middle.apply_symm_apply v.2,
      (realize H counts t).shape.right.apply_symm_apply w.2]
  · have hn : ¬ (labelEquiv H counts t u.1 = labelEquiv H counts t v.1 ∧
        labelEquiv H counts t u.1 = labelEquiv H counts t w.1 ∧
        True ∧
        designatedY H counts t complete (labelEquiv H counts t v.1) =
          designatedY H counts t complete (labelEquiv H counts t u.1) ∧
        designatedZ H counts t complete (labelEquiv H counts t w.1) =
          designatedZ H counts t complete (labelEquiv H counts t u.1)) := by
      intro he
      exact h ⟨(labelEquiv H counts t).injective he.1,
        (labelEquiv H counts t).injective he.2.1⟩
    simp only [Tensor.directSum, ite_eq_right h, ite_eq_right hn, mul_zero]

theorem dimensions_positive :
    0 < rows H counts t ∧ 0 < inner H counts t ∧ 0 < columns H counts t :=
  (realize H counts t).shape_positive

include complete in
theorem volume_eq_copies :
    rows H counts t * inner H counts t * columns H counts t = copies H counts t :=
  (realize_volume H counts t complete).trans (realize_label_card H counts t complete).symm

include complete in
theorem copies_pos : 0 < copies H counts t := by
  rw [← volume_eq_copies H counts t complete]
  exact Nat.mul_pos (Nat.mul_pos (dimensions_positive H counts t).1
    (dimensions_positive H counts t).2.1) (dimensions_positive H counts t).2.2

theorem auxiliaryRank_pos : 0 < (realize H counts t).execution.rankBound :=
  lt_of_lt_of_le
    (Nat.mul_pos (Nat.mul_pos (dimensions_positive H counts t).1
      (dimensions_positive H counts t).2.1) (dimensions_positive H counts t).2.2)
    (realize H counts t).pairing_budget

variable [Fintype X] [Fintype Y] [Fintype Z]

def sourceApproximation {T : Tensor ℂ X Y Z} {factors d D : ℕ}
    (source : Tensor.PolynomialApproximation T (3 ^ factors) d D) :
    Tensor.PolynomialApproximation (Tensor.power T (blocks counts t))
      (3 ^ (factors * blocks counts t)) (d * blocks counts t) (D * blocks counts t) := by
  simpa only [pow_mul] using source.power (blocks counts t)

def approximation {T : Tensor ℂ X Y Z} {factors d D : ℕ}
    (source : Tensor.PolynomialApproximation T (3 ^ factors) d D)
    (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1) :
    Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin (copies H counts t) =>
        Tensor.matrixMultiplication (rows H counts t) (inner H counts t) (columns H counts t)))
      (3 ^ (factors * blocks counts t) * (realize H counts t).execution.rankBound)
      (order H counts t d) (degree H counts t D) := by
  have hs : ∀ x y z, ¬ support H counts t x y z →
      Tensor.power T (blocks counts t) x y z = 0 := by
    intro x y z outside
    by_contra nonzero
    apply outside
    intro i
    exact supported _ _ _ ((Finset.prod_ne_zero_iff.mp nonzero) i (Finset.mem_univ i))
  have full := ExecutionApproximation.approximation (realize H counts t).execution
    (sourceApproximation counts t source) hs
  have selected := full.pullback (leftSelect H counts t complete)
    (middleSelect H counts t complete) (rightSelect H counts t complete)
  rw [selected_output H counts t complete T unit] at selected
  exact selected

def realization {T : Tensor ℂ X Y Z} {factors d D : ℕ}
    (source : Tensor.PolynomialApproximation T (3 ^ factors) d D)
    (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)
    (factors_pos : 0 < factors) (blocks_pos : 0 < blocks counts t) : FiniteMMRealization where
  occurrences := factors * blocks counts t
  multiplicity := copies H counts t
  auxiliaryRank := (realize H counts t).execution.rankBound
  rows := rows H counts t
  inner := inner H counts t
  columns := columns H counts t
  occurrences_pos := Nat.mul_pos factors_pos blocks_pos
  multiplicity_pos := copies_pos H counts t complete
  auxiliaryRank_pos := auxiliaryRank_pos H counts t
  rows_pos := (dimensions_positive H counts t).1
  inner_pos := (dimensions_positive H counts t).2.1
  columns_pos := (dimensions_positive H counts t).2.2
  order := order H counts t d
  degree := degree H counts t D
  approximation := approximation H counts t complete source supported unit

section Projections

variable {T : Tensor ℂ X Y Z} {factors d D : ℕ}
variable (source : Tensor.PolynomialApproximation T (3 ^ factors) d D)
variable (supported : ∀ x y z, T x y z ≠ 0 →
  ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)
variable (factors_pos : 0 < factors) (blocks_pos : 0 < blocks counts t)

@[simp] theorem realization_occurrences :
    (realization H counts t complete source supported unit factors_pos blocks_pos).occurrences =
      factors * blocks counts t := rfl

@[simp] theorem realization_multiplicity :
    (realization H counts t complete source supported unit factors_pos blocks_pos).multiplicity =
      copies H counts t := rfl

@[simp] theorem realization_auxiliaryRank :
    (realization H counts t complete source supported unit factors_pos blocks_pos).auxiliaryRank =
      StageHierarchyResources.stageAuxiliaryBudget counts H.labels H.depth t :=
  realize_rankBound H counts t

@[simp] theorem realization_rows :
    (realization H counts t complete source supported unit factors_pos blocks_pos).rows =
      rows H counts t := rfl

@[simp] theorem realization_inner :
    (realization H counts t complete source supported unit factors_pos blocks_pos).inner =
      inner H counts t := rfl

@[simp] theorem realization_columns :
    (realization H counts t complete source supported unit factors_pos blocks_pos).columns =
      columns H counts t := rfl

end Projections

end MatrixMultiplication.CompletionFiniteRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_HierarchyPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionHierarchyWords

open MatrixMultiplication.Foundation

universe u v p q

variable {A : Type u}

namespace ReadableHierarchy

open RecursiveCompletion CompletionLabels.TopologicalFlatten

def ofProgram {Coord : Color → Type v} {Context : Type q} {Code : Type p}
    [Fintype Code] {depth : ℕ} (s : Program A Coord Context Code depth)
    (ctx : Context) (hctx : ∀ a, s.context a = ctx)
    (joint : Function.Injective (fun a => (s.view .B a, s.view .C a, s.view .A a))) :
    ReadableHierarchy A (Coord .B) (Coord .C) (Coord .A) where
  Label := fun _ => Code
  fintypeLabel := fun _ => inferInstance
  labels := s.labels
  depth := depth
  pair := s.pair
  x := s.view .B
  y := s.view .C
  z := s.view .A
  coordinates_injective := joint
  readXYX n _ prior own := s.read n .B ctx (Program.recordArray n prior) own
  readXYY n _ prior own := s.read n .C ctx (Program.recordArray n prior) own
  readXZX n _ prior own := s.read n .B ctx (Program.recordArray n prior) own
  readXZZ n _ prior own := s.read n .A ctx (Program.recordArray n prior) own
  readYZY n _ prior own := s.read n .C ctx (Program.recordArray n prior) own
  readYZZ n _ prior own := s.read n .A ctx (Program.recordArray n prior) own
  readXYX_readable n hn hp a := by
    change s.read n .B ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .B a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .B (Or.inl (by simp only [hp, firstSide]))
  readXYY_readable n hn hp a := by
    change s.read n .C ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .C a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .C (Or.inr (by simp only [hp, secondSide]))
  readXZX_readable n hn hp a := by
    change s.read n .B ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .B a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .B (Or.inl (by simp only [hp, firstSide]))
  readXZZ_readable n hn hp a := by
    change s.read n .A ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .A a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .A (Or.inr (by simp only [hp, secondSide]))
  readYZY_readable n hn hp a := by
    change s.read n .C ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .C a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .C (Or.inl (by simp only [hp, firstSide]))
  readYZZ_readable n hn hp a := by
    change s.read n .A ctx (Program.recordArray n (labelRecordOf s.labels n a))
      (s.view .A a) = s.labels n a
    rw [Program.recordArray_labelRecordOf, ← hctx a]
    exact s.readable n hn a .A (Or.inr (by simp only [hp, secondSide]))

end ReadableHierarchy

end MatrixMultiplication.CompletionHierarchyWords

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Partitions
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionLabels.leafFintype _root_.OAI.MatrixMultiplication.CompletionLabels.retainedLeafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionPartitions

open MatrixMultiplication.Foundation RecursiveCompletion
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type*} [Fintype X]

def activeCount (S : FlaggedTensor X Y Z) : ℕ := Fintype.card {x // S.flagB x}
def inactiveCount (S : FlaggedTensor X Y Z) : ℕ := Fintype.card {x // ¬ S.flagB x}

def activeFraction (S : FlaggedTensor X Y Z) : ℝ :=
  (activeCount S : ℝ) / Fintype.card X

def inactiveFraction (S : FlaggedTensor X Y Z) : ℝ :=
  (inactiveCount S : ℝ) / Fintype.card X

end MatrixMultiplication.CompletionPartitions

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_Termination
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.step_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionTermination

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
attribute [local instance] Classical.propDecidable Classical.decEq

universe uCoord
variable {X Y Z : Type uCoord}

def tensor (S : FlaggedTensor X Y Z) (deleted : Color) : Tensor ℂ X Y Z :=
  fun x y z => if ownerFlag S deleted (coordinate (x, y, z) deleted) then 0
    else S.tensor x y z

theorem support_iff (S : FlaggedTensor X Y Z) (deleted : Color) (x y z) :
    tensor S deleted x y z ≠ 0 ↔ S.tensor x y z ≠ 0 ∧
      ¬ ownerFlag S deleted (coordinate (x, y, z) deleted) := by
  by_cases h : ownerFlag S deleted (coordinate (x, y, z) deleted) <;>
    simp [tensor, h]

def leftMap (S : FlaggedTensor X Y Z) (deleted : Color) : X → X → ℂ :=
  diagonalMap (fun x => if deleted = .B ∧ S.flagB x then 0 else 1)

def middleMap (S : FlaggedTensor X Y Z) (deleted : Color) : Y → Y → ℂ :=
  diagonalMap (fun y => if deleted = .C ∧ S.flagC y then 0 else 1)

def rightMap (S : FlaggedTensor X Y Z) (deleted : Color) : Z → Z → ℂ :=
  diagonalMap (fun z => if deleted = .A ∧ S.flagA z then 0 else 1)

variable [Fintype X] [Fintype Y] [Fintype Z]

theorem restriction (S : FlaggedTensor X Y Z) (deleted : Color) :
    Tensor.restrict (leftMap S deleted) (middleMap S deleted) (rightMap S deleted)
      S.tensor = tensor S deleted := by
  funext x y z
  rw [leftMap, middleMap, rightMap, restrict_diagonal]
  cases deleted <;> simp [tensor, ownerFlag, coordinate, ite_mul, reduceCtorEq] <;> rfl

def approximation (S : FlaggedTensor X Y Z) (deleted : Color) {R d D : ℕ}
    (W : Tensor.PolynomialApproximation S.tensor R d D) :
    Tensor.PolynomialApproximation (tensor S deleted) R d D := by
  simpa only [restriction] using
    W.restrict (leftMap S deleted) (middleMap S deleted) (rightMap S deleted)

def Leaf (S : FlaggedTensor X Y Z) (deleted : Color) :=
  {p : X × Y × Z // tensor S deleted p.1 p.2.1 p.2.2 ≠ 0}

instance leafFintype (S : FlaggedTensor X Y Z) (deleted : Color) :
    Fintype (Leaf S deleted) :=
  inferInstanceAs (Fintype {p : X × Y × Z // tensor S deleted p.1 p.2.1 p.2.2 ≠ 0})

def leafEquiv (S : FlaggedTensor X Y Z) (deleted : Color) :
    Leaf S deleted ≃ {a : CompletionLabels.Leaf S // leafColor S a ≠ deleted} where
  toFun a :=
    ⟨⟨a.val, ((support_iff S deleted _ _ _).mp a.property).1⟩,
      fun h => ((support_iff S deleted _ _ _).mp a.property).2
        ((leafColor_eq_iff S _ deleted).mp h)⟩
  invFun a :=
    ⟨a.val.val, (support_iff S deleted _ _ _).mpr
      ⟨a.val.property, fun h => a.property ((leafColor_eq_iff S _ deleted).mpr h)⟩⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; rfl

def retainedLeafEquiv (S : FlaggedTensor X Y Z) (deleted first second : Color)
    (colors : ∀ c : Color, c ≠ deleted ↔ c = first ∨ c = second) :
    Leaf S deleted ≃ RetainedLeaf S first second :=
  (leafEquiv S deleted).trans
    (Equiv.subtypeEquivRight (fun a => colors (leafColor S a)))

omit [Fintype X] [Fintype Y] [Fintype Z] in
@[simp] theorem retainedLeafEquiv_coordinates
    (S : FlaggedTensor X Y Z) (deleted first second : Color)
    (colors : ∀ c : Color, c ≠ deleted ↔ c = first ∨ c = second)
    (a : Leaf S deleted) :
    ((retainedLeafEquiv S deleted first second colors a).val).val = a.val := rfl

end MatrixMultiplication.CompletionTermination

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_UniformCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq

variable {A X : Type*} [Fintype A] [Fintype X]

def UniformCoordinate (p : FiniteLaw A) (f : A → X) (P : X → Prop) : Prop :=
  ∀ x, (p.map f).mass x = if P x then (Fintype.card {x // P x} : ℝ)⁻¹ else 0

end MatrixMultiplication.CompletionLaws

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Completion_TerminationLaw
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionTerminationLaw

open MatrixMultiplication.Foundation CompletionLabels CompletionColorLaws CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

theorem retained_mass_one (S : FlaggedTensor X Y Z) (first second : Color)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    eventMass (colorMix S first second pf ps a ha ha')
      (fun w => leafColor S w = first ∨ leafColor S w = second) = 1 := by
  rw [eventMass, sum_subtype_indicator]
  calc
    _ = ∑ w, (colorMix S first second pf ps a ha ha').mass w := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs with h
      · rfl
      · exact (colorMix_mass_zero S first second pf ps a ha ha' w
          (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))).symm
    _ = _ := (colorMix S first second pf ps a ha ha').total

def retainedEquiv (S : FlaggedTensor X Y Z) (first second : Color) :
    {w : Leaf S // leafColor S w = first ∨ leafColor S w = second} ≃
      RetainedLeaf S first second := Equiv.refl _

theorem retained_sum (S : FlaggedTensor X Y Z) (first second : Color) (f : Leaf S → ℝ) :
    (∑ w : RetainedLeaf S first second, f w.val) =
      ∑ w : {w : Leaf S // leafColor S w = first ∨ leafColor S w = second}, f w.val := by
  exact ((retainedEquiv S first second).sum_comp
    (fun w : RetainedLeaf S first second => f w.val)).symm

def law (S : FlaggedTensor X Y Z) (first second : Color)
    (pf : FiniteLaw (ColorSlice S first)) (ps : FiniteLaw (ColorSlice S second))
    (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    FiniteLaw (RetainedLeaf S first second) where
  mass w := (colorMix S first second pf ps a ha ha').mass w.val
  nonneg w := (colorMix S first second pf ps a ha ha').nonneg w.val
  total := by
    rw [retained_sum]
    exact retained_mass_one S first second pf ps a ha ha'

end MatrixMultiplication.CompletionTerminationLaw

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCW75Primitive
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

theorem original_support (x y z : Word) (h : tensor x y z ≠ 0) (i : Fin 3) :
    (x i).val + (y i).val + (z i).val = 2 := by
  have hs : source x y z ≠ 0 := by
    intro hs
    simp [tensor, hs] at h
  have hi := source_factors x y z hs i
  have hcw : CoppersmithWinograd.tensor (x i) (y i) (z i) ≠ 0 := by
    intro hzero
    simp [CWBoundary.tensor, hzero] at hi
  exact (CWOriginalWords.tensor_ne_zero_iff _ _ _).mp hcw

open Elementary

theorem support_exhausted (x y z : Word) (h : tensor x y z ≠ 0) :
    ∃ w, w ∈ Elementary.triples.filter Elementary.retained ∧
      (listedX w, listedY w, listedZ w) = (x, y, z) := by
  have hs : source x y z ≠ 0 := by
    intro hs
    simp [tensor, hs] at h
  obtain ⟨a, hax, hay, haz⟩ :=
    boundary_component_complete (x 0) (y 0) (z 0) (source_factors x y z hs 0)
  obtain ⟨b, hbx, hby, hbz⟩ :=
    boundary_component_complete (x 1) (y 1) (z 1) (source_factors x y z hs 1)
  obtain ⟨third, hcx, hcy, hcz⟩ :=
    boundary_component_complete (x 2) (y 2) (z 2) (source_factors x y z hs 2)
  have hx : listedX [a, b, third] = x := by
    funext i
    fin_cases i <;>
      simp [listedX, listedWord, CWOriginalWords.xWord, hax, hbx, hcx]
  have hy : listedY [a, b, third] = y := by
    funext i
    fin_cases i <;>
      simp [listedY, listedWord, CWOriginalWords.yWord, hay, hby, hcy]
  have hz : listedZ [a, b, third] = z := by
    funext i
    fin_cases i <;>
      simp [listedZ, listedWord, CWOriginalWords.zWord, haz, hbz, hcz]
  have hc := tensor_on_triple a b third
  rw [hx, hy, hz] at hc
  have hr : Elementary.retained [a, b, third] = true := by
    cases hret : Elementary.retained [a, b, third] <;> simp_all
  exact ⟨[a, b, third], List.mem_filter.mpr ⟨triple_mem a b third, hr⟩,
    Prod.ext hx (Prod.ext hy hz)⟩

end MatrixMultiplication.Foundation.CW75Primitive

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_CoppersmithWinograd_ComplexCW75LabelHierarchy
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero
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

theorem coefficient_ne_zero (a : Scalar) :
    CW75Primitive.tensor (x a) (y a) (z a) ≠ 0 := by
  rw [coefficient_one]
  exact one_ne_zero

theorem support_exhausted (u v w : Word) (h : CW75Primitive.tensor u v w ≠ 0) :
    ∃ a : Scalar, (x a, y a, z a) = (u, v, w) := by
  obtain ⟨terms, hterms, he⟩ := CW75Primitive.support_exhausted u v w h
  refine ⟨⟨terms, ?_⟩, he⟩
  simpa [retainedWords] using hterms

theorem term_bits_injective : Function.Injective
    (fun a : BoundaryTerm =>
      (decide ((CW75Primitive.component a).x ≠ 0),
       decide ((CW75Primitive.component a).y = 2),
       decide ((CW75Primitive.component a).z = 1),
       decide ((CW75Primitive.component a).x = 1))) := by
  intro a b h
  cases a <;> cases b <;>
    norm_num [CW75Primitive.component, CWOriginalWords.OriginalComponent.x,
      CWOriginalWords.OriginalComponent.y, CWOriginalWords.OriginalComponent.z,
      ← Fin.val_eq_val] at h <;> rfl

theorem positionLabels_injective : Function.Injective
    (fun a : Scalar => (bPositions a, cPositions a, aChoices a, bChoices a)) := by
  intro a b h
  apply grade_injective
  funext i
  apply congrArg CW75Primitive.component
  apply term_bits_injective
  exact Prod.ext (congrFun (congrArg Prod.fst h) i)
    (Prod.ext (congrFun (congrArg (fun q => q.2.1) h) i)
      (Prod.ext (congrFun (congrArg (fun q => q.2.2.1) h) i)
        (congrFun (congrArg (fun q => q.2.2.2) h) i)))

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

structure FiniteRectangularWitness where
  outer : ℕ
  inner : ℕ
  multiplicity : ℕ
  rank : ℕ
  outer_pos : 0 < outer
  inner_pos : 0 < inner
  multiplicity_pos : 0 < multiplicity
  rank_pos : 0 < rank
  order : ℕ
  degree : ℕ
  approximation : Tensor.PolynomialApproximation
    (Tensor.directSum (fun _ : Fin multiplicity =>
      Tensor.matrixCoefficients (K := ℂ) (Fin outer) (Fin inner) (Fin outer)))
    rank order degree

def curveFiber (u : CurveCoordinate) : Finset (List Elementary.BoundaryTerm) :=
  CW75LabelHierarchy.retainedWords.filter fun w =>
    CW75Primitive.listedX w 0 = u 0 ∧
    CW75Primitive.listedX w 1 = u 1 ∧
    CW75Primitive.listedX w 2 = u 2

def curveFiberSize (u : CurveCoordinate) : ℕ := (curveFiber u).card

theorem mem_curveFiber (u : CurveCoordinate) (w : List Elementary.BoundaryTerm) :
    w ∈ curveFiber u ↔
      w ∈ CW75LabelHierarchy.retainedWords ∧ CW75Primitive.listedX w = u := by
  simp only [curveFiber, Finset.mem_filter]
  constructor
  · rintro ⟨hw, h0, h1, h2⟩
    refine ⟨hw, ?_⟩
    funext i
    fin_cases i <;> assumption
  · rintro ⟨hw, h⟩
    exact ⟨hw, congrFun h 0, congrFun h 1, congrFun h 2⟩

def curveFiberEquiv (u : CurveCoordinate) :
    {s : CurveLeaf // CW75LabelHierarchy.x s = u} ≃ ↥(curveFiber u) where
  toFun s := ⟨s.val.val, (mem_curveFiber u s.val.val).2
    ⟨s.val.property, s.property⟩⟩
  invFun s := ⟨⟨s.val, ((mem_curveFiber u s.val).1 s.property).1⟩,
    ((mem_curveFiber u s.val).1 s.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem curveFiberSize_eq_card (u : CurveCoordinate) :
    curveFiberSize u =
      Fintype.card {s : CurveLeaf // CW75LabelHierarchy.x s = u} := by
  rw [Fintype.card_congr (curveFiberEquiv u), Fintype.card_coe]
  rfl

theorem curveFiberSize_pos : ∀ u : CurveCoordinate, 0 < curveFiberSize u := by
  decide

theorem sum_curveLeaves_by_X (f : CurveCoordinate → ℝ) :
    (∑ s : CurveLeaf, f (CW75LabelHierarchy.x s)) =
      ∑ u : CurveCoordinate, (curveFiberSize u : ℝ) * f u := by
  classical
  rw [← Fintype.sum_fiberwise' CW75LabelHierarchy.x f]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← curveFiberSize_eq_card]

theorem curve_completeRecord_injective :
    Function.Injective (labelRecordOf curveLabels 5) := by
  intro a b h
  apply CW75LabelHierarchy.positionLabels_injective
  exact Prod.ext (congrArg (fun q : LabelRecord CurveLabel 5 => q.1.1.1.2) h)
    (Prod.ext (congrArg (fun q : LabelRecord CurveLabel 5 => q.1.2) h)
      (Prod.ext (congrArg (fun q : LabelRecord CurveLabel 5 => q.2) h)
        (congrArg (fun q : LabelRecord CurveLabel 5 => q.1.1.2) h)))

def encodeCurveX (u : CurveCoordinate) : LabelRecord CurveLabel 3 :=
  (((PUnit.unit, CW75LabelHierarchy.outerX u),
    CW75LabelHierarchy.bPositionsX u), CW75LabelHierarchy.bChoicesX u)

def decodeCurveX (r : LabelRecord CurveLabel 3) : CurveCoordinate := fun i =>
  if r.2 i then 1 else if r.1.2 i then 2 else 0

def curveReaderPair (n : Fin 5) : ReaderPair :=
  match n.val with
  | 1 => .xz
  | 3 | 4 => .yz
  | _ => .xy

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

variable {Position : Type u} [Fintype Position]

variable {Prefix : Type v} {counts : Scalar → ℕ} {n t : ℕ}

theorem root_eligible_iff
    (old : ExactPrefix counts curveLabels 0 t Position) (u v w : LongWord Position) :
    eligible id old u v w ↔ ∀ i, CW75Primitive.tensor (u i) (v i) (w i) ≠ 0 := by
  constructor
  · intro h i
    rw [eligible_coefficient_one id old u v w h i]
    exact one_ne_zero
  · intro h
    have hchoice : ∀ i : Position, ∃ a : Scalar, (x a, y a, z a) = (u i, v i, w i) :=
      fun i => CW75LabelHierarchy.support_exhausted (u i) (v i) (w i) (h i)
    choose word hword using hchoice
    refine ⟨word, ?_, ?_, ?_, ?_⟩
    · funext i
      exact (congrArg Prod.fst (hword i)).symm
    · funext i
      exact (congrArg (fun q => q.2.1) (hword i)).symm
    · funext i
      exact (congrArg (fun q => q.2.2) (hword i)).symm
    · intro i
      change (old.val i : PUnit) = PUnit.unit
      exact Subsingleton.elim _ _

def terminalWord (last : ExactPrefix counts curveLabels 5 t Position) :
    PopulationWords Position (fun a => t * counts a) := by
  let source := sourcePrefixEquiv counts curveLabels 5 t Position curve_completeRecord_injective last
  refine ⟨source.val, ?_⟩
  intro a
  refine Eq.trans ?_ (source.property a)
  unfold wordPopulation
  exact congrArg
    (fun inst : Fintype {i : Position // source.val i = a} => @Fintype.card _ inst)
    (Subsingleton.elim _ _)

theorem terminalWord_record (last : ExactPrefix counts curveLabels 5 t Position) (i : Position) :
    labelRecordOf curveLabels 5 ((terminalWord last).val i) = last.val i :=
  sourceSymbol_record last i

theorem terminalWord_of_represents
    (last : ExactPrefix counts curveLabels 5 t Position) (u v w : LongWord Position)
    (word : Position → Scalar) (hword : Represents id last u v w word) :
    (terminalWord last).val = word := by
  funext i
  exact (sourceSymbol_eq_iff curve_completeRecord_injective last i (word i)).2 (hword.2.2.2 i)

theorem terminal_eligible_iff
    (last : ExactPrefix counts curveLabels 5 t Position) (u v w : LongWord Position) :
    eligible id last u v w ↔
      u = longX (terminalWord last).val ∧ v = longY (terminalWord last).val ∧
        w = longZ (terminalWord last).val := by
  constructor
  · rintro ⟨word, hword⟩
    rw [terminalWord_of_represents last u v w word hword]
    exact ⟨hword.1, hword.2.1, hword.2.2.1⟩
  · rintro ⟨hu, hv, hw⟩
    refine ⟨(terminalWord last).val, hu, hv, hw, ?_⟩
    intro i
    exact (terminalWord_record last i).symm

end MatrixMultiplication.CW75ReorderedWords

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedExecution
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows
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

def initial (counts : Scalar → ℕ) (t : ℕ) : Bundle counts t 0 := by
  let E := (CW75InitialExecution.execution (t * ∑ a, counts a)).reindexOutput
    (rootPrefixEquiv counts curveLabels t (Position counts t) (position_card counts t))
    (Equiv.refl PUnit) (Equiv.refl PUnit) (Equiv.refl PUnit)
  refine {
    PX := PUnit
    PY := PUnit
    PZ := PUnit
    AX := PUnit
    AY := PUnit
    AZ := PUnit
    execution := E
    shape := MatrixCoordinates.scalar
    shape_positive := MatrixCoordinates.scalar_positive
    normal := ?_
    rank_exact := ?_
    volume_exact := ?_
    rows_exact := by simp [MatrixCoordinates.scalar]
    inner_exact := by simp [MatrixCoordinates.scalar]
    columns_exact := by simp [MatrixCoordinates.scalar]
    pairing_budget := le_rfl
  }
  · funext x y z
    change E.value x y z = prefixValue counts t 0 MatrixCoordinates.scalar.tensor x y z
    rw [Execution.reindexOutput_value, CW75InitialExecution.value_retained]
    have hxy : x.2.1 = y.2.1 := Subsingleton.elim _ _
    have hxz : x.2.1 = z.2.1 := Subsingleton.elim _ _
    have hguard : (x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        eligible id x.2.1 x.1 y.1 z.1) ↔
        ∀ i, CW75Primitive.tensor (x.1 i) (y.1 i) (z.1 i) ≠ 0 := by
      rw [root_eligible_iff]
      exact ⟨fun h => h.2.2, fun h => ⟨hxy, hxz, h⟩⟩
    simp only [prefixValue, hguard, MatrixCoordinates.scalar_tensor]
  · change 1 = stageAuxiliaryBudget counts curveLabels 0 t
    simp [stageAuxiliaryBudget]
  · change 1 = stagePairingProduct counts curveLabels 0 t
    simp [stagePairingProduct]

def realize (counts : Scalar → ℕ) (t : ℕ) : Bundle counts t 5 :=
  let B0 := initial counts t
  let B1 : Bundle counts t 1 := extendXY B0 (by decide) rfl rfl
  let B2 : Bundle counts t 2 := extendXZ B1 (by decide) rfl rfl
  let B3 : Bundle counts t 3 := extendXY B2 (by decide) rfl rfl
  let B4 : Bundle counts t 4 := extendYZ B3 (by decide) rfl rfl
  extendYZ B4 (by decide) rfl rfl

theorem realize_rankBound (counts : Scalar → ℕ) (t : ℕ) :
    (realize counts t).execution.rankBound = stageAuxiliaryBudget counts curveLabels 5 t :=
  (realize counts t).rank_exact

theorem realize_volume (counts : Scalar → ℕ) (t : ℕ) :
    (realize counts t).shape.volume = Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [(realize counts t).volume_exact]
  simpa only [exactWords_card] using
    (stagePairingProduct_eq_exactWords_card counts curveLabels 5 curve_completeRecord_injective t)

theorem realize_pairing_budget (counts : Scalar → ℕ) (t : ℕ) :
    (realize counts t).shape.volume ≤ (realize counts t).execution.rankBound :=
  (realize counts t).pairing_budget

theorem realize_value (counts : Scalar → ℕ) (t : ℕ)
    (x : Coordinate counts t × (Prefix counts t 5 × (realize counts t).PX))
    (y : Coordinate counts t × (Prefix counts t 5 × (realize counts t).PY))
    (z : Coordinate counts t × (Prefix counts t 5 × (realize counts t).PZ)) :
    (realize counts t).execution.value x y z =
      if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        x.1 = longX (terminalWord x.2.1).val ∧
        y.1 = longY (terminalWord x.2.1).val ∧
        z.1 = longZ (terminalWord x.2.1).val
      then (realize counts t).shape.tensor x.2.2 y.2.2 z.2.2 else 0 := by
  rw [(realize counts t).normal]
  simp only [prefixValue, terminal_eligible_iff]

theorem realize_label_card (counts : Scalar → ℕ) (t : ℕ) :
    Fintype.card (Prefix counts t 5) = Fintype.card (ExactWords (fun a => t * counts a)) := by
  rw [exactWords_card]
  let : DecidableEq Scalar := Classical.decEq Scalar
  calc
    Fintype.card (Prefix counts t 5) =
        Fintype.card (PopulationWords (Position counts t) (fun a => t * counts a)) :=
      Fintype.card_congr
        (sourcePrefixEquiv counts curveLabels 5 t (Position counts t) curve_completeRecord_injective)
    _ = Nat.multinomial Finset.univ (fun a => t * counts a) :=
      populationWords_card (I := Position counts t)
        (fun a => t * counts a) (position_card counts t)

end MatrixMultiplication.CW75ReorderedExecution

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedFinite
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.RecursiveCompletion.complete_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedFinite

open MatrixMultiplication.Foundation CW75LabelHierarchy StageHierarchyResources
open ExecutionPairingBudget CW75ReorderedWords CW75ReorderedExecution ComplexWitness
open scoped BigOperators Classical

attribute [local irreducible] CW75LabelHierarchy.retainedWords

def blocks (counts : Scalar → ℕ) (t : ℕ) : ℕ := t * ∑ a, counts a

def copies (counts : Scalar → ℕ) (t : ℕ) : ℕ :=
  Fintype.card (ExactWords (fun a => t * counts a))

def rows (counts : Scalar → ℕ) (t : ℕ) : ℕ := (realize counts t).shape.rows
def inner (counts : Scalar → ℕ) (t : ℕ) : ℕ := (realize counts t).shape.inner
def columns (counts : Scalar → ℕ) (t : ℕ) : ℕ := (realize counts t).shape.columns

def rankBudget (counts : Scalar → ℕ) (t : ℕ) : ℕ :=
  27 ^ blocks counts t * stageAuxiliaryBudget counts curveLabels 5 t

def order (counts : Scalar → ℕ) (t : ℕ) : ℕ :=
  6 * blocks counts t * ((realize counts t).execution.order + 1) +
    (realize counts t).execution.order

def degree (counts : Scalar → ℕ) (t : ℕ) : ℕ :=
  18 * blocks counts t * ((realize counts t).execution.order + 1) +
    (realize counts t).execution.leftDegree +
    (realize counts t).execution.middleDegree +
    (realize counts t).execution.rightDegree

def sourceApproximation (counts : Scalar → ℕ) (t : ℕ) :
    Tensor.PolynomialApproximation (CW75InitialExecution.fullSource (blocks counts t))
      (27 ^ blocks counts t) (6 * blocks counts t) (18 * blocks counts t) := by
  simpa only [CW75InitialExecution.fullSource, show (3 : ℕ) ^ 3 = 27 by norm_num,
    show (2 : ℕ) * 3 = 6 by norm_num, show (6 : ℕ) * 3 = 18 by norm_num] using
    (CoppersmithWinograd.approximation.power 3).power (blocks counts t)

def labelEquiv (counts : Scalar → ℕ) (t : ℕ) :
    Fin (copies counts t) ≃ Prefix counts t 5 :=
  Fintype.equivOfCardEq ((Fintype.card_fin (copies counts t)).trans
    (realize_label_card counts t).symm)

def designatedX {counts : Scalar → ℕ} {t : ℕ} (p : Prefix counts t 5) :
    Coordinate counts t := longX (terminalWord p).val

def designatedY {counts : Scalar → ℕ} {t : ℕ} (p : Prefix counts t 5) :
    Coordinate counts t := longY (terminalWord p).val

def designatedZ {counts : Scalar → ℕ} {t : ℕ} (p : Prefix counts t 5) :
    Coordinate counts t := longZ (terminalWord p).val

theorem designated_coefficient_one (counts : Scalar → ℕ) (t : ℕ)
    (p : Prefix counts t 5) :
    CW75InitialExecution.fullSource (blocks counts t)
      (designatedX p) (designatedY p) (designatedZ p) = 1 := by
  unfold CW75InitialExecution.fullSource Tensor.power
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j _
  have hs := CW75Primitive.original_support _ _ _
    (coefficient_ne_zero ((terminalWord p).val i)) j
  simp only [CoppersmithWinograd.tensor, designatedX, designatedY, designatedZ,
    longX, longY, longZ]
  exact ite_eq_left hs

def leftSelect (counts : Scalar → ℕ) (t : ℕ)
    (u : Fin (copies counts t) × (Fin (rows counts t) × Fin (inner counts t))) :
    Coordinate counts t × (Prefix counts t 5 × (realize counts t).PX) :=
  (designatedX (labelEquiv counts t u.1),
    (labelEquiv counts t u.1, (realize counts t).shape.left.symm u.2))

def middleSelect (counts : Scalar → ℕ) (t : ℕ)
    (v : Fin (copies counts t) × (Fin (inner counts t) × Fin (columns counts t))) :
    Coordinate counts t × (Prefix counts t 5 × (realize counts t).PY) :=
  (designatedY (labelEquiv counts t v.1),
    (labelEquiv counts t v.1, (realize counts t).shape.middle.symm v.2))

def rightSelect (counts : Scalar → ℕ) (t : ℕ)
    (w : Fin (copies counts t) × (Fin (columns counts t) × Fin (rows counts t))) :
    Coordinate counts t × (Prefix counts t 5 × (realize counts t).PZ) :=
  (designatedZ (labelEquiv counts t w.1),
    (labelEquiv counts t w.1, (realize counts t).shape.right.symm w.2))

theorem selected_output (counts : Scalar → ℕ) (t : ℕ) :
    Tensor.pullback (leftSelect counts t) (middleSelect counts t) (rightSelect counts t)
      (LocalMaps.originalScale (CW75InitialExecution.fullSource (blocks counts t))
        (realize counts t).execution.value) =
      Tensor.directSum (fun _ : Fin (copies counts t) =>
        Tensor.matrixCoefficients (K := ℂ) (Fin (rows counts t))
          (Fin (inner counts t)) (Fin (columns counts t))) := by
  funext u v w
  simp only [Tensor.pullback, LocalMaps.originalScale, leftSelect, middleSelect, rightSelect]
  rw [realize_value]
  simp only [MatrixCoordinates.tensor, Tensor.pullback]
  by_cases h : u.1 = v.1 ∧ u.1 = w.1
  · have hv : v.1 = u.1 := h.1.symm
    have hw : w.1 = u.1 := h.2.symm
    have hc := designated_coefficient_one counts t (labelEquiv counts t u.1)
    simp only [designatedX, designatedY, designatedZ] at hc
    simp only [hv, hw, designatedX, designatedY, designatedZ, hc,
      Tensor.directSum, true_and, ite_true, if_true, one_mul]
    simp only [rows, inner, columns,
      (realize counts t).shape.left.apply_symm_apply u.2,
      (realize counts t).shape.middle.apply_symm_apply v.2,
      (realize counts t).shape.right.apply_symm_apply w.2]
    unfold Tensor.matrixCoefficients
    split_ifs <;> rfl
  · have hn : ¬ (labelEquiv counts t u.1 = labelEquiv counts t v.1 ∧
        labelEquiv counts t u.1 = labelEquiv counts t w.1 ∧
        designatedX (labelEquiv counts t u.1) =
          longX (terminalWord (labelEquiv counts t u.1)).val ∧
        designatedY (labelEquiv counts t v.1) =
          longY (terminalWord (labelEquiv counts t u.1)).val ∧
        designatedZ (labelEquiv counts t w.1) =
          longZ (terminalWord (labelEquiv counts t u.1)).val) := by
      intro he
      exact h ⟨(labelEquiv counts t).injective he.1,
        (labelEquiv counts t).injective he.2.1⟩
    simp only [Tensor.directSum, ite_eq_right h, ite_eq_right hn, mul_zero]

def approximation (counts : Scalar → ℕ) (t : ℕ) :
    Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin (copies counts t) =>
        Tensor.matrixCoefficients (K := ℂ) (Fin (rows counts t))
          (Fin (inner counts t)) (Fin (columns counts t))))
      (rankBudget counts t) (order counts t) (degree counts t) := by
  have supported : ∀ x y z : Coordinate counts t,
      ¬ CW75InitialExecution.support x y z →
        CW75InitialExecution.fullSource (blocks counts t) x y z = 0 := by
    intro x y z hs
    exact not_ne_iff.mp hs
  have full := ExecutionApproximation.approximation (realize counts t).execution
    (sourceApproximation counts t) supported
  have selected := full.pullback (leftSelect counts t) (middleSelect counts t)
    (rightSelect counts t)
  rw [selected_output] at selected
  simpa only [rankBudget, order, degree, realize_rankBound] using selected

theorem dimensions_positive (counts : Scalar → ℕ) (t : ℕ) :
    0 < rows counts t ∧ 0 < inner counts t ∧ 0 < columns counts t :=
  (realize counts t).shape_positive

theorem volume_eq_copies (counts : Scalar → ℕ) (t : ℕ) :
    rows counts t * inner counts t * columns counts t = copies counts t :=
  realize_volume counts t

theorem rows_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < rows counts t :=
  (dimensions_positive counts t).1

theorem inner_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < inner counts t :=
  (dimensions_positive counts t).2.1

theorem columns_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < columns counts t :=
  (dimensions_positive counts t).2.2

theorem copies_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < copies counts t := by
  rw [← volume_eq_copies]
  exact Nat.mul_pos (Nat.mul_pos (rows_pos counts t) (inner_pos counts t))
    (columns_pos counts t)

theorem rankBudget_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < rankBudget counts t := by
  apply Nat.mul_pos (pow_pos (by decide) _)
  rw [← realize_rankBound]
  exact lt_of_lt_of_le (by
    change 0 < rows counts t * inner counts t * columns counts t
    rw [volume_eq_copies]
    exact copies_pos counts t) (realize_pairing_budget counts t)

end MatrixMultiplication.CW75ReorderedFinite

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Polynomial_ComplexPolynomialExecutionSymmetry
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value _root_.OAI.MatrixMultiplication.Foundation.CW75Primitive.restriction_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundary_basePolynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.scalar_tensor _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor _root_.OAI.MatrixMultiplication.Foundation.InitialTargetExecution.initial_order _root_.OAI.MatrixMultiplication.Foundation.InitialTargetExecution.initial_rankBound _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_auxiliary _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_kernel _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_leftDegree _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_leftMap _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_middleDegree _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_middleMap _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_order _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_rankBound _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_rightDegree _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_rightMap _root_.OAI.MatrixMultiplication.Foundation.PolynomialKernelExecution.Execution.reindexOutput_value _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_constantMatrix_coeff_zero _root_.OAI.MatrixMultiplication.Foundation.PolynomialLocalConstruction.kernel_weightedCoordinatePolynomialMatrix_coeff_zero
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

section Swap

variable {K X Y Z X' Y' Z' : Type*} [CommSemiring K]

def swapXY (T : Tensor K X Y Z) : Tensor K Y X Z := fun y x z => T x y z

theorem RankAtMost.swapXY {T : Tensor K X Y Z} {r : ℕ} (h : RankAtMost T r) :
    RankAtMost (swapXY T) r := by
  rcases h with ⟨a, b, c, rfl⟩
  refine ⟨b, a, c, ?_⟩
  funext y x z
  simp only [rankOne]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem swapXY_restrict [Fintype X] [Fintype Y] [Fintype Z]
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (T : Tensor K X Y Z) :
    swapXY (restrict A B C T) = restrict B A C (swapXY T) := by
  funext y' x' z'
  simp only [swapXY, restrict]
  calc
    (∑ x, ∑ y, ∑ z, A x' x * B y' y * C z' z * T x y z) =
        ∑ y, ∑ x, ∑ z, A x' x * B y' y * C z' z * T x y z := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro z hz
      ring

end Swap
end Tensor

namespace PolynomialLocalConstruction

open _root_.OAI.MatrixMultiplication.Foundation.Tensor LocalMaps

variable {X Y Z OX OY OZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]

theorem kernel_cyclic (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → Polynomial ℂ) (MY : Y → OY → AY → Polynomial ℂ)
    (MZ : Z → OZ → AZ → Polynomial ℂ)
    (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    kernel (Tensor.cyclic auxiliary) MY MZ MX y z x = kernel auxiliary MX MY MZ x y z := by
  have h := congrFun (congrFun (congrFun
    (Tensor.cyclic_restrict (MX x.1) (MY y.1) (MZ z.1)
      (fun a b c => Polynomial.C (auxiliary a b c))) y.2) z.2) x.2
  simpa only [kernel, fiberTransform, Tensor.cyclic, Tensor.restrict] using h.symm

theorem kernel_swapXY (auxiliary : Tensor ℂ AX AY AZ)
    (MX : X → OX → AX → Polynomial ℂ) (MY : Y → OY → AY → Polynomial ℂ)
    (MZ : Z → OZ → AZ → Polynomial ℂ)
    (x : X × OX) (y : Y × OY) (z : Z × OZ) :
    kernel (Tensor.swapXY auxiliary) MY MX MZ y x z = kernel auxiliary MX MY MZ x y z := by
  have h := congrFun (congrFun (congrFun
    (Tensor.swapXY_restrict (MX x.1) (MY y.1) (MZ z.1)
      (fun a b c => Polynomial.C (auxiliary a b c))) y.2) x.2) z.2
  simpa only [kernel, fiberTransform, Tensor.swapXY, Tensor.restrict] using h.symm

end PolynomialLocalConstruction

namespace PolynomialKernelExecution.Execution

open _root_.OAI.MatrixMultiplication.Foundation.Tensor PolynomialLocalConstruction

variable {X Y Z Prefix PX PY PZ AX AY AZ : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]
variable {support : X → Y → Z → Prop}
variable (E : Execution X Y Z Prefix PX PY PZ AX AY AZ support)

def cyclic : Execution Y Z X Prefix PY PZ PX AY AZ AX
    (fun y z x => support x y z) where
  auxiliary := Tensor.cyclic E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank.cyclic
  order := E.order
  leftDegree := E.middleDegree
  middleDegree := E.rightDegree
  rightDegree := E.leftDegree
  leftMap := E.middleMap
  middleMap := E.rightMap
  rightMap := E.leftMap
  left_degree := E.middle_degree
  middle_degree := E.right_degree
  right_degree := E.left_degree
  value := Tensor.cyclic E.value
  vanishes := by
    intro y z x hs j hj
    rw [kernel_cyclic]
    exact E.vanishes x y z hs j hj
  leading := by
    intro y z x hs
    rw [kernel_cyclic]
    exact E.leading x y z hs
  synchronized := by
    intro y z x hs hn
    have h := E.synchronized x y z hs hn
    exact ⟨h.1.symm.trans h.2, h.1.symm⟩

@[simp] theorem cyclic_auxiliary : E.cyclic.auxiliary = Tensor.cyclic E.auxiliary := rfl
@[simp] theorem cyclic_rankBound : E.cyclic.rankBound = E.rankBound := rfl
@[simp] theorem cyclic_order : E.cyclic.order = E.order := rfl
@[simp] theorem cyclic_leftDegree : E.cyclic.leftDegree = E.middleDegree := rfl
@[simp] theorem cyclic_middleDegree : E.cyclic.middleDegree = E.rightDegree := rfl
@[simp] theorem cyclic_rightDegree : E.cyclic.rightDegree = E.leftDegree := rfl
@[simp] theorem cyclic_leftMap : E.cyclic.leftMap = E.middleMap := rfl
@[simp] theorem cyclic_middleMap : E.cyclic.middleMap = E.rightMap := rfl
@[simp] theorem cyclic_rightMap : E.cyclic.rightMap = E.leftMap := rfl

@[simp] theorem cyclic_value
    (y : Y × (Prefix × PY)) (z : Z × (Prefix × PZ)) (x : X × (Prefix × PX)) :
    E.cyclic.value y z x = E.value x y z := rfl

def swapXY : Execution Y X Z Prefix PY PX PZ AY AX AZ
    (fun y x z => support x y z) where
  auxiliary := Tensor.swapXY E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank.swapXY
  order := E.order
  leftDegree := E.middleDegree
  middleDegree := E.leftDegree
  rightDegree := E.rightDegree
  leftMap := E.middleMap
  middleMap := E.leftMap
  rightMap := E.rightMap
  left_degree := E.middle_degree
  middle_degree := E.left_degree
  right_degree := E.right_degree
  value := Tensor.swapXY E.value
  vanishes := by
    intro y x z hs j hj
    rw [kernel_swapXY]
    exact E.vanishes x y z hs j hj
  leading := by
    intro y x z hs
    rw [kernel_swapXY]
    exact E.leading x y z hs
  synchronized := by
    intro y x z hs hn
    have h := E.synchronized x y z hs hn
    exact ⟨h.1.symm, h.1.symm.trans h.2⟩

@[simp] theorem swapXY_auxiliary : E.swapXY.auxiliary = Tensor.swapXY E.auxiliary := rfl
@[simp] theorem swapXY_rankBound : E.swapXY.rankBound = E.rankBound := rfl
@[simp] theorem swapXY_order : E.swapXY.order = E.order := rfl
@[simp] theorem swapXY_leftDegree : E.swapXY.leftDegree = E.middleDegree := rfl
@[simp] theorem swapXY_middleDegree : E.swapXY.middleDegree = E.leftDegree := rfl
@[simp] theorem swapXY_rightDegree : E.swapXY.rightDegree = E.rightDegree := rfl
@[simp] theorem swapXY_leftMap : E.swapXY.leftMap = E.middleMap := rfl
@[simp] theorem swapXY_middleMap : E.swapXY.middleMap = E.leftMap := rfl
@[simp] theorem swapXY_rightMap : E.swapXY.rightMap = E.rightMap := rfl

@[simp] theorem swapXY_value
    (y : Y × (Prefix × PY)) (x : X × (Prefix × PX)) (z : Z × (Prefix × PZ)) :
    E.swapXY.value y x z = E.value x y z := rfl

section OriginalCoordinates

variable {X' Y' Z' : Type*}
variable (eX : X' ≃ X) (eY : Y' ≃ Y) (eZ : Z' ≃ Z)

def reindexOriginal : Execution X' Y' Z' Prefix PX PY PZ AX AY AZ
    (fun x y z => support (eX x) (eY y) (eZ z)) where
  auxiliary := E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank
  order := E.order
  leftDegree := E.leftDegree
  middleDegree := E.middleDegree
  rightDegree := E.rightDegree
  leftMap := fun x => E.leftMap (eX x)
  middleMap := fun y => E.middleMap (eY y)
  rightMap := fun z => E.rightMap (eZ z)
  left_degree := fun x => E.left_degree (eX x)
  middle_degree := fun y => E.middle_degree (eY y)
  right_degree := fun z => E.right_degree (eZ z)
  value := fun x y z => E.value (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2)
  vanishes := fun x y z hs j hj =>
    E.vanishes (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) hs j hj
  leading := fun x y z hs =>
    E.leading (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) hs
  synchronized := fun x y z hs hn =>
    E.synchronized (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) hs hn

@[simp] theorem reindexOriginal_auxiliary :
    (E.reindexOriginal eX eY eZ).auxiliary = E.auxiliary := rfl
@[simp] theorem reindexOriginal_rankBound :
    (E.reindexOriginal eX eY eZ).rankBound = E.rankBound := rfl
@[simp] theorem reindexOriginal_order :
    (E.reindexOriginal eX eY eZ).order = E.order := rfl
@[simp] theorem reindexOriginal_leftDegree :
    (E.reindexOriginal eX eY eZ).leftDegree = E.leftDegree := rfl
@[simp] theorem reindexOriginal_middleDegree :
    (E.reindexOriginal eX eY eZ).middleDegree = E.middleDegree := rfl
@[simp] theorem reindexOriginal_rightDegree :
    (E.reindexOriginal eX eY eZ).rightDegree = E.rightDegree := rfl
@[simp] theorem reindexOriginal_leftMap :
    (E.reindexOriginal eX eY eZ).leftMap = fun x => E.leftMap (eX x) := rfl
@[simp] theorem reindexOriginal_middleMap :
    (E.reindexOriginal eX eY eZ).middleMap = fun y => E.middleMap (eY y) := rfl
@[simp] theorem reindexOriginal_rightMap :
    (E.reindexOriginal eX eY eZ).rightMap = fun z => E.rightMap (eZ z) := rfl

@[simp] theorem reindexOriginal_value
    (x : X' × (Prefix × PX)) (y : Y' × (Prefix × PY)) (z : Z' × (Prefix × PZ)) :
    (E.reindexOriginal eX eY eZ).value x y z =
      E.value (eX x.1, x.2) (eY y.1, y.2) (eZ z.1, z.2) := rfl

end OriginalCoordinates

section Support

variable (support' : X → Y → Z → Prop)
variable (h : ∀ x y z, support' x y z → support x y z)

def onSupport : Execution X Y Z Prefix PX PY PZ AX AY AZ support' where
  auxiliary := E.auxiliary
  rankBound := E.rankBound
  auxiliary_rank := E.auxiliary_rank
  order := E.order
  leftDegree := E.leftDegree
  middleDegree := E.middleDegree
  rightDegree := E.rightDegree
  leftMap := E.leftMap
  middleMap := E.middleMap
  rightMap := E.rightMap
  left_degree := E.left_degree
  middle_degree := E.middle_degree
  right_degree := E.right_degree
  value := E.value
  vanishes := fun x y z hs j hj => E.vanishes x y z (h x.1 y.1 z.1 hs) j hj
  leading := fun x y z hs => E.leading x y z (h x.1 y.1 z.1 hs)
  synchronized := fun x y z hs hn => E.synchronized x y z (h x.1 y.1 z.1 hs) hn

@[simp] theorem onSupport_auxiliary : (E.onSupport support' h).auxiliary = E.auxiliary := rfl
@[simp] theorem onSupport_rankBound : (E.onSupport support' h).rankBound = E.rankBound := rfl
@[simp] theorem onSupport_order : (E.onSupport support' h).order = E.order := rfl
@[simp] theorem onSupport_leftDegree : (E.onSupport support' h).leftDegree = E.leftDegree := rfl
@[simp] theorem onSupport_middleDegree : (E.onSupport support' h).middleDegree = E.middleDegree := rfl
@[simp] theorem onSupport_rightDegree : (E.onSupport support' h).rightDegree = E.rightDegree := rfl
@[simp] theorem onSupport_leftMap : (E.onSupport support' h).leftMap = E.leftMap := rfl
@[simp] theorem onSupport_middleMap : (E.onSupport support' h).middleMap = E.middleMap := rfl
@[simp] theorem onSupport_rightMap : (E.onSupport support' h).rightMap = E.rightMap := rfl
@[simp] theorem onSupport_value : (E.onSupport support' h).value = E.value := rfl

end Support

end PolynomialKernelExecution.Execution
end MatrixMultiplication.Foundation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Tensor_MatrixBalancing
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.boundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.cyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.CWPrimitiveDegeneration.twiceCyclicBoundaryApproximation_polynomial _root_.OAI.MatrixMultiplication.Foundation.ExecutionPairingBudget.MatrixCoordinates.standard_tensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite coefficient tensors and their algebraic transformations. -/

noncomputable section

namespace MatrixMultiplication.MatrixBalancing

open MatrixMultiplication.Foundation
open MatrixMultiplication.Foundation.Tensor

variable {K X Y Z : Type*} [Field K]
variable {r d D : ℕ}

def swapXYApproximation {T : Tensor K X Y Z}
    (P : PolynomialApproximation T r d D) :
    PolynomialApproximation (Tensor.swapXY T) r d D where
  polynomial := Tensor.swapXY P.polynomial
  rank_bound := P.rank_bound.swapXY
  vanishes := fun y x z k hk => P.vanishes x y z k hk
  leading := fun y x z => P.leading x y z
  degree_bound := fun y x z => P.degree_bound x y z

theorem swapXY_directSum {ι : Type*} [DecidableEq ι]
    (T : ι → Tensor K X Y Z) :
    Tensor.swapXY (Tensor.directSum T) =
      Tensor.directSum (fun i => Tensor.swapXY (T i)) := by
  funext x y z
  have hguard : (y.1 = x.1 ∧ y.1 = z.1) ↔ (x.1 = y.1 ∧ x.1 = z.1) := by
    constructor
    · rintro ⟨hyx, hyz⟩
      exact ⟨hyx.symm, hyx.symm.trans hyz⟩
    · rintro ⟨hxy, hxz⟩
      exact ⟨hxy.symm, hxy.symm.trans hxz⟩
  simp only [Tensor.swapXY, Tensor.directSum, hguard]
  split_ifs with h
  · rw [h.1]
  · rfl

def directSum_swapXY {ι : Type*} [DecidableEq ι]
    {T : ι → Tensor K X Y Z}
    (P : PolynomialApproximation (Tensor.directSum T) r d D) :
    PolynomialApproximation (Tensor.directSum (fun i => Tensor.swapXY (T i))) r d D := by
  simpa only [swapXY_directSum] using swapXYApproximation P

section Matrix

variable {ι A B C : Type*} [DecidableEq ι]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem matrix_swapYZ :
    Tensor.pullback (Prod.swap : B × A → A × B)
      (Prod.swap : A × C → C × A) (Prod.swap : C × B → B × C)
      (Tensor.cyclic (Tensor.swapXY (matrixCoefficients (K := K) A B C))) =
        matrixCoefficients (K := K) B A C := by
  funext x y z
  simp only [Tensor.pullback, Tensor.cyclic, Tensor.swapXY, Prod.swap,
    matrixCoefficients]
  simp only [eq_comm, and_comm, and_left_comm]

theorem matrix_swapXZ :
    Tensor.pullback (Prod.swap : A × C → C × A)
      (Prod.swap : C × B → B × C) (Prod.swap : B × A → A × B)
      (Tensor.swapXY (Tensor.cyclic (matrixCoefficients (K := K) A B C))) =
        matrixCoefficients (K := K) A C B := by
  funext x y z
  simp only [Tensor.pullback, Tensor.cyclic, Tensor.swapXY, Prod.swap,
    matrixCoefficients]
  simp only [eq_comm, and_comm, and_left_comm, and_assoc]

def matrixDirectSum_swapYZ
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) B A C)) r d D := by
  have h := (directSum_swapXY P).directSum_cyclic.directSum_pullback
    (Prod.swap : B × A → A × B) (Prod.swap : A × C → C × A)
    (Prod.swap : C × B → B × C)
  simpa only [matrix_swapYZ] using h

def matrixDirectSum_swapXZ
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A C B)) r d D := by
  have h := (directSum_swapXY P.directSum_cyclic).directSum_pullback
    (Prod.swap : A × C → C × A) (Prod.swap : C × B → B × C)
    (Prod.swap : B × A → A × B)
  simpa only [matrix_swapXZ] using h

def matrixDirectSum_reindex {κ A' B' C' : Type*}
    [DecidableEq κ] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D)
    (e : κ → ι) (he : Function.Injective e)
    (f : A' → A) (hf : Function.Injective f)
    (g : B' → B) (hg : Function.Injective g)
    (j : C' → C) (hj : Function.Injective j) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : κ => matrixCoefficients (K := K) A' B' C')) r d D := by
  have h := P.pullback
    (fun x : κ × (A' × B') => (e x.1, (f x.2.1, g x.2.2)))
    (fun y : κ × (B' × C') => (e y.1, (g y.2.1, j y.2.2)))
    (fun z : κ × (C' × A') => (e z.1, (j z.2.1, f z.2.2)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x y z
  simp only [Tensor.pullback, Tensor.directSum, matrixCoefficients,
    he.eq_iff, hf.eq_iff, hg.eq_iff, hj.eq_iff]

def matrixDirectSum_product {κ A' B' C' : Type*}
    [DecidableEq κ] [DecidableEq A'] [DecidableEq B'] [DecidableEq C']
    {s e E : ℕ}
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D)
    (Q : PolynomialApproximation
      (Tensor.directSum (fun _ : κ => matrixCoefficients (K := K) A' B' C')) s e E) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : ι × κ =>
        matrixCoefficients (K := K) (A × A') (B × B') (C × C')))
      (r * s) (d + e) (D + E) := by
  have h := (P.directSum_product Q).directSum_pullback
    (fun x : (A × A') × (B × B') => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
    (fun y : (B × B') × (C × C') => ((y.1.1, y.2.1), (y.1.2, y.2.2)))
    (fun z : (C × C') × (A × A') => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x y z
  simp only [Tensor.directSum, Tensor.pullback, matrixCoefficients_product]

def matrixDirectSum_balanced
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : ι => matrixCoefficients (K := K) A B C)) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : ι × ι =>
        matrixCoefficients (K := K) (A × B) (C × C) (A × B)))
      (r ^ 2) (2 * d) (2 * D) := by
  have h := matrixDirectSum_swapXZ (matrixDirectSum_product P (matrixDirectSum_swapYZ P))
  have h' := matrixDirectSum_reindex h
    (Equiv.refl (ι × ι)) (Equiv.refl _).injective
    (Equiv.refl (A × B)) (Equiv.refl _).injective
    (Equiv.refl (C × C)) (Equiv.refl _).injective
    (Equiv.prodComm A B) (Equiv.prodComm A B).injective
  simpa only [pow_two, two_mul] using h'

end Matrix

def finiteBalanced {L a b c : ℕ}
    (P : PolynomialApproximation
      (Tensor.directSum (fun _ : Fin L =>
        matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c))) r d D) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : Fin (L ^ 2) =>
        matrixCoefficients (K := K) (Fin (a * b)) (Fin (c ^ 2)) (Fin (a * b))))
      (r ^ 2) (2 * d) (2 * D) := by
  let tags : Fin (L ^ 2) ≃ Fin L × Fin L := Fintype.equivOfCardEq (by simp [pow_two])
  let outer : Fin (a * b) ≃ Fin a × Fin b := Fintype.equivOfCardEq (by simp)
  let inner : Fin (c ^ 2) ≃ Fin c × Fin c := Fintype.equivOfCardEq (by simp [pow_two])
  exact matrixDirectSum_reindex (matrixDirectSum_balanced P)
    tags tags.injective outer outer.injective inner inner.injective outer outer.injective

end MatrixMultiplication.MatrixBalancing

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_ComplexBounds_CW75ReorderedBalanced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedBalanced

open MatrixMultiplication.Foundation CW75LabelHierarchy MatrixBalancing

def witness (counts : Scalar → ℕ) (t : ℕ) : ComplexWitness.FiniteRectangularWitness where
  outer := CW75ReorderedFinite.rows counts t * CW75ReorderedFinite.inner counts t
  inner := CW75ReorderedFinite.columns counts t ^ 2
  multiplicity := CW75ReorderedFinite.copies counts t ^ 2
  rank := CW75ReorderedFinite.rankBudget counts t ^ 2
  outer_pos := Nat.mul_pos (CW75ReorderedFinite.rows_pos counts t)
    (CW75ReorderedFinite.inner_pos counts t)
  inner_pos := pow_pos (CW75ReorderedFinite.columns_pos counts t) 2
  multiplicity_pos := pow_pos (CW75ReorderedFinite.copies_pos counts t) 2
  rank_pos := pow_pos (CW75ReorderedFinite.rankBudget_pos counts t) 2
  order := 2 * CW75ReorderedFinite.order counts t
  degree := 2 * CW75ReorderedFinite.degree counts t
  approximation := finiteBalanced (CW75ReorderedFinite.approximation counts t)

@[simp] theorem witness_outer (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).outer =
      CW75ReorderedFinite.rows counts t * CW75ReorderedFinite.inner counts t := rfl

@[simp] theorem witness_inner (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).inner = CW75ReorderedFinite.columns counts t ^ 2 := rfl

@[simp] theorem witness_multiplicity (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).multiplicity = CW75ReorderedFinite.copies counts t ^ 2 := rfl

@[simp] theorem witness_rank (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).rank = CW75ReorderedFinite.rankBudget counts t ^ 2 := rfl

end MatrixMultiplication.CW75ReorderedBalanced

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_Information
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualInformation

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

universe u v w

variable {A : Type u} [Fintype A] {X : Type w} [Fintype X]

def ConditionalIndependent {R L : Type*} [Fintype R] [Fintype L]
    (p : FiniteLaw A) (prior : A → R) (label : A → L) (x : A → X) : Prop :=
  ∀ r, 0 < (p.map prior).mass r → ∀ l xx,
    ((p.conditional prior r).map (fun a => (label a, x a))).mass (l, xx) =
      ((p.conditional prior r).map label).mass l *
        ((p.conditional prior r).map x).mass xx

def ConditionalMassFactorization {R L : Type*} [Fintype R] [Fintype L]
    (p : FiniteLaw A) (prior : A → R) (label : A → L) (x : A → X) : Prop :=
  ∀ r l xx,
    (p.map (fun a => (prior a, (label a, x a)))).mass (r, (l, xx)) *
        (p.map prior).mass r =
      (p.map (fun a => (prior a, label a))).mass (r, l) *
        (p.map (fun a => (prior a, x a))).mass (r, xx)

variable {Label : ℕ → Type v} [∀ n, Fintype (Label n)]

def remainingEntropy (p : FiniteLaw A) (labels : ∀ n, A → Label n)
    (x : A → X) (n : ℕ) : ℝ :=
  finiteEntropy (p.map (fun a => (labelRecordOf labels n a, x a))).mass -
    finiteEntropy (p.map (labelRecordOf labels n)).mass

end MatrixMultiplication.DualInformation

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_ProgramIndependence
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualProgramIndependence

universe u v w z

open MatrixMultiplication.Foundation DualInformation CompletionProductLaws
open CompletionColorLaws CompletionLabels RecursiveCompletion
open DualUniformProducts
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {I : Type*} [Fintype I] [DecidableEq I]
  {A : I → Type u} {R : I → Type v} {L : I → Type w} {X : I → Type z}
  [∀ i, Fintype (A i)] [∀ i, Fintype (R i)]
  [∀ i, Fintype (L i)] [∀ i, Fintype (X i)]

section ProgramInvariant

variable {SX SY SZ : Type u} [Fintype SX] [Fintype SY] [Fintype SZ]

def ProgramLawsIndependent (S : FlaggedTensor SX SY SZ) (r : ReadableTensor S)
    (p : ∀ c, FiniteLaw (ColorSlice S c)) : Prop :=
  ∀ c, ∀ n : Fin r.depth, r.program.pair n.val = .yz →
    ConditionalMassFactorization (p c)
      (fun a => labelRecordOf r.program.labels n.val a.val)
      (fun a => r.program.labels n.val a.val)
      (fun a => a.val.val.1)

end ProgramInvariant

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_CompletionIndependence
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
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
open CompletionLaws CompletionColorLaws CompletionProductLaws
open DualInformation TopologicalFlatten
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

def slotPrior (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (i : Fin m) (k : ℕ) (j : Fin m) (a : Leaf S) :
    Color × LabelRecord (fun _ => Code) (slotCut depth k i j) :=
  (leafColor S a, labelRecordOf p.labels (slotCut depth k i j) a)

def slotLabel (S : FlaggedTensor X Y Z)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (i : Fin m) (k : ℕ) (j : Fin m) (a : Leaf S) : Code :=
  if j = i then p.labels k a else default

def slotCompletionEvent (center output : Color) (i : Fin m) (k : ℕ)
    (r : ∀ j : Fin m, Color × LabelRecord (fun _ => Code) (slotCut depth k i j)) : Prop :=
  raisedFlag center output (fun j => (r j).1 = output) ∧
    ∀ j, (r j).1 = center ∨ (r j).1 = output

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_CompletionLaws
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CompletionTermination.retainedLeafEquiv_coordinates
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

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

abbrev Laws (S : FlaggedTensor X Y Z) := ∀ c, FiniteLaw (ColorSlice S c)

def minusLaws (S : FlaggedTensor X Y Z) (p : Laws S) (m : ℕ) (hm : 0 < m)
    (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) : Laws (complete S .B m)
  | .B => conditionalCompletionLaw S .B .B (p .B) (p .B) m hm 0 (by norm_num) (by norm_num)
  | .A => conditionalCompletionLaw S .B .A (p .B) (p .A) m hm rho hrho0.le hrho1
  | .C => conditionalCompletionLaw S .B .C (p .B) (p .C) m hm rho hrho0.le hrho1

def plusALaws (S : FlaggedTensor X Y Z) (p : Laws S) (m : ℕ) (hm : 0 < m)
    (rho hA hC : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) : Laws (complete S .A m)
  | .B => conditionalCompletionLaw S .A .B (p .A) (p .B) m hm (1 - rho)
      (sub_nonneg.mpr hrho1.le) (by linarith)
  | .A => conditionalCompletionLaw S .A .A (p .A) (p .A) m hm 0 (by norm_num) (by norm_num)
  | .C => conditionalCompletionLaw S .A .C (p .A) (p .C) m hm (gibbsWeight hA hC)
      (gibbsWeight_nonneg hA hC) (gibbsWeight_lt_one hA hC)

def plusCLaws (S : FlaggedTensor X Y Z) (p : Laws S) (m : ℕ) (hm : 0 < m)
    (rho hA hC : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) : Laws (complete S .C m)
  | .B => conditionalCompletionLaw S .C .B (p .C) (p .B) m hm (1 - rho)
      (sub_nonneg.mpr hrho1.le) (by linarith)
  | .A => conditionalCompletionLaw S .C .A (p .C) (p .A) m hm (gibbsWeight hC hA)
      (gibbsWeight_nonneg hC hA) (gibbsWeight_lt_one hC hA)
  | .C => conditionalCompletionLaw S .C .C (p .C) (p .C) m hm 0 (by norm_num) (by norm_num)

def baseLeaf : (c : Color) → ColorSlice BaseTwo.flagged c
  | .B => ⟨⟨(1, 0, 0), by norm_num [BaseTwo.flagged, BaseTwo.tensor]⟩,
      by simp [leafColor, BaseTwo.flagged, BaseTwo.flagB]⟩
  | .A => ⟨⟨(0, 0, 1), by norm_num [BaseTwo.flagged, BaseTwo.tensor]⟩,
      by simp [leafColor, BaseTwo.flagged, BaseTwo.flagB, BaseTwo.flagA]⟩
  | .C => ⟨⟨(0, 1, 0), by norm_num [BaseTwo.flagged, BaseTwo.tensor]⟩,
      by simp [leafColor, BaseTwo.flagged, BaseTwo.flagB, BaseTwo.flagA]⟩

def baseLaws : Laws BaseTwo.flagged := fun c => FiniteLaw.pure (baseLeaf c)

def script2 : Script := .step .base .B 2
def script4 : Script := .step script2 .A 2
def script8 : Script := .step script4 .C 2
def script24 : Script := .step script8 .B 3
def script48 : Script := .step script24 .C 2
def script96 : Script := .step script48 .B 2

def laws2 : Laws (Script.tensor BaseTwo.flagged script2) :=
  minusLaws BaseTwo.flagged baseLaws 2 (Nat.zero_lt_succ 1) (1 / 2) (by norm_num) (by norm_num)

def laws4 : Laws (Script.tensor BaseTwo.flagged script4) :=
  plusALaws (Script.tensor BaseTwo.flagged script2) laws2 2 (Nat.zero_lt_succ 1)
    DualWitness.state2.rho DualWitness.state2.hA DualWitness.state2.hC
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])
    (by norm_num [DualWitness.state2, DualWitness.initial, DualWitness.minus])

def laws8 : Laws (Script.tensor BaseTwo.flagged script8) :=
  plusCLaws (Script.tensor BaseTwo.flagged script4) laws4 2 (Nat.zero_lt_succ 1)
    DualWitness.state4.rho DualWitness.state4.hA DualWitness.state4.hC
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])
    (by norm_num [DualWitness.state4, DualWitness.state2, DualWitness.initial,
      DualWitness.minus, DualWitness.plusA])

def laws24 : Laws (Script.tensor BaseTwo.flagged script24) :=
  minusLaws (Script.tensor BaseTwo.flagged script8) laws8 3 (Nat.zero_lt_succ 2)
    DualWitness.state8.rho
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.1)
    (by rw [DualWitness.state8_rho]; exact DualWitness.rho8_range.2)

def laws48 : Laws (Script.tensor BaseTwo.flagged script48) :=
  plusCLaws (Script.tensor BaseTwo.flagged script24) laws24 2 (Nat.zero_lt_succ 1)
    DualWitness.state24.rho DualWitness.state24.hA DualWitness.state24.hC
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.1)
    (by rw [DualWitness.state24_rho]; exact DualWitness.rho24_range.2)

def laws96 : Laws (Script.tensor BaseTwo.flagged script96) :=
  minusLaws (Script.tensor BaseTwo.flagged script48) laws48 2 (Nat.zero_lt_succ 1)
    DualWitness.state48.rho
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.1)
    (by rw [DualWitness.state48_rho]; exact DualWitness.rho48_range.2)

def laws288 : Laws (Script.tensor BaseTwo.flagged Script.dual) :=
  plusALaws (Script.tensor BaseTwo.flagged script96) laws96 3 (Nat.zero_lt_succ 2)
    DualWitness.state96.rho DualWitness.state96.hA DualWitness.state96.hC
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.1)
    (by rw [DualWitness.state96_rho]; exact DualWitness.rho96_range.2)

end MatrixMultiplication.DualCompletionLaws

end

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

structure ActualFamily (k budget : ℝ) where
  witness : ℕ → ComplexWitness.FiniteRectangularWitness
  scale : ℕ → ℝ
  outerRate : ℝ
  innerRate : ℝ
  multiplicityRate : ℝ
  rankRate : ℝ
  scale_positive : ∀ᶠ n in atTop, 0 < scale n
  outer_positive : 0 < outerRate
  outer_limit : Tendsto
    (fun n => Real.log ((witness n).outer : ℝ) / scale n) atTop (𝓝 outerRate)
  inner_limit : Tendsto
    (fun n => Real.log ((witness n).inner : ℝ) / scale n) atTop (𝓝 innerRate)
  multiplicity_limit : Tendsto
    (fun n => Real.log ((witness n).multiplicity : ℝ) / scale n) atTop (𝓝 multiplicityRate)
  rank_limit : Tendsto
    (fun n => Real.log ((witness n).rank : ℝ) / scale n) atTop (𝓝 rankRate)
  aspect_gap : k * outerRate < innerRate
  cost_bound : rankRate - multiplicityRate ≤ budget * outerRate

end MatrixMultiplication.DualExponentBound

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_FiniteRealization
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionLabels.leafFintype _root_.OAI.MatrixMultiplication.CompletionLabels.retainedLeafFintype _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_inner _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_multiplicity _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_outer _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_rank _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualFiniteRealization

open MatrixMultiplication.Foundation RecursiveCompletion
open CompletionHierarchyWords CompletionExecution CompletionFiniteRealization
open scoped BigOperators Classical

variable {A X Y Z : Type} [Fintype A]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ) (t : ℕ)
variable (complete : Function.Injective (labelRecordOf H.labels H.depth))
variable [Fintype X] [Fintype Y] [Fintype Z]

def rankBudget (R : ℕ) : ℕ :=
  R ^ CompletionFiniteRealization.blocks counts t * (realize H counts t).execution.rankBound

def sourcePower {T : Tensor ℂ X Y Z} {R d D : ℕ}
    (source : Tensor.PolynomialApproximation T R d D) :
    Tensor.PolynomialApproximation
      (Tensor.power T (CompletionFiniteRealization.blocks counts t))
      (R ^ CompletionFiniteRealization.blocks counts t)
      (d * CompletionFiniteRealization.blocks counts t)
      (D * CompletionFiniteRealization.blocks counts t) :=
  source.power (CompletionFiniteRealization.blocks counts t)

def approximation {T : Tensor ℂ X Y Z} {R d D : ℕ}
    (source : Tensor.PolynomialApproximation T R d D)
    (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1) :
    Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin (copies H counts t) =>
        Tensor.matrixCoefficients (K := ℂ)
          (Fin (rows H counts t)) (Fin (inner H counts t)) (Fin (columns H counts t))))
      (rankBudget H counts t R) (order H counts t d) (degree H counts t D) := by
  have hs : ∀ x y z, ¬ support H counts t x y z →
      Tensor.power T (CompletionFiniteRealization.blocks counts t) x y z = 0 := by
    intro x y z outside
    by_contra nonzero
    apply outside
    intro i
    exact supported _ _ _ ((Finset.prod_ne_zero_iff.mp nonzero) i (Finset.mem_univ i))
  have full := ExecutionApproximation.approximation (realize H counts t).execution
    (sourcePower counts t source) hs
  have selected := full.pullback (leftSelect H counts t complete)
    (middleSelect H counts t complete) (rightSelect H counts t complete)
  rw [selected_output H counts t complete T unit] at selected
  exact selected

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem rankBudget_pos {R : ℕ} (hR : 0 < R) : 0 < rankBudget H counts t R :=
  Nat.mul_pos (pow_pos hR _) (auxiliaryRank_pos H counts t)

def witness {T : Tensor ℂ X Y Z} {R d D : ℕ}
    (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
    (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1) :
    ComplexWitness.FiniteRectangularWitness where
  outer := rows H counts t * inner H counts t
  inner := columns H counts t ^ 2
  multiplicity := copies H counts t ^ 2
  rank := rankBudget H counts t R ^ 2
  outer_pos := Nat.mul_pos (dimensions_positive H counts t).1
    (dimensions_positive H counts t).2.1
  inner_pos := pow_pos (dimensions_positive H counts t).2.2 2
  multiplicity_pos := pow_pos (copies_pos H counts t complete) 2
  rank_pos := pow_pos (rankBudget_pos H counts t hR) 2
  order := 2 * order H counts t d
  degree := 2 * degree H counts t D
  approximation := MatrixBalancing.finiteBalanced
    (approximation H counts t complete source supported unit)

section Projections

variable {T : Tensor ℂ X Y Z} {R d D : ℕ}
variable (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
variable (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)

@[simp] theorem witness_outer :
    (witness H counts t complete source hR supported unit).outer =
      rows H counts t * inner H counts t := rfl

@[simp] theorem witness_inner :
    (witness H counts t complete source hR supported unit).inner = columns H counts t ^ 2 := rfl

@[simp] theorem witness_multiplicity :
    (witness H counts t complete source hR supported unit).multiplicity = copies H counts t ^ 2 :=
  rfl

@[simp] theorem witness_rank :
    (witness H counts t complete source hR supported unit).rank =
      (R ^ CompletionFiniteRealization.blocks counts t *
        (realize H counts t).execution.rankBound) ^ 2 := rfl

theorem witness_dimensions :
    (witness H counts t complete source hR supported unit).outer =
      ConditionalLabels.stagePairingSize counts H.labels H.depth
        (fun n => H.pair n.val) .xz t *
      ConditionalLabels.stagePairingSize counts H.labels H.depth
        (fun n => H.pair n.val) .xy t ∧
    (witness H counts t complete source hR supported unit).inner =
      ConditionalLabels.stagePairingSize counts H.labels H.depth
        (fun n => H.pair n.val) .yz t ^ 2 := by
  rcases realize_dimensions H counts t with ⟨hr, hi, hc⟩
  change (realize H counts t).shape.rows * (realize H counts t).shape.inner = _ ∧
    (realize H counts t).shape.columns ^ 2 = _
  simp only [hr, hi, hc, and_self]

end Projections

def dualSource :
    Tensor.PolynomialApproximation (Script.tensor BaseTwo.flagged Script.dual).tensor
      (2 ^ 288) (Script.dual.order 1) (Script.dual.degree 3) := by
  simpa only [Script.dual_factors] using
    Script.approximation BaseTwo.flagged BaseTwo.approximation Script.dual

end MatrixMultiplication.DualFiniteRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_ConditionalRateBridge
attribute [-instance] _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.labelRecordZero_subsingleton
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_auxiliaryRank _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_columns _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_inner _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_multiplicity _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_occurrences _root_.OAI.MatrixMultiplication.CompletionFiniteRealization.realization_rows _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_inner _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_multiplicity _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_outer _root_.OAI.MatrixMultiplication.DualFiniteRealization.witness_rank _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendCode_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.appendPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.decodedFine_eq_geometryDecode _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.encodeSourceWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.finePrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.mem_conditionalFinset _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.oldPrefix_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.rootPrefixWord_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_apply_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourcePrefixEquiv_symm_val _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_encodeSourceWord _root_.OAI.MatrixMultiplication.Foundation.ConditionalPrefixWords.sourceSymbol_record
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

namespace MatrixMultiplication.ConditionalLabels

open MatrixMultiplication.Foundation Filter StageHierarchyResources HierarchySeparationRates
open LabelHierarchyCounts
open scoped BigOperators Topology Classical

universe u v
variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

def normalizedCountLaw (counts : A → ℕ) (hD : 0 < ∑ a, counts a) : FiniteLaw A where
  mass a := (counts a : ℝ) / (∑ b, counts b : ℕ)
  nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  total := by
    rw [← Finset.sum_div, ← Nat.cast_sum]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD))

@[simp] theorem normalizedCountLaw_mass (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (a : A) :
    (normalizedCountLaw counts hD).mass a =
      (counts a : ℝ) / (∑ b, counts b : ℕ) := rfl

theorem normalized_prefix_mass (counts : A → ℕ) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (n : ℕ) (r : LabelRecord Label n) :
    (p.map (labelRecordOf labels n)).mass r =
      (sourcePrefixCounts counts labels n r : ℝ) / (∑ a, counts a : ℕ) := by
  simp only [FiniteLaw.map_mass, mass, sourcePrefixCounts, pushforwardCounts,
    Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : labelRecordOf labels n a = r <;> simp [h]

theorem tendsto_log_prefix_multinomial (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (n : ℕ) :
    Tendsto (fun t : ℕ => Real.log
      (Nat.multinomial Finset.univ
        (sourcePrefixCounts (fun a => t * counts a) labels n) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy (p.map (labelRecordOf labels n)).mass)) := by
  have hsum : (∑ r, sourcePrefixCounts counts labels n r) = ∑ a, counts a :=
    pushforwardCounts_sum counts (labelRecordOf labels n)
  have hpositive : 0 < ∑ r, sourcePrefixCounts counts labels n r := by rwa [hsum]
  have hmass : (fun r => (sourcePrefixCounts counts labels n r : ℝ) /
      (∑ r, sourcePrefixCounts counts labels n r : ℕ)) =
      (p.map (labelRecordOf labels n)).mass := by
    funext r
    rw [hsum]
    exact (normalized_prefix_mass counts p mass labels n r).symm
  have h := tendsto_log_multinomial_mul (sourcePrefixCounts counts labels n) hpositive
  rw [hmass, hsum] at h
  have hscale (t : ℕ) : sourcePrefixCounts (fun a => t * counts a) labels n =
      (fun r => t * sourcePrefixCounts counts labels n r) :=
    funext (sourcePrefixCounts_mul counts labels t n)
  simpa only [hscale] using h

theorem stageEntropyRate_div_eq_refinementEntropy (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (depth n : ℕ) (hn : n < depth) :
    stageEntropyRate counts labels n / (∑ a, counts a : ℕ) =
      (FiniteLabelHierarchy.ofLawLabels p labels depth).refinementEntropy n := by
  have hstage := (tendsto_log_stageRefinementCount_div counts labels n).div_const
    ((∑ a, counts a : ℕ) : ℝ)
  simp only [div_div] at hstage
  have hcoarse := tendsto_log_prefix_multinomial counts hD p mass labels n
  have hfine := tendsto_log_prefix_multinomial counts hD p mass labels (n + 1)
  have heq : finiteEntropy (p.map (labelRecordOf labels (n + 1))).mass =
      finiteEntropy (p.map (labelRecordOf labels n)).mass +
        stageEntropyRate counts labels n / (∑ a, counts a : ℕ) := by
    apply tendsto_nhds_unique hfine
    apply (hcoarse.add hstage).congr
    intro t
    rw [multinomial_succ (sourcePrefixCounts (fun a => t * counts a) labels) n
      (sourcePrefixCounts_compatible (fun a => t * counts a) labels n)]
    have hcoarse_pos : 0 < Nat.multinomial Finset.univ
        (sourcePrefixCounts (fun a => t * counts a) labels n) := Nat.multinomial_pos _ _
    have hrefinement_pos : 0 <
        refinementCount (sourcePrefixCounts (fun a => t * counts a) labels) n :=
      stageRefinementCount_pos counts labels n t
    rw [Nat.cast_mul, Real.log_mul
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hcoarse_pos))
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hrefinement_pos)), add_div]
    rfl
  have hchain := (FiniteLabelHierarchy.ofLawLabels p labels depth).prefixLaw_entropy_succ
    n (Nat.succ_le_of_lt hn)
  rw [FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass,
    FiniteLabelHierarchy.ofLawLabels_prefixLaw_mass] at hchain
  linarith

theorem stagePairingRate_div_eq_lawPairingRate (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    stagePairingRate counts labels depth reader pair / (∑ a, counts a : ℕ) =
      lawPairingRate p labels depth reader pair := by
  unfold stagePairingRate lawPairingRate pairingRate
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : reader n = pair
  · simp only [h, ite_true, if_true]
    exact stageEntropyRate_div_eq_refinementEntropy counts hD p mass labels depth n.val n.isLt
  · simp [h]

theorem tendsto_log_stagePairingSize_law (counts : A → ℕ)
    (hD : 0 < ∑ a, counts a) (p : FiniteLaw A)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
    (labels : ∀ n, A → Label n) (depth : ℕ)
    (reader : Fin depth → ReaderPair) (pair : ReaderPair) :
    Tendsto (fun t => Real.log (stagePairingSize counts labels depth reader pair t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (lawPairingRate p labels depth reader pair)) := by
  rw [← stagePairingRate_div_eq_lawPairingRate counts hD p mass labels depth reader pair]
  exact tendsto_log_stagePairingSize_normalized counts labels depth reader pair

end MatrixMultiplication.ConditionalLabels

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_FiniteRates
attribute [-simp] _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_inner _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_multiplicity _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_outer _root_.OAI.MatrixMultiplication.CW75ReorderedBalanced.witness_rank _root_.OAI.MatrixMultiplication.CW75ReorderedExecution.pairingProduct_zero _root_.OAI.MatrixMultiplication.CompletionProductLaws.independentProduct_mass _root_.OAI.MatrixMultiplication.CompletionProductLaws.sigmaJoint_mass _root_.OAI.MatrixMultiplication.Foundation.CW75InitialExecution.execution_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualFiniteRealization

open MatrixMultiplication.Foundation CompletionHierarchyWords CompletionExecution
open CompletionFiniteRealization StageHierarchyResources ConditionalLabels Filter
open scoped BigOperators Topology Classical

variable {A X Y Z : Type} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ)
variable (hD : 0 < ∑ a, counts a)
variable (complete : Function.Injective (labelRecordOf H.labels H.depth))
variable (p : FiniteLaw A)
variable (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))

def pairRate (pair : ReaderPair) : ℝ :=
  lawPairingRate p H.labels H.depth (fun n => H.pair n.val) pair

include hD complete mass in
omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem copies_limit :
    Tendsto (fun t : ℕ => Real.log (copies H counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (finiteEntropy p.mass)) := by
  have hmass : (fun a => (counts a : ℝ) / (∑ b, counts b : ℕ)) = p.mass :=
    (funext mass).symm
  simpa only [copies, realize_label_card H counts _ complete, hmass] using
    tendsto_log_exactWords_card_mul counts hD

include hD complete mass in
omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem auxiliary_limit :
    Tendsto (fun t : ℕ => Real.log ((realize H counts t).execution.rankBound : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (finiteEntropy p.mass)) := by
  have hmass : (fun a => (counts a : ℝ) / (∑ b, counts b : ℕ)) = p.mass :=
    (funext mass).symm
  simpa only [realize_rankBound, hmass] using
    tendsto_log_stageAuxiliaryBudget counts hD H.labels H.depth complete

include hD in
theorem source_rank_limit (R : ℕ) :
    Tendsto (fun t : ℕ =>
      Real.log ((R ^ CompletionFiniteRealization.blocks counts t : ℕ) : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (Real.log R)) := by
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  have htD : (t : ℝ) * (∑ a, counts a : ℕ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr ht) hD'
  rw [Nat.cast_pow, Real.log_pow, CompletionFiniteRealization.blocks, Nat.cast_mul]
  exact (mul_div_cancel_left₀ (Real.log R) htD).symm

include hD complete mass in
omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem rank_budget_limit {R : ℕ} (hR : 0 < R) :
    Tendsto (fun t : ℕ => Real.log (rankBudget H counts t R : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (Real.log R + finiteEntropy p.mass)) := by
  apply ((source_rank_limit counts hD R).add
    (auxiliary_limit H counts hD complete p mass)).congr
  intro t
  have hs : ((R ^ CompletionFiniteRealization.blocks counts t : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (Nat.ne_of_gt hR))
  have ha : ((realize H counts t).execution.rankBound : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (auxiliaryRank_pos H counts t))
  rw [rankBudget, Nat.cast_mul, Real.log_mul hs ha, add_div]

variable {T : Tensor ℂ X Y Z} {R d D : ℕ}
variable (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
variable (supported : ∀ x y z, T x y z ≠ 0 →
  ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)

include hD mass in
theorem witness_outer_limit :
    Tendsto (fun t : ℕ =>
      Real.log ((witness H counts t complete source hR supported unit).outer : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (pairRate H p .xy + pairRate H p .xz)) := by
  have hi := tendsto_log_stagePairingSize_law counts hD p mass H.labels H.depth
    (fun n => H.pair n.val) .xy
  have hr := tendsto_log_stagePairingSize_law counts hD p mass H.labels H.depth
    (fun n => H.pair n.val) .xz
  apply (hi.add hr).congr
  intro t
  rw [(witness_dimensions H counts t complete source hR supported unit).1,
    Nat.cast_mul, Real.log_mul]
  · ring
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (pairingSize_pos _ _ _ (fun n => stageRefinementCount_pos counts H.labels n.val t)))
  · exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (pairingSize_pos _ _ _ (fun n => stageRefinementCount_pos counts H.labels n.val t)))

include hD mass in
theorem witness_inner_limit :
    Tendsto (fun t : ℕ =>
      Real.log ((witness H counts t complete source hR supported unit).inner : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (2 * pairRate H p .yz)) := by
  apply ((tendsto_log_stagePairingSize_law counts hD p mass H.labels H.depth
    (fun n => H.pair n.val) .yz).const_mul 2).congr
  intro t
  rw [(witness_dimensions H counts t complete source hR supported unit).2,
    Nat.cast_pow, Real.log_pow]
  norm_num
  ring

include hD mass in
theorem witness_multiplicity_limit :
    Tendsto (fun t : ℕ =>
      Real.log ((witness H counts t complete source hR supported unit).multiplicity : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop (𝓝 (2 * finiteEntropy p.mass)) := by
  apply ((copies_limit H counts hD complete p mass).const_mul 2).congr
  intro t
  rw [witness_multiplicity, Nat.cast_pow, Real.log_pow]
  norm_num
  ring

include hD mass in
theorem witness_rank_limit :
    Tendsto (fun t : ℕ =>
      Real.log ((witness H counts t complete source hR supported unit).rank : ℝ) /
        ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (2 * (Real.log R + finiteEntropy p.mass))) := by
  apply ((rank_budget_limit H counts hD complete p mass hR).const_mul 2).congr
  intro t
  rw [witness_rank, Nat.cast_pow, Real.log_pow]
  simp only [rankBudget, Nat.cast_mul, Nat.cast_pow]
  norm_num
  ring

end MatrixMultiplication.DualFiniteRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_FamilyConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualFiniteRealization

open MatrixMultiplication.Foundation CompletionHierarchyWords Filter
open scoped BigOperators Topology Classical

variable {A X Y Z : Type} [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ)
variable (hD : 0 < ∑ a, counts a)
variable (complete : Function.Injective (labelRecordOf H.labels H.depth))
variable (p : FiniteLaw A)
variable (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ))
variable {T : Tensor ℂ X Y Z} {R d D : ℕ}
variable (source : Tensor.PolynomialApproximation T R d D) (hR : 0 < R)
variable (supported : ∀ x y z, T x y z ≠ 0 →
  ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)

def actualFamily {k budget : ℝ}
    (positive : 0 < pairRate H p .xy + pairRate H p .xz)
    (aspect : k * (pairRate H p .xy + pairRate H p .xz) < 2 * pairRate H p .yz)
    (cost : 2 * Real.log R ≤ budget * (pairRate H p .xy + pairRate H p .xz)) :
    DualExponentBound.ActualFamily k budget where
  witness := fun t => witness H counts t complete source hR supported unit
  scale := fun t => (t : ℝ) * (∑ a, counts a : ℕ)
  outerRate := pairRate H p .xy + pairRate H p .xz
  innerRate := 2 * pairRate H p .yz
  multiplicityRate := 2 * finiteEntropy p.mass
  rankRate := 2 * (Real.log R + finiteEntropy p.mass)
  scale_positive := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
    exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero ht)) (Nat.cast_pos.mpr hD)
  outer_positive := positive
  outer_limit := witness_outer_limit H counts hD complete p mass source hR supported unit
  inner_limit := witness_inner_limit H counts hD complete p mass source hR supported unit
  multiplicity_limit := witness_multiplicity_limit H counts hD complete p mass source hR supported unit
  rank_limit := witness_rank_limit H counts hD complete p mass source hR supported unit
  aspect_gap := aspect
  cost_bound := by simpa only [mul_add, add_sub_cancel_right] using cost

end MatrixMultiplication.DualFiniteRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_LawEntropy
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualLawEntropy

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionProductLaws CompletionLaws
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

universe u
variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

def allCenter (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (w : Fin m → Leaf S) : Prop := ∀ i, leafColor S (w i) = center

def centerWordEquiv (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ) :
    {w : Fin m → Leaf S // allCenter S center m w} ≃ (Fin m → ColorSlice S center) where
  toFun w i := ⟨w.val i, w.property i⟩
  invFun w := ⟨fun i => (w i).val, fun i => (w i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MatrixMultiplication.DualLawEntropy

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_HiddenRates
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualHiddenRates

universe u

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open DualCompletionLaws CompletionPartitions CompletionEntropyAlgebra
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} [Fintype X] [Fintype Y] [Fintype Z]

structure HiddenInvariant (S : FlaggedTensor X Y Z) (p : Laws S)
    (s : DualWitness.State) : Prop where
  B : finiteEntropy (p .B).mass = Real.log (activeCount S) + s.hB
  A : finiteEntropy (p .A).mass = Real.log (inactiveCount S) + s.hA
  C : finiteEntropy (p .C).mass = Real.log (inactiveCount S) + s.hC

end MatrixMultiplication.DualHiddenRates

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_Uniform
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
universe uCoord
namespace MatrixMultiplication.DualUniform

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualCompletionLaws
open CompletionPartitions
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type uCoord} [Fintype X] [Fintype Y] [Fintype Z]

structure UniformLaws (S : FlaggedTensor X Y Z) (p : Laws S) : Prop where
  B : UniformCoordinate (p .B) (fun a => a.val.val.1) S.flagB
  A : UniformCoordinate (p .A) (fun a => a.val.val.1) (fun x => ¬ S.flagB x)
  C : UniformCoordinate (p .C) (fun a => a.val.val.1) (fun x => ¬ S.flagB x)

end MatrixMultiplication.DualUniform

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_UniformInstances
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section
namespace MatrixMultiplication.DualUniform

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels CompletionColorLaws
open CompletionLaws DualCompletionLaws CompletionPartitions
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

theorem coord_nonempty (s : Script) : Nonempty (Script.Coord (Fin 2) s) := by
  induction s with
  | base => exact inferInstanceAs (Nonempty (Fin 2))
  | step prior center m ih =>
    let _ := ih
    exact inferInstanceAs (Nonempty (Fin m → Script.Coord (Fin 2) prior))
attribute [local instance] coord_nonempty

end MatrixMultiplication.DualUniform

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_ScriptIndependence
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
open CompletionColorLaws DualCompletionLaws DualInformation TopologicalFlatten DualUniform

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type u} {Code : Type w} [Fintype X] [Fintype Y] [Fintype Z]
  [Fintype Code] [Inhabited Code] {depth m : ℕ}

abbrev dualReadable (s : Script) :=
  ReadableTensor.script BaseTwo.flagged BaseConditionalReaders.baseTwoReadable s

end MatrixMultiplication.DualProgramIndependence

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessProgram
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels

abbrev Word := Script.Coord (Fin 2) Script.dual
def source : FlaggedTensor Word Word Word := Script.tensor BaseTwo.flagged Script.dual
abbrev Support := RetainedLeaf source .B .C

def readable : ReadableTensor source :=
  ReadableTensor.script BaseTwo.flagged BaseConditionalReaders.baseTwoReadable Script.dual

def program := terminationProgram source .B .C (by intro h; cases h)
  readable.program readable.context_eq readable.view_eq

def x (a : Support) : Word := a.val.val.1

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_Witness
attribute [-instance] _root_.OAI.MatrixMultiplication.CompletionTermination.leafFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitness

attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLaws CompletionColorLaws DualCompletionLaws

def law : FiniteLaw Support :=
  CompletionTerminationLaw.law source .B .C (laws288 .B) (laws288 .C) state288.rho
    (by rw [state288_rho]; exact rho288_range.1.le)
    (by rw [state288_rho]; exact rho288_range.2.le)

def rate (pair : ReaderPair) : ℝ :=
  ConditionalLabels.lawPairingRate law program.labels (1 + readable.depth)
    (fun n => program.pair n.val) pair

end MatrixMultiplication.DualWitness

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Duality_WitnessRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualWitnessRealization

open MatrixMultiplication.Foundation RecursiveCompletion CompletionLabels
open CompletionLabels.TopologicalFlatten CompletionHierarchyWords
open scoped BigOperators Classical

theorem program_context (a : DualWitness.Support) : DualWitness.program.context a = PUnit.unit :=
  rfl

theorem program_joint :
    Function.Injective (fun a : DualWitness.Support =>
      (DualWitness.program.view .B a, DualWitness.program.view .C a,
        DualWitness.program.view .A a)) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact h

def hierarchy :
    ReadableHierarchy DualWitness.Support DualWitness.Word DualWitness.Word DualWitness.Word :=
  ReadableHierarchy.ofProgram DualWitness.program PUnit.unit program_context program_joint

@[simp] theorem hierarchy_x (a : DualWitness.Support) : hierarchy.x a = a.val.val.1 := rfl
@[simp] theorem hierarchy_y (a : DualWitness.Support) : hierarchy.y a = a.val.val.2.1 := rfl
@[simp] theorem hierarchy_z (a : DualWitness.Support) : hierarchy.z a = a.val.val.2.2 := rfl

def tensor : Tensor ℂ DualWitness.Word DualWitness.Word DualWitness.Word :=
  CompletionTermination.tensor DualWitness.source .A

def retainedLeafEquiv : CompletionTermination.Leaf DualWitness.source .A ≃ DualWitness.Support :=
  CompletionTermination.retainedLeafEquiv DualWitness.source .A .B .C
    (by intro c; cases c <;> simp)

def approximation :
    Tensor.PolynomialApproximation tensor (2 ^ 288)
      (Script.dual.order 1) (Script.dual.degree 3) :=
  CompletionTermination.approximation DualWitness.source .A DualFiniteRealization.dualSource

end MatrixMultiplication.DualWitnessRealization

end

end OAI
end

section
-- module Solutions.Q235_MM.MatrixMultiplication_Entropy_CurveLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.CurveLaws

open MatrixMultiplication.Foundation ComplexWitness

theorem fiberSize_real_pos (u : CurveCoordinate) : (0 : ℝ) < curveFiberSize u := by
  exact_mod_cast curveFiberSize_pos u

def uniformLift (p : FiniteLaw CurveCoordinate) : FiniteLaw CurveLeaf where
  mass s := p.mass (CW75LabelHierarchy.x s) / curveFiberSize (CW75LabelHierarchy.x s)
  nonneg s := div_nonneg (p.nonneg _) (fiberSize_real_pos _).le
  total := by
    rw [sum_curveLeaves_by_X (fun u => p.mass u / (curveFiberSize u : ℝ))]
    simpa only [mul_div_cancel₀ _ (fiberSize_real_pos _).ne'] using p.total

def partition (t : ℝ) : ℝ :=
  ∑ u : CurveCoordinate, (curveFiberSize u : ℝ) ^ t

theorem partition_pos (t : ℝ) : 0 < partition t := by
  apply Finset.sum_pos
  · intro u _
    exact Real.rpow_pos_of_pos (fiberSize_real_pos u) t
  · exact Finset.univ_nonempty

def marginal (t : ℝ) : FiniteLaw CurveCoordinate where
  mass u := (curveFiberSize u : ℝ) ^ t / partition t
  nonneg u := div_nonneg (Real.rpow_pos_of_pos (fiberSize_real_pos u) t).le
    (partition_pos t).le
  total := by
    rw [← Finset.sum_div]
    exact div_self (partition_pos t).ne'

def leafLaw (t : ℝ) : FiniteLaw CurveLeaf := uniformLift (marginal t)

def hidden (t : ℝ) : ℝ :=
  ∑ u : CurveCoordinate, (marginal t).mass u * Real.log (curveFiberSize u)

def incident (t : ℝ) : ℝ := Real.log (partition t) - t * hidden t

end MatrixMultiplication.CurveLaws

end

end OAI
end


