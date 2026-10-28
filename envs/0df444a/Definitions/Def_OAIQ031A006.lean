-- Prove2me | Definitions.Def_OAIQ031A006
-- name    : OAIQ031A006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:58:49.420223+00:00
-- url     : https://prove2.me/theorems/c6973478-47a0-404f-afa8-0dc12851a7d6
-- title:
--   Definitions bundle OAIQ031A006 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 20 definitions, 2 inductive types or structures, 3 instances and 36 theorems. The definitions and types are `OAI.ArExplicit.A.quotientCoordinates`, `OAI.ArExplicit.CocycleData.PairMonomial`, `OAI.ArExplicit.CocycleData.PairMonomial.number`, `OAI.ArExplicit.CocycleData.boundaryRightContributions`, `OAI.ArExplicit.CocycleData.multiplicationCoefficient`, `OAI.ArExplicit.CocycleData.selected`, `OAI.ArExplicit.CocycleData.zSelected`, `OAI.ArExplicit.CompleteCokernel`, `OAI.ArExplicit.CompleteComparison.fullHomCoboundaries`, `OAI.ArExplicit.CompleteComparison.leftShiftCocycleLinearEquiv`, `OAI.ArExplicit.CompleteComparison.leftShiftCohomologyEquiv`, `OAI.ArExplicit.ExternalTensor.forgetComplex`, `OAI.ArExplicit.ExternalTensor.forgetField`, `OAI.ArExplicit.ExternalTensor.scalarTotal`, `OAI.ArExplicit.LinearHomology.cycleMap`, `OAI.ArExplicit.ProjectiveNullhomotopyAbove.Pair`, `OAI.ArExplicit.TIndex.lowerSource`, `OAI.ArExplicit.TIndex.lowerTarget`, `OAI.ArExplicit.TIndex.weight`, `OAI.ArExplicit.TrivialExtension.coordinateLinearEquiv`, `OAI.ArExplicit.TwoCone.FourthCokernel`, `OAI.ArExplicit.TwoCone.restrictedSource`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_TMultiplication`, `AuslanderReiten_Algebras_TensorStructure`, `AuslanderReiten_Algebras_TrivialExtension`, `AuslanderReiten_Bar_BarCasimir`, `AuslanderReiten_Cocycles_CocycleCorners`, `AuslanderReiten_Cocycles_CocycleFormula`, `AuslanderReiten_Cocycles_CocycleTwist`, `AuslanderReiten_Cocycles_SparseCocycle`, `AuslanderReiten_Cocycles_SparseParity`, `AuslanderReiten_Cocycles_TwistedBoundaryData`, `AuslanderReiten_Cocycles_TwistedBoundaryFormula`, `AuslanderReiten_Complete_CompleteResolutionTail`, `AuslanderReiten_Cones_TwoConeTail`, `AuslanderReiten_Cones_TwoConeTailRestriction`, `AuslanderReiten_Duality_LinearHomologyDuality`, `AuslanderReiten_HomComplex_FullHomLinear`, `AuslanderReiten_HomComplex_FullHomProducts`, `AuslanderReiten_HomComplex_FullHomShift`, `AuslanderReiten_Homology_ProjectiveNullhomotopyAbove`, `AuslanderReiten_Tensor_ExternalTensorBottomDifferential`, `AuslanderReiten_Tensor_ExternalTensorForget`.
--
--   **Imports.** It imports the bundle `OAIQ031A000` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A027`, `OAIQ031A030`, `OAIQ031A031`, `OAIQ031A033`, `OAIQ031A034`, `OAIQ031A035`, `OAIQ031A038`, `OAIQ031A039` and `OAIQ031A042`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TrivialExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]

namespace TrivialExtension

variable {k A}

theorem trace_mul (a b : TrivialExtension k A) :
    trace (a * b) = b.dual a.base + a.dual b.base := by simp

theorem trace_mul_comm (a b : TrivialExtension k A) : trace (a * b) = trace (b * a) := by
  simp only [trace_mul, add_comm]

def coordinateLinearEquiv : TrivialExtension k A ≃ₗ[k] A × Module.Dual k A where
  __ := coordinates
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Field

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

theorem traceForm_nondegenerate :
    (traceForm : LinearMap.BilinForm k (TrivialExtension k A)).Nondegenerate := by
  have left : ∀ a : TrivialExtension k A, (∀ b, traceForm a b = 0) → a = 0 := by
    intro a ha
    have hb : a.base = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff k a.base).mp
      intro φ
      simpa [trace_mul, inr] using ha (inr φ)
    have hd : a.dual = 0 := by
      ext b
      simpa [trace_mul, inl] using ha (inl b)
    exact TrivialExtension.ext hb hd
  constructor
  · exact left
  · intro a ha
    apply left a
    intro b
    rw [traceForm_apply, trace_mul_comm]
    exact ha b

instance instFinite [Module.Finite k A] : Module.Finite k (TrivialExtension k A) :=
  Module.Finite.equiv coordinateLinearEquiv.symm

end Field
end TrivialExtension

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

namespace Letter

theorem sum_univ {M : Type*} [AddCommMonoid M] (f : Letter → M) :
    ∑ i, f i = f .e + f .x + f .y + f .z + f .u +
      f .v + f .t + f .j + f .f + f .n := by
  change (∑ i ∈ ({.e, .x, .y, .z, .u, .v, .t, .j, .f, .n} : Finset Letter), f i) = _
  simp [add_assoc]

end Letter

namespace CocycleData

open BaseAlgebra TrivialExtension

variable {k : Type*} [Field k] (q : k)

def multiplicationCoefficient (a b : T k q) (i : TIndex) : k :=
  (multiplication.map fun m => if m.output = i then
    q ^ m.degree * T.coefficient q m.first a * T.coefficient q m.second b else 0).sum

theorem multiplication_false_e (a b : T k q) :
    T.coefficient q (false, .e) (a * b) = multiplicationCoefficient q a b (false, .e) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]

theorem multiplication_false_x (a b : T k q) :
    T.coefficient q (false, .x) (a * b) = multiplicationCoefficient q a b (false, .x) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

theorem multiplication_false_y (a b : T k q) :
    T.coefficient q (false, .y) (a * b) = multiplicationCoefficient q a b (false, .y) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

theorem multiplication_false_z (a b : T k q) :
    T.coefficient q (false, .z) (a * b) = multiplicationCoefficient q a b (false, .z) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

theorem multiplication_false_u (a b : T k q) :
    T.coefficient q (false, .u) (a * b) = multiplicationCoefficient q a b (false, .u) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]

theorem multiplication_false_v (a b : T k q) :
    T.coefficient q (false, .v) (a * b) = multiplicationCoefficient q a b (false, .v) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

theorem multiplication_false_t (a b : T k q) :
    T.coefficient q (false, .t) (a * b) = multiplicationCoefficient q a b (false, .t) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]

theorem multiplication_false_j (a b : T k q) :
    T.coefficient q (false, .j) (a * b) = multiplicationCoefficient q a b (false, .j) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

theorem multiplication_false_f (a b : T k q) :
    T.coefficient q (false, .f) (a * b) = multiplicationCoefficient q a b (false, .f) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]

theorem multiplication_false_n (a b : T k q) :
    T.coefficient q (false, .n) (a * b) = multiplicationCoefficient q a b (false, .n) := by
  simp [multiplicationCoefficient, multiplication, T.coefficient, BaseAlgebra.product]
  ring

end CocycleData
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

namespace A

variable {k : Type*} [Field k] (q : k)

noncomputable def quotientCoordinates : (k × k) ⊗[k] (k × k) ≃ₐ[k] (k × k) × (k × k) :=
  (Algebra.TensorProduct.prodRight k k (k × k) k k).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.rid k k (k × k))
      (Algebra.TensorProduct.rid k k (k × k)))

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCasimir
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

variable [CharP k 2]

theorem double_zero_p0 {V : Type u} [AddCommGroup V] [Module k V] (x : V) : x + x = 0 := by
  have htwo : (2 : k) = 0 := CharP.cast_eq_zero k 2
  rw [← two_smul k x, htwo, zero_smul]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SparseParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.SparseParity

variable {α : Type*}

theorem module_add_self_eq_zero {k M : Type*} [Semiring k] [CharP k 2]
    [AddCommMonoid M] [Module k M] (a : M) : a + a = 0 := by
  have htwo : (2 : k) = 0 := by simpa using CharP.cast_eq_zero k 2
  rw [← two_smul k a, htwo, zero_smul]

end ArExplicit.SparseParity

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SparseCocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

theorem linearMap_list_sum_apply {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (l : List (M →ₗ[R] N)) (a : M) : l.sum a = (l.map (fun f => f a)).sum := by
  induction l with
  | nil => rfl
  | cons f l ih => simp [List.sum_cons, ih]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCorners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit
namespace TIndex

def lowerSource : Letter → Bool
  | .e | .x | .y | .z | .u | .v => false
  | .t | .j | .f | .n => true

def lowerTarget : Letter → Bool
  | .e | .x | .y | .z | .t | .j => false
  | .u | .v | .f | .n => true

def weight (i : TIndex) : ℕ := if i.1 then 1 else 0

end TIndex

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {α β k : Type*} [Field k] (q : k)

theorem list_mul_sum (r : k) (l : List α) (f : α → k) :
    r * (l.map f).sum = (l.map fun x => r * f x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [mul_add, ih]

theorem list_sum_mul (r : k) (l : List α) (f : α → k) :
    (l.map f).sum * r = (l.map fun x => f x * r).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [add_mul, ih]

theorem list_sum_map_add_p0 {M : Type*} [AddCommMonoid M]
    (l : List α) (f g : α → M) :
    (l.map f).sum + (l.map g).sum = (l.map fun a => f a + g a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [← ih, add_assoc, add_left_comm]

theorem list_sum_flatMap_p0 {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem list_left_mul (a : T k q) (l : List α) (f : α → T k q) :
    a * (l.map f).sum = (l.map fun x => a * f x).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [mul_add, ih]

theorem list_right_mul_p0 (a : T k q) (l : List α) (f : α → T k q) :
    (l.map f).sum * a = (l.map fun x => f x * a).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [add_mul, ih]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleTwist
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

def selected : TIndex → Bool
  | (false, .u) | (false, .v) | (false, .t) => true
  | (true, .e) | (true, .x) | (true, .y) | (true, .z) | (true, .u) | (true, .v) => true
  | _ => false

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_TwistedBoundaryData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

def zSelected : TIndex → Bool
  | (false, .u) | (false, .v) | (false, .t) => true
  | (true, .e) | (true, .x) | (true, .y) | (true, .z) | (true, .u) | (true, .v) => true
  | _ => false

structure PairMonomial where
  first : TIndex
  second : TIndex
  output : TIndex
  qDegree : ℕ
  hDegree : ℕ
  deriving DecidableEq

def PairMonomial.number (p : PairMonomial) : ℕ :=
  p.first.number + 20 * (p.second.number + 20 * (p.output.number + 20 * (p.qDegree + 8 * p.hDegree)))

def boundaryRightContributions (m : MulMonomial) : List PairMonomial :=
  (if zSelected m.second then [⟨m.first, m.second, m.output, m.degree + 1, 1⟩] else []) ++
  (if zSelected m.output then [⟨m.first, m.second, m.output, m.degree + 1, 1⟩] else []) ++
  (if zSelected m.first then [⟨m.first, m.second, m.output, m.degree + 1,
    if m.second.1 then 0 else 1⟩] else [])

end ArExplicit.CocycleData

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_TwistedBoundaryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {α β : Type*} {k : Type*} [Field k] (q : k)

theorem list_sum_flatMap_p1 {M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem list_sum_map_add_p1 {M : Type*} [AddCommMonoid M]
    (l : List α) (f g : α → M) :
    (l.map f).sum + (l.map g).sum = (l.map fun a => f a + g a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [← ih, add_assoc, add_left_comm]

theorem sum_list_comm {M : Type*} [AddCommMonoid M] {ι : Type*} [Fintype ι]
    (l : List α) (f : ι → α → M) :
    (∑ i, (l.map (f i)).sum) = (l.map fun a => ∑ i, f i a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

theorem selected_eq (i : TIndex) : selected i = zSelected i := by
  obtain ⟨b, i⟩ := i
  cases b <;> cases i <;> rfl

theorem mul_inverse_weight (H : kˣ) (i : TIndex) :
    (H : k) * ((H⁻¹ : kˣ) : k) ^ i.weight = (H : k) ^ (if i.1 then 0 else 1) := by
  obtain ⟨b, i⟩ := i
  cases b <;> simp [TIndex.weight]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolutionTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {R : Type u} [Ring R]

abbrev CompleteCokernel (P : ChainComplex (ModuleCat.{u} R) ℤ) :=
  P.X 0 ⧸ LinearMap.range (P.d 1 0).hom

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TwoCone

universe u

variable {R : Type u}
  [Ring R]
variable (Q : ℕ → ModuleCat.{u} R) (δ : (n : ℕ) → Q (n+1) →ₗ[R] Q n)

abbrev FourthCokernel := Q 4 ⧸ LinearMap.range (δ 4)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeTailRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
universe u
variable {R S : Type u}
  [Ring R]
  [Ring S]
  (j : S →+* R)
variable (Q : ℕ → ModuleCat.{u} R) (δ : (n : ℕ) → Q (n+1) →ₗ[R] Q n)

abbrev restrictedSource (n : ℕ) : ModuleCat.{u} S := (ModuleCat.restrictScalars j).obj (Q n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_LinearHomologyDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.LinearHomology

universe u

variable {k : Type u} [Field k]
variable {U V W : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

def cycleMap (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) : U →ₗ[k] LinearMap.ker g :=
  f.codRestrict (LinearMap.ker g) (fun x => DFunLike.congr_fun h x)

end ArExplicit.LinearHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

section Cochains

variable {C : Type*} [Category* C] [Preadditive C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

theorem cocycleHom_component (x : Cocycle K L n) (i : ℤ) :
    (Cocycle.equivHomShift.symm x).f i = x.1.v i (i + n) rfl := by
  simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    Cocycle.rightShift_coe, Cochain.rightShift_v, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv]
  exact Category.comp_id _

end Cochains

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u v

section Cochains

variable (k : Type u) [CommRing k]
variable {C : Type*} [Category* C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ) (n : ℤ)

def fullHomCoboundaries : Submodule k (Cocycle K L n) where
  __ := coboundaries K L n
  smul_mem' a x hx := by
    obtain ⟨m, hm, y, hy⟩ := hx
    refine ⟨m, hm, a • y, ?_⟩
    rw [δ_smul, hy]
    rfl

instance fullHomModule : Module k (CohomologyClass K L n) :=
  inferInstanceAs (Module k ((Cocycle K L n) ⧸ fullHomCoboundaries k K L n))

variable {K L n}

@[simp]
theorem fullHom_mk_smul (a : k) (x : Cocycle K L n) :
    CohomologyClass.mk (a • x) = a • CohomologyClass.mk x := rfl

theorem cocycleHom_smul (a : k) (x : Cocycle K L n) :
    Cocycle.equivHomShift.symm (a • x) = a • Cocycle.equivHomShift.symm x := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [cocycleHom_component, HomologicalComplex.smul_f_apply,
    Cocycle.coe_smul, Cochain.smul_v] <;> rfl

end Cochains

open scoped ModuleCat.Algebra

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

variable (k : Type u) [CommRing k]
variable {C : Type*} [Category* C] [Preadditive C] [Linear k C]
variable (K L : CochainComplex C ℤ) (n a n' : ℤ)

variable {k K L n a n'}

variable (k K L n a n')

noncomputable def leftShiftCocycleLinearEquiv (hn : n + a = n') :
    Cocycle K L n ≃ₗ[k] Cocycle (K⟦a⟧) L n' :=
  { Cocycle.leftShiftAddEquiv n a n' hn with
    map_smul' := by
      intro c x
      apply Subtype.ext
      exact Cochain.leftShift_smul x.val a n' hn c }

variable {k K L n a n'}

theorem leftShift_boundary (hn : n + a = n') (x : Cocycle K L n)
    (hx : x ∈ coboundaries K L n) : x.leftShift a n' hn ∈ coboundaries (K⟦a⟧) L n' := by
  obtain ⟨m, hm, y, hy⟩ := hx
  have hm' : m + a = n' - 1 := by omega
  refine ⟨n' - 1, by omega, a.negOnePow • y.leftShift a (n' - 1) hm', ?_⟩
  rw [δ_units_smul, Cochain.δ_leftShift y a (n' - 1) n' hm' n hn, hy]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

theorem leftUnshift_boundary (hn : n + a = n') (x : Cocycle (K⟦a⟧) L n')
    (hx : x ∈ coboundaries (K⟦a⟧) L n') : x.leftUnshift n hn ∈ coboundaries K L n := by
  obtain ⟨m', hm', y, hy⟩ := hx
  have hm : n - 1 + a = m' := by omega
  refine ⟨n - 1, by omega, a.negOnePow • y.leftUnshift (n - 1) hm, ?_⟩
  rw [δ_units_smul, Cochain.δ_leftUnshift y (n - 1) hm n n' hn, hy]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

variable (k K L n a n')

noncomputable def leftShiftCohomologyEquiv (hn : n + a = n') :
    CohomologyClass K L n ≃ₗ[k] CohomologyClass (K⟦a⟧) L n' :=
  Submodule.Quotient.equiv (fullHomCoboundaries k K L n)
    (fullHomCoboundaries k (K⟦a⟧) L n') (leftShiftCocycleLinearEquiv k K L n a n' hn) (by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact leftShift_boundary hn x hx
      · intro hy
        let E := leftShiftCocycleLinearEquiv k K L n a n' hn
        refine ⟨E.symm y, leftUnshift_boundary hn y hy, E.apply_symm_apply y⟩)

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ProjectiveNullhomotopyAbove
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ProjectiveNullhomotopyAbove

universe u
variable {R : Type u} [Ring R]
variable {P Q : ℕ → Type u}
variable [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]
variable [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)]
variable (dP : (n : ℕ) → P (n + 1) →ₗ[R] P n)
variable (dQ : (n : ℕ) → Q (n + 1) →ₗ[R] Q n)
variable (f : (n : ℕ) → Q (n + 2) →ₗ[R] P n)

structure Pair (n : ℕ) where
  lo : Q (n + 1) →ₗ[R] P n
  hi : Q (n + 2) →ₗ[R] P (n + 1)
  eqn : f n = (dP n).comp hi + lo.comp (dQ (n + 1))

end ArExplicit.ProjectiveNullhomotopyAbove

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorBottomDifferential
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P U : ChainComplex (ModuleCat.{u} A) ℕ) (Q V : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "E" => A ⊗[k] B

theorem hom_zero_apply_p0 {M N : ModuleCat.{u} E} (x : M) : (0 : M ⟶ N) x = 0 := rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorForget
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

abbrev forgetField : ModuleCat.{u} A ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A)

abbrev forgetComplex (P : ChainComplex (ModuleCat.{u} A) ℕ) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ((forgetField k A).mapHomologicalComplex _).obj P

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

instance hasScalarTotal : HomologicalComplex.HasMapBifunctor (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) := fun _ => inferInstance

abbrev scalarTotal : ChainComplex (ModuleCat.{u} k) ℕ :=
  HomologicalComplex.mapBifunctor (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ)

end ArExplicit.ExternalTensor

end

end OAI
end


