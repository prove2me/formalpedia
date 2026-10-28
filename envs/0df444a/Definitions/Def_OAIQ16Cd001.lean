-- Prove2me | Definitions.Def_OAIQ16Cd001
-- name    : OAIQ16Cd001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T14:39:23.143307+00:00
-- url     : https://prove2.me/theorems/6ec1f932-fb60-48a6-b898-03c2c13fbeb0
-- title:
--   Definitions bundle OAIQ16Cd001 of the split of OpenAI, The optimal order of convex-body covering density
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 65 definitions, 2 inductive types or structures, 5 instances and 10 theorems. The definitions and types are `OAI.SingleLatticeCovering.Shear.Pattern.instDecidableEqProdForallFinReal_1`, `OAI.SingleLatticeCovering.Shear.Pattern.slice`, `OAI.SingleLatticeCovering.Shear.SourcePattern`, `OAI.SingleLatticeCovering.Shear.SuffixBinary`, `OAI.SingleLatticeCovering.Shear.UniqueLabels`, `OAI.SingleLatticeCovering.Shear.allPatterns`, `OAI.SingleLatticeCovering.Shear.alphabetPoints`, `OAI.SingleLatticeCovering.Shear.instDecidableEqProdForallFinReal_solutions`, `OAI.SingleLatticeCovering.Shear.patternTotal`, `OAI.SingleLatticeCovering.Shear.pointBudget`, `OAI.SingleLatticeCovering.Shear.restrictColumns`, `OAI.SingleLatticeCovering.SimplexYoung.circuitTerm`, `OAI.SingleLatticeCovering.SimplexYoung.scaledCircuitFamily`, `OAI.SingleLatticeCovering.SimplexYoung.simplexConstant`, `OAI.SingleLatticeCovering.SimplexYoung.simplexRoot`, `OAI.SingleLatticeCovering.SimplexYoung.sourceEta`, `OAI.SingleLatticeCovering.Vertical.Block`, `OAI.SingleLatticeCovering.Vertical.Block.Group`, `OAI.SingleLatticeCovering.Vertical.Block.Vec`, `OAI.SingleLatticeCovering.Vertical.Block.det`, `OAI.SingleLatticeCovering.Vertical.Block.linear`, `OAI.SingleLatticeCovering.Vertical.Block.roundingLoss`, `OAI.SingleLatticeCovering.Vertical.Block.shift`, `OAI.SingleLatticeCovering.Vertical.Block.shiftDim`, `OAI.SingleLatticeCovering.Vertical.Block.shiftDimMap`, `OAI.SingleLatticeCovering.Vertical.Block.shiftMap`, `OAI.SingleLatticeCovering.Vertical.Block.terminalDim`, `OAI.SingleLatticeCovering.Vertical.Block.terminalShift`, `OAI.SingleLatticeCovering.Vertical.Chain`, `OAI.SingleLatticeCovering.Vertical.Chain.CeilingSizes`, `OAI.SingleLatticeCovering.Vertical.Chain.Every`, `OAI.SingleLatticeCovering.Vertical.Chain.FullVec`, `OAI.SingleLatticeCovering.Vertical.Chain.Halving`, `OAI.SingleLatticeCovering.Vertical.Chain.Vec`, `OAI.SingleLatticeCovering.Vertical.Chain.alphabetRadius`, `OAI.SingleLatticeCovering.Vertical.Chain.alphabetSeq`, `OAI.SingleLatticeCovering.Vertical.Chain.alphabets`, `OAI.SingleLatticeCovering.Vertical.Chain.blockSum`, `OAI.SingleLatticeCovering.Vertical.Chain.coefficient`, `OAI.SingleLatticeCovering.Vertical.Chain.denominators` and 27 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `CoveringDensity_Model`, `LatticeCovering_Bits`, `LatticeCovering_Chains`, `LatticeCovering_Completion`, `LatticeCovering_Covering`, `LatticeCovering_GridCounts`, `LatticeCovering_Lines`, `LatticeCovering_Patterns`, `LatticeCovering_PrimeGrids`, `LatticeCovering_Products`, `LatticeCovering_Rates`, `LatticeCovering_Residuals`, `LatticeCovering_Shears`, `LatticeCovering_Transport`, `TranslativeCovering_Periodization`, `TranslativeCovering_SourceLocalization`, `TranslativeCovering_SourceParameters`, `TranslativeCovering_TargetSampling`, `TranslativeCovering_WeightedVolume`.
--
--   **Imports.** It imports the published bundle `Def_CoveringDensity`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ16Cd002`; the statements `OAI.PatternTail.bound`, `OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all` and `OAI.TranslativeCovering.main`; the proofs of `OAI.AllLatticeExclusion.no_cover` and `OAI.SourcePatternTail.uniform`.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_CoveringDensity

section
-- module Solutions.OAIQ16_CD.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.CoveringDensity_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TranslativeCovering

open Set

def MainStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∃ K : Set (Space n), ConvexBody K ∧ CentrallySymmetric K ∧
      ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) < thetaT K

end TranslativeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical





noncomputable section

open scoped BigOperators
open Classical
namespace SingleLatticeCovering.WeightedSelection
universe u v
variable {Z : Type u} {W : Type v} [Fintype Z] [Fintype W] [Nonempty W]


def mass (F : Z → ℝ) (E : Finset Z) : ℝ := 𝔼 z, if z ∈ E then F z else 0

def loss (F : Z → ℝ) (E : Finset Z) (q : W → Z → ℝ) (w : W) : ℝ :=
  𝔼 z, if z ∈ E then F z*q w z else 0

end SingleLatticeCovering.WeightedSelection

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
-- module Solutions.OAIQ16_CD.LatticeCovering_Lines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical





noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical

variable {E V W : Type*} [Fintype E]

def join (P : E → Finset V) (point : E → W) : Finset (V × W) := by
  classical
  exact Finset.univ.biUnion (fun e => (P e).image (fun x => (x,point e)))



def SuffixBinary {m : ℕ} (P : Finset (Fin m → ℝ)) : Prop :=
  ∀ j : Fin m, ∀ y : Fin m → ℝ, ∃ a : ℝ, ∀ x ∈ P,
    (∀ k, j<k → x k=y k) → x j=a ∨ x j=a+1

def bits (b : ℕ) (lam : Fin b → ℝ) (e : Fin b → Bool) : Fin b → ℝ :=
  fun j => lam j + if e j then 1 else 0


end SingleLatticeCovering.Vertical


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
-- module Solutions.OAIQ16_CD.LatticeCovering_Chains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical
open scoped BigOperators


def concat {m b : ℕ} (P : (Fin b → Bool) → Finset (Fin m → ℝ))
    (lam : Fin b → ℝ) : Finset (Fin (m+b) → ℝ) := by
  classical
  exact (join P (bits b lam)).image (fun x => Fin.append x.1 x.2)


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open scoped BigOperators


structure Block where
  b : ℕ
  p : ℕ
  prime : p.Prime
  h : ℝ
  h_pos : 0 < h
  usable : Finset (Fin b → ZMod p)
  direction : Fin b → ZMod p
  direction_ne : direction ≠ 0

namespace Block
abbrev Group (B : Block) := Fin B.b → ZMod B.p
abbrev Vec (B : Block) := Fin B.b → ℝ
instance instFactPrimeP (B : Block) : Fact B.p.Prime := ⟨B.prime⟩

def det (B : Block) : ℝ := B.h^B.b/(B.p : ℝ)


def shift (A B : Block) (w : Fin B.b → A.Group) (l : B.Vec) : A.Vec :=
  fun j => A.h/(A.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k



end Block
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open scoped BigOperators



inductive Chain : Block → Type
  | base (B : Block) : Chain B
  | append {A : Block} (c : Chain A) (B : Block)
      (w : Fin B.b → A.Group) : Chain B

namespace Chain
variable {A B : Block}

abbrev dim : {B : Block} → Chain B → ℕ
  | _, .base B => B.b
  | _, .append c B _ => c.dim+B.b

abbrev Vec (c : Chain B) := Fin c.dim → ℝ

def last : {B : Block} → (c : Chain B) → c.Vec → B.Vec
  | _, .base _, y => y
  | _, .append c _ _, y => fun j => y (Fin.natAdd c.dim j)

def subLast : {B : Block} → (c : Chain B) → c.Vec → B.Vec → c.Vec
  | _, .base _, y, t => y-t
  | _, .append c _ _, y, t =>
      Fin.append (fun j => y (Fin.castAdd _ j)) (fun j => y (Fin.natAdd c.dim j)-t j)

@[simp] lemma last_subLast (c : Chain B) (y : c.Vec) (t : B.Vec) :
    c.last (c.subLast y t) = c.last y-t := by
  cases c <;> simp [last, subLast, Pi.sub_def]



def coefficient (loss : Block → ℝ) : {B : Block} → Chain B → ℝ
  | _, .base B => Real.exp (-((B.b : ℝ)*B.h^2/B.p))
  | _, .append (A := A) c B _ =>
      c.coefficient loss * Real.exp (-((B.b : ℝ)*B.h^2/B.p)) * (1-loss B)*(1-loss A)


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Filter Topology
open scoped BigOperators

def blockLoss (A : ℝ) (B : Block) : ℝ := A*(B.b : ℝ)^(-(1/100 : ℝ))


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open scoped BigOperators
namespace Block

def roundingLoss (B : Block) : ℝ := (B.b : ℝ)*B.h^2/(B.p : ℝ)
end Block

namespace Chain
variable {A B : Block}

def first : {B : Block} → Chain B → Block
  | _, .base B => B
  | _, .append c _ _ => c.first

def Every (P : Block → Prop) : {B : Block} → Chain B → Prop
  | _, .base B => P B
  | _, .append c B _ => c.Every P ∧ P B

def blockSum (f : Block → ℝ) : {B : Block} → Chain B → ℝ
  | _, .base B => f B
  | _, .append c B _ => c.blockSum f+f B

def Halving : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B _ => c.Halving ∧ 2*B.b ≤ A.b



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Filter Topology
open scoped BigOperators


def nextSize (b : ℕ) : ℕ := ⌈(b : ℝ)^(9/10 : ℝ)⌉₊

namespace Chain
variable {B : Block}
def CeilingSizes : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B _ => c.CeilingSizes ∧ B.b=nextSize A.b
end Chain



end SingleLatticeCovering.Vertical

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
-- module Solutions.OAIQ16_CD.LatticeCovering_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open scoped BigOperators

namespace Block

def linear (B : Block) : B.Vec ≃ₗ[ℝ] B.Vec :=
  LinearEquiv.smulOfNeZero ℝ B.Vec B.h B.h_pos.ne'
@[simp] lemma linear_apply (B : Block) (l : B.Vec) : B.linear l = B.h • l := rfl

def shiftMap (A B : Block) (w : Fin B.b → A.Group) : B.Vec →ₗ[ℝ] A.Vec :=
  Matrix.mulVecLin (fun j k => A.h/(A.p : ℝ)*((w k j).val : ℝ))
@[simp] lemma shiftMap_apply (A B : Block) (w : Fin B.b → A.Group) (l : B.Vec) :
    A.shiftMap B w l = A.shift B w l := by
  ext j
  change (∑ k, (A.h/(A.p : ℝ)*((w k j).val : ℝ))*l k) =
    A.h/(A.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring
end Block

end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open scoped BigOperators


def terminalColumns (b p : ℕ) : Fin (b*Nat.clog 2 p) → Fin b → ZMod p :=
  fun i => Pi.single (finProdFinEquiv.symm i).1
    ((2 : ZMod p)^((finProdFinEquiv.symm i).2 : ℕ))


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Module Submodule MeasureTheory
open scoped BigOperators

abbrev integerLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

namespace Block
abbrev terminalDim (B : Block) : ℕ := B.b*Nat.clog 2 B.p

def shiftDim (B : Block) (d : ℕ) (w : Fin d → B.Group) (l : Fin d → ℝ) : B.Vec :=
  fun j => B.h/(B.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k

def shiftDimMap (B : Block) (d : ℕ) (w : Fin d → B.Group) : (Fin d → ℝ) →ₗ[ℝ] B.Vec :=
  Matrix.mulVecLin (fun j k => B.h/(B.p : ℝ)*((w k j).val : ℝ))
@[simp] lemma shiftDimMap_apply (B : Block) (d : ℕ) (w : Fin d → B.Group) (l : Fin d → ℝ) :
    B.shiftDimMap d w l = B.shiftDim d w l := by
  ext j
  change (∑ k, (B.h/(B.p : ℝ)*((w k j).val : ℝ))*l k) =
    B.h/(B.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

abbrev terminalShift (B : Block) : (Fin B.terminalDim → ℝ) →ₗ[ℝ] B.Vec :=
  B.shiftDimMap B.terminalDim (terminalColumns B.b B.p)



end Block

namespace Chain
variable {B : Block}
abbrev fullDim (c : Chain B) : ℕ := c.dim+B.terminalDim
abbrev FullVec (c : Chain B) := Fin c.fullDim → ℝ



end Chain
end SingleLatticeCovering.Vertical


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
-- module Solutions.OAIQ16_CD.LatticeCovering_Residuals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Module Submodule MeasureTheory
open scoped BigOperators

namespace Chain
variable {A B : Block}

def heights : {B : Block} → (c : Chain B) → c.Vec
  | _, .base B => fun _ => B.h
  | _, .append c B _ => Fin.append c.heights (fun _ => B.h)

def radiusSq (c : Chain B) : ℝ := c.blockSum (fun Q => (Q.b : ℝ)*Q.h^2)



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open scoped BigOperators

namespace Chain
variable {B : Block}

def alphabetRadius (c : Chain B) : ℕ := 1+(c.fullDim+2)^c.fullDim


def denominators : {B : Block} → (c : Chain B) → Fin c.dim → ℕ
  | _, .base B => fun _ => B.p
  | _, .append c B _ => Fin.append c.denominators (fun _ => B.p)

def fullDenominators (c : Chain B) : Fin c.fullDim → ℕ :=
  Fin.append c.denominators (fun _ => 1)

end Chain


noncomputable def rationalAlphabet (Q p : ℕ) : Finset ℝ :=
  (Finset.Icc (-(Q*p : ℤ)) (Q*p : ℤ)).image (fun k : ℤ => (k : ℝ)/(p : ℝ))

noncomputable def Chain.alphabets {B : Block} (c : Chain B) : Fin c.fullDim → Finset ℝ :=
  fun j => rationalAlphabet c.alphabetRadius (c.fullDenominators j)


end SingleLatticeCovering.Vertical


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
-- module Solutions.OAIQ16_CD.LatticeCovering_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section





noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace SingleLatticeCovering.Shear

universe u



def restrictColumns {E : Type*} {q d : ℕ} (h : q ≤ d) (Z : Fin d → E) : Fin q → E :=
  fun i => Z (Fin.castLE h i)

@[simp] lemma restrictColumns_self {E : Type*} {d : ℕ} (Z : Fin d → E) :
    restrictColumns (le_refl d) Z = Z := rfl

end SingleLatticeCovering.Shear


end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Shears
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace SingleLatticeCovering.Shear.Pattern
variable {α : Type*}
local instance instDecidableEqProdForallFinReal_1 {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _


def slice {q : ℕ} (s : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ) :
    Finset ((Fin q → ℝ) × α) := by
  classical
  exact (s.filter (fun l => l.1 (Fin.last q) = v)).image (fun l => (Fin.init l.1,l.2))

end SingleLatticeCovering.Shear.Pattern

namespace SingleLatticeCovering.Shear
variable {α : Type*}
local instance instDecidableEqProdForallFinReal_solutions {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _



def UniqueLabels {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  ∀ l ∈ s, ∀ r ∈ s, l.1=r.1 → l.2=r.2




def SuffixBinary {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  ∀ j : Fin q, ∀ y : Fin q → ℝ, ∃ v : ℝ, ∀ l ∈ s,
    (∀ k : Fin q, j<k → l.1 k = y k) → l.1 j = v ∨ l.1 j = v+1

def SourcePattern {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  s.Nonempty ∧ UniqueLabels s ∧ SuffixBinary s

end SingleLatticeCovering.Shear



namespace SingleLatticeCovering.Shear
open scoped BigOperators

noncomputable def alphabetPoints {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    Finset ((Fin q → ℝ) × α) :=
  (Fintype.piFinset (fun j : Fin q => A j.val)).product labels

noncomputable def allPatterns {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    Finset (Finset ((Fin q → ℝ) × α)) := by
  classical
  exact (alphabetPoints A labels q).powerset.filter SourcePattern


end SingleLatticeCovering.Shear

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace SingleLatticeCovering.Vertical
open scoped BigOperators

noncomputable def labelPattern {α : Type*} {D : ℕ}
    (P : Finset (Fin D → ℝ)) (a : (Fin D → ℝ) → α) :
    Finset ((Fin D → ℝ) × α) := by
  classical
  exact P.image (fun l => (l,a l))


end SingleLatticeCovering.Vertical

end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Covering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.Vertical

namespace Chain
variable {B : Block}

noncomputable def alphabetSeq (c : Chain B) (j : ℕ) : Finset ℝ :=
  if h : j < c.fullDim then c.alphabets ⟨j,h⟩ else ∅

@[simp] lemma alphabetSeq_fin (c : Chain B) (j : Fin c.fullDim) :
    c.alphabetSeq j.val=c.alphabets j := by
  simp [alphabetSeq,j.isLt]
end Chain
end SingleLatticeCovering.Vertical

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Rates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace SingleLatticeCovering.Shear
open Real Filter Topology
open scoped BigOperators



def pointBudget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) : ℕ :=
  (s.card+1)*∏ j ∈ Finset.range D, ((A j).card+1)

def patternTotal {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (D+1), (allPatterns A s q).card


end SingleLatticeCovering.Shear

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GridCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section


noncomputable section







noncomputable section
namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix Filter Topology
open scoped ENNReal BigOperators


def simplexRoot {r : ℕ} : Matrix (Fin r) (Fin r) ℝ :=
  1 + Matrix.replicateCol Unit (fun _ : Fin r => (1:ℝ)) *
    Matrix.replicateRow Unit (fun _ : Fin r => (1:ℝ)/(Real.sqrt (r+1:ℕ)+1))



end SingleLatticeCovering.SimplexYoung





open MeasureTheory Filter Set
open scoped Topology
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal


def simplexConstant (r : ℕ) : ℝ :=
  (Real.sqrt ((r:ℝ)/(r+1:ℕ)))⁻¹^r / Real.sqrt (r+1:ℕ)

lemma integral_pos_of_continuous_density {f : ℝ → ℝ}
    (hp : ∀ x, 0 < f x) (hi : Integrable f volume) : 0 < ∫ x, f x := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hi).mpr
  have he : Function.support f = univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (hp x)]
  rw [he]
  simp



end SingleLatticeCovering.SimplexYoung


open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix
open scoped ENNReal Pointwise


def scaledCircuitFamily {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    Fin (r+1) → Set (Fin d → ℝ) := Fin.cons ((-1:ℝ) • J) (fun j => c j • J)


end SingleLatticeCovering.SimplexYoung



end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_PrimeGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open scoped BigOperators



def circuitTerm (d : ℕ) (V : ℝ) (r : ℕ) : ℝ :=
  (4:ℝ)^r * (simplexConstant r)^d * V^r / (r.factorial:ℝ)




end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung


def sourceEta (d : ℕ) : ℝ := (d:ℝ)/4 * Real.log (27/16:ℝ) - 3*Real.log (d:ℝ)


end SingleLatticeCovering.SimplexYoung




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
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_WeightedVolume
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace WeightedVolume
open Set MeasureTheory Metric
open scoped ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
end WeightedVolume

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace SourceParameters
open Filter
open scoped Topology
noncomputable def M (n : ℕ) : ℕ := ⌈Real.exp ((n:ℝ)*Real.log n/16)⌉₊
end SourceParameters

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_TargetSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace TargetSampling
open Set MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
variable {Ω : Type u_1} [MeasurableSpace Ω]

noncomputable def pairs (M : ℕ) : Finset (Fin M × Fin M) :=
  univ.filter (fun p => p.1 ≠ p.2)

noncomputable def score {M : ℕ} (A : Set (Ω × Ω)) (x : Fin M → Ω) : ℝ :=
  ∑ p ∈ pairs M,A.indicator (fun _ => 1) (x p.1,x p.2)

end TargetSampling

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace SourceLocalization
open Set Metric MeasureTheory SourceParameters
open scoped ENNReal Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
end SourceLocalization

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_Periodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering

open scoped Classical Topology

noncomputable def integerGrid (n N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ))

end TranslativeCovering

end OAI
end


