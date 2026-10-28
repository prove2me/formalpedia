-- Prove2me | Definitions.Def_OAIQ057D007
-- name    : OAIQ057D007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T20:45:24.733273+00:00
-- url     : https://prove2.me/theorems/2e67a0a2-d108-49f0-9cea-ade3fd81815c
-- title:
--   Definitions bundle OAIQ057D007 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.exists_channel_fin21`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 9 definitions, 1 inductive type or structure, 7 instances and 18 theorems. The definitions and types are `OAI.DimensionTen.chart`, `OAI.DimensionTen.complementaryIndex`, `OAI.DimensionTen.complementarySign`, `OAI.DimensionTen.omega`, `OAI.DimensionTen.productVector`, `OAI.DimensionTen.projector`, `OAI.DimensionTen.pure`, `OAI.DimensionTen.rootInteger`, `OAI.TensorCriterion.altPair`, `OAI.ZeroKey.ClassicalRecordSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, lean/OAI/InformationTheory, in whole or in part: `Quantum_DimensionTen_CompoundTrace`, `Quantum_DimensionTen_Kraus`, `Quantum_DimensionTen_PencilModel`, `Quantum_DimensionTen_PureMatrices`, `Quantum_DimensionTen_RootReduction`, `Quantum_DimensionTen_TensorKraus`, `Quantum_DimensionTen_TensorSymmetry`, `Quantum_PPTSquare_GaloisAction`, `Quantum_PPTSquare_Mod131Data`, `Quantum_PPTSquare_Mod139Data`, `Quantum_PPTSquare_Mod41Data`, `Quantum_PPTSquare_TensorModel`, `SecretKey_Model`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ057D009`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis, lean/OAI/InformationTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ057_CH.Compat
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
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_GaloisAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial

open scoped BigOperators
open Equiv Equiv.Perm Function
namespace GaloisAction
open NumberField
open scoped NumberField
attribute [local instance] Classical.propDecidable
local instance prime41 : Fact (Nat.Prime 41) := ⟨by decide⟩
local instance prime139 : Fact (Nat.Prime 139) := ⟨by decide⟩
end GaloisAction

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_Mod131Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace ModularPencil
namespace P131
local instance primeFact : Fact (Nat.Prime 131) := ⟨by decide +kernel⟩
end P131
end ModularPencil

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_Mod139Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace ModularPencil
namespace P139
local instance primeFact : Fact (Nat.Prime 139) := ⟨by decide +kernel⟩
end P139
end ModularPencil

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_Mod41Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace ModularPencil
namespace P41
local instance primeFact : Fact (Nat.Prime 41) := ⟨by decide +kernel⟩
end P41
end ModularPencil

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_TensorModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open scoped MatrixOrder
namespace TensorCriterion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

def altPair : Fin 6 → Fin 4 × Fin 4 := ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

end TensorCriterion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PencilModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen

def projector (x : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.vecMulVec x (star x)


def chart (t : Fin 3 → ℂ) : Fin 4 → ℂ := Fin.cons 1 t


def productVector {a b : ℕ} (u : Fin a → ℂ) (v : Fin b → ℂ) : Fin a × Fin b → ℂ :=
  fun ij => u ij.1 * v ij.2


end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma kronecker_transpose {a b c d : Type*} (A : Matrix a b ℂ) (B : Matrix c d ℂ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := rfl

lemma real_compression_transpose {a b : Type*} [Fintype a]
    (V : Matrix a b ℂ) (hV : Vᴴ = Vᵀ) (A : Matrix a a ℂ) :
    (Vᴴ * A * V)ᵀ = Vᴴ * Aᵀ * V := by
  simp only [Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma real_embedding_transpose {a b : Type*} [Fintype a]
    (V : Matrix b a ℂ) (hV : Vᴴ = Vᵀ) (A : Matrix a a ℂ) :
    (V * A * Vᴴ)ᵀ = V * Aᵀ * Vᴴ := by
  simp only [Matrix.transpose_mul, hV, Matrix.transpose_transpose, Matrix.mul_assoc]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_PureMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def pure {n : Type*} (x : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec x (star x)

def omega (a : ℕ) : Fin a × Fin a → ℂ := fun ij => if ij.1 = ij.2 then 1 else 0

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_CompoundTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def complementaryIndex : Fin 6 → Fin 6 := ![5,4,3,2,1,0]
def complementarySign : Fin 6 → ℂ := ![1,-1,1,1,-1,1]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Kraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open Matrix
namespace DimensionTen

lemma posSemidef_sum {r n : Type*} [Fintype r] (A : r → Matrix n n ℂ)
    (h : ∀ i, (A i).PosSemidef) : (∑ i, A i).PosSemidef := by
  classical
  have hh : ∀ s : Finset r, (∑ i ∈ s, A i).PosSemidef := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
    | @insert i s hi ih => simpa [Finset.sum_insert hi] using (h i).add ih
  exact hh Finset.univ

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_RootReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen


def rootInteger {K : Type*} [Field K] [CharZero K] (f : ℤ[X]) (hm : f.Monic)
    (x : f.rootSet K) : 𝓞 K :=
  ⟨x, ⟨f, hm, (mem_rootSet.mp x.property).2⟩⟩

@[simp] lemma rootInteger_coe {K : Type*} [Field K] [CharZero K] (f : ℤ[X]) (hm : f.Monic)
    (x : f.rootSet K) : (rootInteger f hm x : K) = x := rfl

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorKraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma sum_kronecker {r a b c d : Type*} [Fintype r]
    (A : r → Matrix a b ℂ) (B : Matrix c d ℂ) :
    (∑ r, A r) ⊗ₖ B = ∑ r, A r ⊗ₖ B := by
  ext i j
  simp [Matrix.sum_apply, Finset.sum_mul]

lemma kronecker_sum {r a b c d : Type*} [Fintype r]
    (A : Matrix a b ℂ) (B : r → Matrix c d ℂ) :
    A ⊗ₖ (∑ r, B r) = ∑ r, A ⊗ₖ B r := by
  ext i j
  simp [Matrix.sum_apply, Finset.mul_sum]

lemma block_expansion {a c : ℕ} (X : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    X = ∑ i : Fin c, ∑ j : Fin c,
      (Matrix.of (fun a b => X (a, i) (b, j))) ⊗ₖ (Matrix.single i j 1) := by
  ext ⟨u, i⟩ ⟨v, j⟩
  simp [Matrix.sum_apply, Matrix.single_apply, ite_and]

lemma sum_four_comm {a b c d M : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [AddCommMonoid M] (f : a → b → c → d → M) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]; arg 2; ext k; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.SecretKey_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ZeroKey

section

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder

universe v4350_0 v4350_1

open scoped Matrix.Norms.L2Operator in
instance matrixMeasurableSpace {m : Type v4350_0} {n : Type v4350_1} [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℂ) := borel _

universe v4353_0 v4353_1

open scoped Matrix.Norms.L2Operator in
instance matrixBorelSpace {m : Type v4353_0} {n : Type v4353_1} [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := ⟨rfl⟩

universe v4357_0 v4357_1

universe v4361_0 v4361_1

end

open MeasureTheory ProbabilityTheory Matrix Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

universe v5486_0 v5486_1

end ZeroKey

namespace ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory Filter

section

universe u

structure ClassicalRecordSpace where
  Carrier : Type u
  measurableSpace : MeasurableSpace Carrier
  standardBorel : StandardBorelSpace Carrier
  nonempty : Nonempty Carrier

attribute [instance] ClassicalRecordSpace.measurableSpace ClassicalRecordSpace.standardBorel ClassicalRecordSpace.nonempty

instance instCoeSortClassicalRecordSpaceType : CoeSort ClassicalRecordSpace (Type u) := ⟨ClassicalRecordSpace.Carrier⟩

end

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u

end

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

universe u

end ZeroKey

end

end OAI
end


