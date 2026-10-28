-- Prove2me | Definitions.Def_OAIQ039C015
-- name    : OAIQ039C015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:13:25.64791+00:00
-- url     : https://prove2.me/theorems/5207b37c-a96b-428e-8185-de04689995ab
-- title:
--   Definitions bundle OAIQ039C015 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 25 definitions, 2 inductive types or structures, 5 instances and 17 theorems. The definitions and types are `OAI.Kadison.OperatorAmplification.matrixCornerInclusionDecidableEq`, `OAI.Kadison.OperatorAmplification.matrixStandardFormDecidableEq`, `OAI.Kadison.OperatorFunctionals.extendOperator`, `OAI.Kadison.OperatorFunctionals.instNormedAddCommGroupContinuousLinearMapComplexIdSubtypeMemSubmodule_solutions`, `OAI.Kadison.OperatorFunctionals.instNormedSpaceComplexContinuousLinearMapIdSubtypeMemSubmodule_solutions`, `OAI.Kadison.OperatorFunctionals.singularBasis`, `OAI.Kadison.Pairing`, `OAI.Kadison.Pairing.Representatives`, `OAI.Kadison.Pairing.contraction`, `OAI.Kadison.Pairing.finiteLabels`, `OAI.Kadison.Pairing.pairEquiv`, `OAI.Kadison.Pairing.pairFunctionEquiv`, `OAI.Kadison.Pairing.repr`, `OAI.Kadison.PartialIsometryOrder.DyadicPartition.Index`, `OAI.Kadison.PartialIsometryOrder.EqualPartition`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.instDecidableEq_1`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.instDecidableEq_2`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.orthogonalRankDecidableEq`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.part`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.piece`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.singleton`, `OAI.Kadison.PartialIsometryOrder.IsFiniteAlgebra`, `OAI.Kadison.PartialIsometryOrder.ProjectionIn`, `OAI.Kadison.RationalStarExtension.instNormedAlgebraRat_solutions`, `OAI.Kadison.WeakDualHull.hull`, `OAI.Kadison.WeakDualHull.instAddCommGroupWeakDualComplex_solutions`, `OAI.Kadison.WeakDualHull.instModuleRealWeakDualComplex_solutions`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_DyadicCuts`, `Commutator_DyadicPartition`, `Commutator_EqualPartitionSums`, `Commutator_EqualProjectionPartition`, `Commutator_FiniteCancellation`, `Commutator_FiniteFunctionalFactorization`, `Commutator_FinitePairings2`, `Commutator_FiniteSupportFactorization`, `Commutator_MatrixCornerInclusion`, `Commutator_MatrixStandardForm`, `Commutator_OrthogonalRank`, `Commutator_PairTrace`, `Commutator_PairTrace2`, `Commutator_Pairings`, `Commutator_PartitionRankComparison`, `Commutator_RationalStarExtension`, `Commutator_WeakDualHull`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C029`; the statements `OAI.Kadison.PartialIsometryOrder.nonfinite_two_isometries`, `OAI.Kadison.TraceDimension.faithful`, `OAI.Kadison.finite_pairing_source_bound`, `OAI.Kadison.finite_pairing_test_bound` and `OAI.Kadison.uniform_commutator_nonfinite_factor`; the proofs of `OAI.Kadison.finite_pairing_source_bound`, `OAI.Kadison.finite_pairing_test_bound` and `OAI.Kadison.uniform_commutator_nonfinite_factor`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsFiniteAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ v∈M,star v*v=1 → v*star v=1

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure ProjectionIn (M : VonNeumannAlgebra H) where
  val : H →L[ℂ] H
  mem : val∈M
  projection : IsStarProjection val

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EqualProjectionPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure EqualPartition (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι] where
  base : H →L[ℂ] H
  base_mem : base∈M
  base_projection : IsStarProjection base
  v : ι → H →L[ℂ] H
  mem : ∀ i,v i∈M
  initial : ∀ i,star (v i)*v i=base
  source : ∀ i,v i*base=v i
  cross : ∀ i j,i≠j → star (v i)*v j=0
  total : ∑ i,v i*star (v i)=1

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance instDecidableEq_r85358a_1 : DecidableEq ι := Classical.decEq ι
def singleton (M : VonNeumannAlgebra H) : EqualPartition M Unit where
  base := 1
  base_mem := M.one_mem
  base_projection := IsStarProjection.one _
  v := fun _ => 1
  mem := fun _ => M.one_mem
  initial := by simp
  source := by simp
  cross := by intros; contradiction
  total := by simp

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DyadicPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance instDecidableEq_1 : DecidableEq ι := Classical.decEq ι

end EqualPartition

namespace DyadicPartition

variable (M : VonNeumannAlgebra H)

def Index : ℕ → Type
  | 0 => Unit
  | n+1 => Index n × Bool

instance indexFintype : (n : ℕ) → Fintype (Index n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd (Index n) Bool (indexFintype n) inferInstance

instance indexNonempty : (n : ℕ) → Nonempty (Index n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => @instNonemptyProd (Index n) Bool (indexNonempty n) inferInstance

end DyadicPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EqualPartitionSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance equalPartitionSumsDecidableEq_r85358a_1 : DecidableEq ι := Classical.decEq ι
def piece (i : ι) : H →L[ℂ] H := D.v i*star (D.v i)

def part (s : Finset ι) : H →L[ℂ] H := ∑ i∈s,D.piece i

lemma piece_mem (i : ι) : D.piece i∈M := M.mul_mem (D.mem i) (M.star_mem' (D.mem i))

lemma part_mem (s : Finset ι) : D.part s∈M := M.sum_mem (fun i _ => D.piece_mem i)

@[simp] lemma part_empty : D.part ∅=0 := by simp [part]

@[simp] lemma part_univ : D.part Finset.univ=1 := D.total

@[simp] lemma part_singleton (i : ι) : D.part {i}=D.piece i := by simp [part]

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFunctionalFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open InnerProductSpace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} [Fintype ι]

variable [FiniteDimensional ℂ H]

def singularBasis (R : H →L[ℂ] H) :
    OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H :=
  (R.toLinearMap.isSymmetric_adjoint_comp_self).eigenvectorBasis rfl

end Kadison.OperatorFunctionals

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_Pairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison

abbrev Pairing (J : Type*) := {σ : Equiv.Perm J // Function.Involutive σ ∧ ∀ j, σ j ≠ j}

namespace Pairing

variable {J : Type*}

instance instCoeFunForall : CoeFun (Pairing J) (fun _ => J → J) := ⟨fun σ => σ.val⟩

@[simp] theorem apply_apply (σ : Pairing J) (j : J) : σ (σ j) = j := σ.property.1 j

theorem apply_ne (σ : Pairing J) (j : J) : σ j ≠ j := σ.property.2 j

theorem injective (σ : Pairing J) : Function.Injective σ := σ.val.injective

@[ext] theorem ext (σ τ : Pairing J) (h : ∀ j, σ j = τ j) : σ = τ := by
  apply Subtype.ext
  exact Equiv.ext h

instance instFintype [Fintype J] : Fintype (Pairing J) := Fintype.ofFinite _

instance instDecidableEq : DecidableEq (Pairing J) := Classical.decEq _

variable [LinearOrder J]

def repr (σ : Pairing J) (j : J) : J := min j (σ j)

@[simp] theorem repr_apply (σ : Pairing J) (j : J) : repr σ (σ j) = repr σ j := by
  simp only [repr, apply_apply, min_comm]

variable [Fintype J]

def contraction {E : Type*} (σ : Pairing J) (B : E → E → ℂ) (v : J → E) : ℂ :=
  ∏ j ∈ Finset.univ.filter (fun j => j < σ j), B (v j) (v (σ j))

end Pairing

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FinitePairings2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Pairing

variable {J : Type*} [LinearOrder J]

def finiteLabels (σ : Pairing J) (p : J) {N : ℕ} (n : Fin (N+1)) (j : J) :
    J × Fin (N+1) :=
  (repr σ j, if repr σ j = repr σ p then n else 0)

end Kadison.Pairing
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteSupportFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorFunctionals

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (K : Submodule ℂ H) [K.HasOrthogonalProjection]

def extendOperator : (K →L[ℂ] K) →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun := fun (R : K →L[ℂ] K) => K.subtypeL.comp (R.comp K.orthogonalProjectionOnto)
      map_add' := by intro R S; ext x; rfl
      map_smul' := by intro z R; ext x; rfl }
    1 (by
      intro R
      rw [one_mul]
      apply opNorm_le_bound _ (norm_nonneg R)
      intro x
      change ‖R (K.orthogonalProjectionOnto x)‖≤‖R‖*‖x‖
      exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (K.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg R)))

omit [CompleteSpace H] in
@[simp] lemma extendOperator_apply (R : K →L[ℂ] K) (x : H) :
    extendOperator K R x=(R (K.orthogonalProjectionOnto x) : H) := rfl

local instance instNormedSpaceComplexContinuousLinearMapIdSubtypeMemSubmodule_solutions : NormedSpace ℂ (K →L[ℂ] K) := ContinuousLinearMap.toNormedSpace

local instance instNormedAddCommGroupContinuousLinearMapComplexIdSubtypeMemSubmodule_solutions : NormedAddCommGroup (K →L[ℂ] K) := ContinuousLinearMap.toNormedAddCommGroup

end Kadison.OperatorFunctionals

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M Q : VonNeumannAlgebra H) (hQM : Q≤M)

local instance matrixCornerInclusionDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixStandardForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance matrixStandardFormDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartitionRankComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance instDecidableEq_2 : DecidableEq ι := Classical.decEq ι

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_OrthogonalRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance orthogonalRankDecidableEq : DecidableEq ι := Classical.decEq ι

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PairTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Pairing

variable {J : Type*} [LinearOrder J]

abbrev Representatives (σ : Pairing J) := {j : J // j < σ j}

@[simp] theorem repr_representative (σ : Pairing J) (r : Representatives σ) :
    repr σ r = r := min_eq_left (le_of_lt r.property)

def pairEquiv (σ : Pairing J) : Representatives σ × Bool ≃ J :=
  Equiv.ofBijective (fun rb => if rb.2 then σ rb.1.1 else rb.1.1) (by
    constructor
    · rintro ⟨r, b⟩ ⟨s, c⟩ he
      have hr : r = s := by
        apply Subtype.ext
        have hh := congrArg (repr σ) he
        cases b <;> cases c <;> simpa only [Bool.false_eq_true, ↓reduceIte,
          repr_apply, repr_representative] using hh
      subst s
      congr 1
      cases b <;> cases c <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
      · exact (σ.apply_ne r he.symm).elim
      · exact (σ.apply_ne r he).elim
    · intro j
      by_cases hj : j < σ j
      · exact ⟨(⟨j, hj⟩, false), rfl⟩
      · have hj' : σ j < j := lt_of_le_of_ne (le_of_not_gt hj) (σ.apply_ne j)
        refine ⟨(⟨σ j, ?_⟩, true), ?_⟩
        · simpa only [apply_apply] using hj'
        · exact σ.apply_apply j)

@[simp] theorem pairEquiv_false (σ : Pairing J) (r : Representatives σ) :
    pairEquiv σ (r, false) = r := rfl

@[simp] theorem pairEquiv_true (σ : Pairing J) (r : Representatives σ) :
    pairEquiv σ (r, true) = σ r := rfl

def pairFunctionEquiv (σ : Pairing J) (I : Type*) :
    (J → I) ≃ (Representatives σ → Bool → I) :=
  (Equiv.arrowCongr (pairEquiv σ).symm (Equiv.refl I)).trans
    (Equiv.curry (Representatives σ) Bool I)

@[simp] theorem pairFunctionEquiv_apply (σ : Pairing J) {I : Type*}
    (b : J → I) (r : Representatives σ) (v : Bool) :
    pairFunctionEquiv σ I b r v = b (pairEquiv σ (r, v)) := rfl

end Kadison.Pairing
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PairTrace2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Pairing

variable {J : Type*} [LinearOrder J]

lemma repr_lt_apply (σ : Pairing J) (j : J) : repr σ j < σ (repr σ j) := by
  rcases lt_or_gt_of_ne (σ.apply_ne j).symm with hj | hj
  · simpa only [repr, min_eq_left (le_of_lt hj)] using hj
  · simpa only [repr, min_eq_right (le_of_lt hj), apply_apply] using hj

end Kadison.Pairing
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RationalStarExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

namespace Kadison.RationalStarExtension

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance instNormedAlgebraRat_solutions : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A

end Kadison.RationalStarExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakDualHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology ComplexOrder

namespace Kadison.WeakDualHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

local instance instAddCommGroupWeakDualComplex_solutions : AddCommGroup (WeakDual ℂ E) := inferInstanceAs (AddCommGroup (E →L[ℂ] ℂ))

local instance instModuleRealWeakDualComplex_solutions : Module ℝ (WeakDual ℂ E) := inferInstanceAs (Module ℝ (E →L[ℂ] ℂ))

def hull (S : Set (WeakDual ℂ E)) : Set (WeakDual ℂ E) := closure (convexHull ℝ S)

lemma eval_nonneg {S : Set (WeakDual ℂ E)} (a : E)
    (h : ∀ f∈S,0≤f a) {f : WeakDual ℂ E} (hf : f∈hull S) : 0≤f a := by
  have hc : IsClosed {f : WeakDual ℂ E | 0≤f a} :=
    isClosed_le continuous_const (WeakDual.eval_continuous a)
  have hv : Convex ℝ {f : WeakDual ℂ E | 0≤f a} := by
    intro g hg k hk s t hs ht _
    change 0 ≤ s • g a+t • k a
    exact add_nonneg (smul_nonneg hs (show 0≤g a from hg))
      (smul_nonneg ht (show 0≤k a from hk))
  exact closure_minimal (convexHull_min h hv) hc hf

end Kadison.WeakDualHull

end

end
end

end OAI
end


