-- Prove2me | Definitions.Def_OAIQ039C016
-- name    : OAIQ039C016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:13:26.502923+00:00
-- url     : https://prove2.me/theorems/65ffaea5-5f82-42c9-a7ee-59b2f7df3d80
-- title:
--   Definitions bundle OAIQ039C016 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 11 definitions, 1 inductive type or structure and 8 theorems. The definitions and types are `OAI.Kadison.PartialIsometryOrder.Replicas`, `OAI.Kadison.ProjectionShift.partialSum`, `OAI.Kadison.RectangularColumn.SumHilbert`, `OAI.Kadison.RectangularColumn.instNormedAddCommGroupContinuousLinearMapComplexId_solutions`, `OAI.Kadison.RectangularColumn.instNormedSpaceComplexContinuousLinearMapId_solutions`, `OAI.Kadison.RectangularColumn.triangularMap`, `OAI.Kadison.RectangularTensors.perm`, `OAI.Kadison.RectangularTensors.tensor`, `OAI.Kadison.SchurWeyl.assignmentMatrix`, `OAI.Kadison.SchurWeyl.coefficientMatrix`, `OAI.Kadison.gramEquiv`, `OAI.Kadison.gramIsometry`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_InvariantForms`, `Commutator_ProjectionShift`, `Commutator_ProjectionStrong`, `Commutator_ProperIsometryReplicas`, `Commutator_RectangularColumn`, `Commutator_RectangularTensors`, `Commutator_SchurWeylDevelopment`, `Commutator_TensorPermutations`, `Commutator_TensorPermutations2`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C030` and `OAIQ039C041`; the statement `OAI.Kadison.RectangularColumn.column_bound`; the proof of `OAI.Kadison.SchurWeyl.matrix_union_expansion`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_SchurWeylDevelopment
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

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def assignmentMatrix (b c : J → I) : Matrix I I 𝕜 :=
  fun r s => ∑ j, if s = b j ∧ r = c j then 1 else 0

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InvariantForms
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

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def coefficientMatrix (F : MultilinearMap 𝕜 (fun _ : J => Matrix I I 𝕜) 𝕜) :
    Matrix (J → I) (J → I) 𝕜 :=
  fun a b => F (fun j => Matrix.single (b j) (a j) 1)

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionStrong
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.ProjectionChains

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_norm_sq {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖P x‖^2=(inner ℂ (P x) x).re := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.isSelfAdjoint
  have he : inner ℂ (P (P x)) x=inner ℂ (P x) (P x) := hs (P x) x
  rw [←he]
  have hp := congrArg (fun T : H →L[ℂ] H => T x) hP.isIdempotentElem.eq
  change P (P x)=P x at hp
  rw [hp]
  rfl

lemma projection_norm_mono {P Q : H →L[ℂ] H} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hPQ : P≤Q) (x : H) : ‖P x‖≤‖Q x‖ := by
  have h := (hP.le_iff_mul_eq_left hQ).mp hPQ
  have hx : P (Q x)=P x := congrArg (fun T : H →L[ℂ] H => T x) h
  rw [←hx]
  exact (P.le_opNorm (Q x)).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hP.norm_le P) (norm_nonneg (Q x)))

end Kadison.ProjectionChains

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.ProjectionShift

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (w p : H →L[ℂ] H)

def partialSum : ℕ → H →L[ℂ] H
  | 0 => 0
  | n+1 => p+w*partialSum n*star w

end Kadison.ProjectionShift

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperIsometryReplicas
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

structure Replicas (M : VonNeumannAlgebra H) (r : H →L[ℂ] H) where
  a : ℕ → H →L[ℂ] H
  mem : ∀ n,a n∈M
  initial : ∀ n,star (a n)*a n=r
  cross : ∀ n m,n≠m → star (a n)*a m=0
  source : ∀ n,a n*r=a n

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RectangularColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.RectangularColumn

variable {A K F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

local instance instNormedAddCommGroupContinuousLinearMapComplexId_solutions : NormedAddCommGroup (K →L[ℂ] F) := ContinuousLinearMap.toNormedAddCommGroup

local instance instNormedSpaceComplexContinuousLinearMapId_solutions : NormedSpace ℂ (K →L[ℂ] F) := ContinuousLinearMap.toNormedSpace

abbrev SumHilbert (F K : Type*) := WithLp 2 (F × K)

def triangularMap (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F)) (a : A) :
    SumHilbert F K →L[ℂ] SumHilbert F K :=
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ F K
  e.symm.toContinuousLinearMap.comp
    (((lam a).comp (ContinuousLinearMap.fst ℂ F K)+
      (D a).comp (ContinuousLinearMap.snd ℂ F K)).prod
      ((σ a).comp (ContinuousLinearMap.snd ℂ F K)) |>.comp e.toContinuousLinearMap)

@[simp] lemma triangularMap_apply (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F))
    (a : A) (x : SumHilbert F K) :
    triangularMap σ lam D a x=WithLp.toLp 2 (lam a x.fst+D a x.snd,σ a x.snd) := rfl

lemma derivation_one (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (lam : A →⋆ₐ[ℂ] (F →L[ℂ] F)) (D : A →L[ℂ] (K →L[ℂ] F))
    (hD : ∀ a b, D (a*b)=(D a).comp (σ b)+(lam a).comp (D b)) : D 1=0 := by
  have h := hD 1 1
  have he : D 1=D 1+D 1 := by
    simpa only [one_mul,map_one,ContinuousLinearMap.one_def,ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp] using h
  exact (add_eq_left.mp he.symm)

end Kadison.RectangularColumn

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RectangularTensors
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

namespace Kadison.RectangularTensors

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I K L J : Type*} [Fintype I] [Fintype K] [Fintype L] [Fintype J] [DecidableEq J]

def tensor (A : J → Matrix I K 𝕜) : Matrix (J → I) (J → K) 𝕜 :=
  fun a b => ∏ j, A j (a j) (b j)

def perm [DecidableEq I] (σ : Equiv.Perm J) : Matrix (J → I) (J → I) 𝕜 :=
  fun a b => if a = b ∘ σ.symm then 1 else 0

end Kadison.RectangularTensors
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorPermutations
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

section Gram

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem inner_linearCombination_eq (a : ι → E) (b : ι → F)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j))
    (x y : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ b x) (Finsupp.linearCombination ℂ b y) =
      inner ℂ (Finsupp.linearCombination ℂ a x) (Finsupp.linearCombination ℂ a y) := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

def gramIsometry (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) : E →ₗᵢ[ℂ] F := by
  let A := Finsupp.linearCombination ℂ a
  let B := Finsupp.linearCombination ℂ b
  have hA : Function.Surjective A := by
    apply LinearMap.range_eq_top.mp
    rwa [Finsupp.range_linearCombination]
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_linearCombination_eq a b h]
    rw [LinearMap.mem_ker.mp hx]
    simp
  let f := (LinearMap.ker A).liftQ B hker |>.comp
    (A.quotKerEquivOfSurjective hA).symm.toLinearMap
  have happ : ∀ x, f (A x) = B x := by
    intro x
    change (LinearMap.ker A).liftQ B hker
      ((A.quotKerEquivOfSurjective hA).symm (A x)) = B x
    have he : (A.quotKerEquivOfSurjective hA).symm (A x) =
        Submodule.Quotient.mk x := by
      apply (A.quotKerEquivOfSurjective hA).injective
      simp [LinearMap.quotKerEquivOfSurjective_apply_mk]
    rw [he, Submodule.liftQ_apply]
  refine ⟨f, ?_⟩
  apply (LinearMap.norm_map_iff_inner_map_map f).mpr
  intro x y
  obtain ⟨v, rfl⟩ := hA x
  obtain ⟨w, rfl⟩ := hA y
  rw [happ, happ]
  exact inner_linearCombination_eq a b h v w

@[simp] theorem gramIsometry_apply (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) (i : ι) :
    gramIsometry a b ha h (a i) = b i := by
  classical
  unfold gramIsometry
  dsimp
  have hA : Function.Surjective (Finsupp.linearCombination ℂ a) := by
    apply LinearMap.range_eq_top.mp
    rwa [Finsupp.range_linearCombination]
  have he : ((Finsupp.linearCombination ℂ a).quotKerEquivOfSurjective hA).symm
      (a i) = Submodule.Quotient.mk (Finsupp.single i 1) := by
    apply ((Finsupp.linearCombination ℂ a).quotKerEquivOfSurjective hA).injective
    simp [LinearMap.quotKerEquivOfSurjective_apply_mk]
  rw [he, Submodule.liftQ_apply]
  simp

end Gram

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorPermutations2
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

section GramEquiv

variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem gramIsometry_surjective (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (hb : Submodule.span ℂ (Set.range b) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) :
    Function.Surjective (gramIsometry a b ha h) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hb]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨a i, gramIsometry_apply a b ha h i⟩

def gramEquiv (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (hb : Submodule.span ℂ (Set.range b) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) : E ≃ₗᵢ[ℂ] F :=
  LinearIsometryEquiv.ofSurjective (gramIsometry a b ha h)
    (gramIsometry_surjective a b ha hb h)

@[simp] theorem gramEquiv_apply (a : ι → E) (b : ι → F)
    (ha : Submodule.span ℂ (Set.range a) = ⊤)
    (hb : Submodule.span ℂ (Set.range b) = ⊤)
    (h : ∀ i j, inner ℂ (b i) (b j) = inner ℂ (a i) (a j)) (i : ι) :
    gramEquiv a b ha hb h (a i) = b i := gramIsometry_apply a b ha h i

end GramEquiv

end Kadison
end

end OAI
end


