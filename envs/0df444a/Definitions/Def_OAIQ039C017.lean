-- Prove2me | Definitions.Def_OAIQ039C017
-- name    : OAIQ039C017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:13:58.595957+00:00
-- url     : https://prove2.me/theorems/8068c677-5ad4-4e54-9011-e0db6772c2c9
-- title:
--   Definitions bundle OAIQ039C017 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 25 definitions, 7 instances and 16 theorems. The definitions and types are `OAI.Kadison.ReducingRepresentation.compression`, `OAI.Kadison.ReducingRepresentation.extendZero`, `OAI.Kadison.ReducingRepresentation.matrixInclusion`, `OAI.Kadison.RepresentedTower.stageUnitaryMap`, `OAI.Kadison.RepresentedTower.stageUnitaryRepresentation`, `OAI.Kadison.RepresentedTower.unitaryRepresentation`, `OAI.Kadison.SchurWeyl.IsEndpointPairing`, `OAI.Kadison.SchurWeyl.inflateMatrix`, `OAI.Kadison.SchurWeyl.permutationMatrix`, `OAI.Kadison.SchurWeyl.rawCycleTrace`, `OAI.Kadison.SchurWeyl.tensorMatrices`, `OAI.Kadison.SchurWeyl.tensorPower`, `OAI.Kadison.SchurWeyl.traceForm`, `OAI.Kadison.SeparableReducingHull.generator`, `OAI.Kadison.SeparableReducingHull.hull`, `OAI.Kadison.SeparableReducingHull.orbit`, `OAI.Kadison.SeparableReducingHull.reducingAlgebra`, `OAI.Kadison.SeparableSmall.Model`, `OAI.Kadison.SeparableSmall.unitary`, `OAI.Kadison.SeparableTest.algebra`, `OAI.Kadison.SeparableTest.generators`, `OAI.Kadison.SeparableTest.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra`, `OAI.Kadison.SeparableTest.space`, `OAI.Kadison.TracialL2.norm`, `OAI.Kadison.centeredSpace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CenteredSpace`, `Commutator_CycleInvariants`, `Commutator_CyclePairTrace3`, `Commutator_InvariantForms`, `Commutator_ModuleZeroExtension`, `Commutator_ReducingCompression`, `Commutator_ReducingMatrix`, `Commutator_RepresentedTowerAverage`, `Commutator_SchurWeylDevelopment`, `Commutator_SeparableReducingHull`, `Commutator_SeparableSmall`, `Commutator_SeparableTestGeometry`, `Commutator_TracialL2Tools`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C029` and `OAIQ039C030`; the statements `OAI.Kadison.CornerPolarTransfer.compressed_scalar_polar`, `OAI.Kadison.CornerPolarTransfer.defect_bound`, `OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership`, `OAI.Kadison.FinitePatching.Words.momentBound_add`, `OAI.Kadison.FinitePatching.Words.moment_limit_of_dense_coefficients`, `OAI.Kadison.FinitePatching.Words.word_perturbation_bound`, `OAI.Kadison.FinitePatching.exists_finite_word_patch`, `OAI.Kadison.FinitePatching.trace_centered_compression_bound`, `OAI.Kadison.RelativeCornerQuantization.exists_polar_cut` and `OAI.Kadison.RelativeCornerQuantization.exists_relative_centered_compression`; the proofs of `OAI.Kadison.CyclicSpatial.exists_cyclic_intertwiner` and `OAI.Kadison.MatrixCornerImplementation.exists_local_module`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_CenteredSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

abbrev centeredSpace (Ω : E) : Submodule ℂ E := (ℂ ∙ Ω)ᗮ

end Kadison
end

end OAI
end

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

def tensorPower (A : Matrix I I 𝕜) : Matrix (J → I) (J → I) 𝕜 :=
  fun a b => ∏ j, A (a j) (b j)

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
@[simp] lemma tensorPower_apply (A : Matrix I I 𝕜) (a b : J → I) :
    tensorPower A a b = ∏ j, A (a j) (b j) := rfl

def permutationMatrix (σ : Equiv.Perm J) : Matrix (J → I) (J → I) 𝕜 :=
  fun a b => if a = b ∘ σ.symm then 1 else 0

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

def tensorMatrices (A : J → Matrix I I 𝕜) : Matrix (J → I) (J → I) 𝕜 :=
  fun a b => ∏ j, A j (a j) (b j)

def traceForm (T : Matrix (J → I) (J → I) 𝕜) :
    MultilinearMap 𝕜 (fun _ : J => Matrix I I 𝕜) 𝕜 :=
  ∑ a, ∑ b, T a b • ((MultilinearMap.mkPiRing 𝕜 J 1).compLinearMap
    fun j => Matrix.entryLinearMap 𝕜 𝕜 (b j) (a j))

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
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

def rawCycleTrace (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) : 𝕜 :=
  Matrix.trace (permutationMatrix σ * tensorMatrices A)

omit [DecidableEq J] in
lemma constant_on_cycle {R : Type*} (σ : Equiv.Perm J) (f : J → R)
    (hf : ∀ j, f (σ j) = f j) {i j : J} (h : σ.SameCycle i j) : f i = f j := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, hf] using ih

def inflateMatrix {R : Type*} [DecidableEq R] (A : Matrix I I 𝕜) :
    Matrix (I × R) (I × R) 𝕜 :=
  fun a b => if a.2 = b.2 then A a.1 b.1 else 0

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclePairTrace3
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

namespace Kadison.SchurWeyl

variable {J : Type*}

def IsEndpointPairing (σ : Equiv.Perm (Option J)) : Prop :=
  σ none = none ∧ (∀ j, σ (σ j) = j) ∧ ∀ j, σ j = j → j = none

lemma some_removeNone_of_fixed (σ : Equiv.Perm (Option J)) (hσ : σ none = none) (j : J) :
    some (σ.removeNone j) = σ (some j) := by
  apply Equiv.removeNone_some
  cases he : σ (some j) with
  | none =>
    have hh := σ.injective (he.trans hσ.symm)
    cases hh
  | some k => exact ⟨k, rfl⟩

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ModuleZeroExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H F : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (F →L[ℂ] F))

variable (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

def extendZero (T : K →L[ℂ] F) : H →L[ℂ] F := T.comp K.orthogonalProjectionOnto

omit [CompleteSpace H] [CompleteSpace F] in
@[simp] lemma extendZero_subtype (T : K →L[ℂ] F) (x : K) :
    extendZero (K := K) T (x:H)=T x := by simp [extendZero]

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ReducingCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (K : Submodule ℂ H) [CompleteSpace K]
  (hinv : ∀ (a : A) (x : H), x∈K → σ a x∈K)

def compression (S : H →L[ℂ] H) : K →L[ℂ] K :=
  K.orthogonalProjectionOnto.comp (S.comp K.subtypeL)

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ReducingMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def matrixInclusion (K : Submodule ℂ H) (h : ℕ) :
    (PiLp 2 fun _ : Fin h => K) →ₗᵢ[ℂ] (PiLp 2 fun _ : Fin h => H) where
  toFun x := WithLp.toLp 2 (fun i => (x i:H))
  map_add' x y := by ext i; rfl
  map_smul' c x := by ext i; rfl
  norm_map' x := by
    rw [PiLp.norm_eq_of_L2,PiLp.norm_eq_of_L2]
    rfl

omit [CompleteSpace H] in
@[simp] lemma matrixInclusion_apply (K : Submodule ℂ H) (h : ℕ)
    (x : PiLp 2 fun _ : Fin h => K) (i : Fin h) : matrixInclusion K h x i=(x i:H) := rfl

end Kadison.ReducingRepresentation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RepresentedTowerAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator Topology

open MeasureTheory Filter

namespace Kadison.RepresentedTower

variable {A K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))

def unitaryRepresentation : unitary A →* (K ≃ₗᵢ[ℂ] K) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    { toFun := fun u => ⟨ρ (u:A),Unitary.map_mem ρ u.property⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' u v := Subtype.ext (map_mul ρ (u:A) (v:A)) }

variable (I : ℕ → Type*) [∀ n,Fintype (I n)] [∀ n,DecidableEq (I n)] [∀ n,Nonempty (I n)]

variable (φ : ∀ n,Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

def stageUnitaryMap (n : ℕ) : unitary (Matrix (I n) (I n) ℂ) →* unitary A where
  toFun u := ⟨φ n (u : Matrix (I n) (I n) ℂ),Unitary.map_mem (φ n) u.property⟩
  map_one' := Subtype.ext (map_one (φ n))
  map_mul' u v := Subtype.ext (map_mul (φ n) (u:Matrix (I n) (I n) ℂ) (v:Matrix (I n) (I n) ℂ))

def stageUnitaryRepresentation (n : ℕ) : unitary (Matrix (I n) (I n) ℂ) →* (K ≃ₗᵢ[ℂ] K) :=
  (unitaryRepresentation ρ).comp (stageUnitaryMap I φ n)

end Kadison.RepresentedTower

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableReducingHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.SeparableReducingHull

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def generator (T : ι → H →L[ℂ] H) (i : ι × Bool) : H →L[ℂ] H :=
  if i.2 then star (T i.1) else T i.1

def orbit (T : ι → H →L[ℂ] H) (v : κ → H) (p : List (ι × Bool) × κ) : H :=
  (p.1.map (generator T)).prod (v p.2)

def hull (T : ι → H →L[ℂ] H) (v : κ → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range (orbit T v))).topologicalClosure

lemma hull_closed (T : ι → H →L[ℂ] H) (v : κ → H) :
    IsClosed (hull T v : Set H) := Submodule.isClosed_topologicalClosure _

instance hull_complete (T : ι → H →L[ℂ] H) (v : κ → H) : CompleteSpace (hull T v) :=
  (hull_closed T v).completeSpace_coe

lemma vector_mem (T : ι → H →L[ℂ] H) (v : κ → H) (j : κ) : v j∈hull T v := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨([],j),by simp [orbit]⟩

lemma generator_invariant (T : ι → H →L[ℂ] H) (v : κ → H) (i : ι × Bool) :
    ∀ x∈hull T v, generator T i x∈hull T v := by
  change (Submodule.span ℂ (Set.range (orbit T v))).topologicalClosure ≤
    (hull T v).comap (generator T i).toLinearMap
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨w,j⟩,rfl⟩
    change generator T i (orbit T v (w,j))∈hull T v
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨(i::w,j),by simp [orbit,mul_apply_eq_comp]⟩
  · exact (hull_closed T v).preimage (generator T i).continuous

lemma invariant (T : ι → H →L[ℂ] H) (v : κ → H) (i : ι) :
    ∀ x∈hull T v,T i x∈hull T v := by
  simpa only [generator,Bool.false_eq_true,ite_false] using generator_invariant T v (i,false)

lemma star_invariant (T : ι → H →L[ℂ] H) (v : κ → H) (i : ι) :
    ∀ x∈hull T v,star (T i) x∈hull T v := by
  simpa only [generator,ite_true] using generator_invariant T v (i,true)

instance hull_separable [Countable ι] [Countable κ]
    (T : ι → H →L[ℂ] H) (v : κ → H) : TopologicalSpace.SeparableSpace (hull T v) := by
  apply TopologicalSpace.IsSeparable.separableSpace
  exact ((Set.countable_range (orbit T v)).isSeparable.span (R := ℂ)).closure

def reducingAlgebra (K : Submodule ℂ H) : StarSubalgebra ℂ (H →L[ℂ] H) where
  carrier := {T | (∀ x∈K,T x∈K) ∧ (∀ x∈K,star T x∈K)}
  zero_mem' := by simp
  add_mem' := by
    rintro S T ⟨hS,hSs⟩ ⟨hT,hTs⟩
    constructor
    · intro x hx; exact K.add_mem (hS x hx) (hT x hx)
    · intro x hx; simpa only [star_add,add_apply] using K.add_mem (hSs x hx) (hTs x hx)
  mul_mem' := by
    rintro S T ⟨hS,hSs⟩ ⟨hT,hTs⟩
    constructor
    · intro x hx; exact hS _ (hT x hx)
    · intro x hx; simpa only [star_mul,mul_apply_eq_comp] using hTs _ (hSs x hx)
  algebraMap_mem' := by
    intro c
    constructor
    · intro x hx; simpa only [Algebra.algebraMap_eq_smul_one,smul_apply,
        one_apply_eq_self] using K.smul_mem c hx
    · intro x hx; simpa only [Algebra.algebraMap_eq_smul_one,star_smul,star_one,
        smul_apply,one_apply_eq_self] using K.smul_mem (star c) hx
  star_mem' := by rintro T ⟨hT,hTs⟩; exact ⟨hTs,by simpa only [star_star] using hT⟩

lemma reducingAlgebra_closed (K : Submodule ℂ H) (hK : IsClosed (K : Set H)) :
    IsClosed (reducingAlgebra K : Set (H →L[ℂ] H)) := by
  change IsClosed {T : H →L[ℂ] H | (∀ x∈K,T x∈K) ∧ (∀ x∈K,star T x∈K)}
  simp only [Set.ofPred_and,Set.ofPred_forall]
  apply IsClosed.inter
  · exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
      hK.preimage (show Continuous (fun T : H →L[ℂ] H => T x) by fun_prop)))
  · exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
      hK.preimage (show Continuous (fun T : H →L[ℂ] H => star T x) by fun_prop)))

lemma generator_mem_reducingAlgebra (T : ι → H →L[ℂ] H) (v : κ → H) (i : ι) :
    T i∈reducingAlgebra (hull T v) := ⟨invariant T v i,star_invariant T v i⟩

end Kadison.SeparableReducingHull

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

universe u

namespace Kadison.SeparableSmall

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
theorem small : Small.{0} H := by
  obtain ⟨F,hF⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X:=H)
  exact small_of_injective hF.injective

local instance separableSmallSmall : Small.{0} H := small H

abbrev Model : Type := Shrink H

instance model_inner : InnerProductSpace ℂ (Model H) where
  inner x y := inner ℂ ((equivShrink H).symm x) ((equivShrink H).symm y)
  conj_inner_symm x y := inner_conj_symm _ _
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner ((equivShrink H).symm x)
  add_left x y z := by
    change inner ℂ (Shrink.linearEquiv ℂ H (x+y)) _ = _
    rw [map_add,inner_add_left]
    rfl
  smul_left x y c := by
    change inner ℂ (Shrink.linearEquiv ℂ H (c • x)) _ = _
    rw [map_smul,inner_smul_left]
    rfl

def unitary : Model H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := Shrink.linearEquiv ℂ H
  norm_map' _ := rfl

instance model_complete : CompleteSpace (Model H) :=
  (unitary H).toIsometryEquiv.completeSpace_iff.mpr inferInstance

instance model_separable : TopologicalSpace.SeparableSpace (Model H) :=
  (unitary H).symm.surjective.denseRange.separableSpace (unitary H).symm.continuous

end Kadison.SeparableSmall

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SeparableTestGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.SeparableTest

open SeparableReducingHull ReducingRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (Y : H →L[ℂ] H)

def generators : ((Fin h×Fin h)⊕Unit) → H →L[ℂ] H :=
  Sum.elim (fun ij => X ij.1 ij.2) (fun _ => Y)

def space (ξ : PiLp 2 (fun _ : Fin h => H)) : Submodule ℂ H := hull (generators h X Y) (fun i => ξ i)

def algebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun ij : Fin h×Fin h => X ij.1 ij.2))).topologicalClosure

instance algebra_closed : IsClosed (algebra h X : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance algebra_cstar : CStarAlgebra (algebra h X) := StarSubalgebra.cstarAlgebra _

local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra : PartialOrder (algebra h X) := CStarAlgebra.spectralOrder _

variable (ξ : PiLp 2 (fun _ : Fin h => H))

lemma algebra_reduces : algebra h X ≤ reducingAlgebra (space h X Y ξ) := by
  apply StarSubalgebra.topologicalClosure_minimal
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact generator_mem_reducingAlgebra (generators h X Y) (fun i => ξ i) (Sum.inl (i,j))
  · exact reducingAlgebra_closed _ (hull_closed _ _)

lemma Y_invariant : ∀ x∈space h X Y ξ,Y x∈space h X Y ξ :=
  invariant (generators h X Y) (fun i => ξ i) (Sum.inr Unit.unit)

end Kadison.SeparableTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

def norm (a : A) : ℝ := ‖τ.toPreGNS a‖

end Kadison.TracialL2

end

end
end

end OAI
end


