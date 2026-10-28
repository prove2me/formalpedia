-- Prove2me | Definitions.Def_OAIQ039C047
-- name    : OAIQ039C047
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:56.458215+00:00
-- url     : https://prove2.me/theorems/66ab4e88-00f2-4a76-888f-e83f35ac0849
-- title:
--   Definitions bundle OAIQ039C047 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 9 definitions and 12 theorems. The definitions and types are `OAI.Kadison.FreeBlocks.blockEmbedding`, `OAI.Kadison.FreeBlocks.blockIsometry`, `OAI.Kadison.FreeBlocks.letterGNSIso`, `OAI.Kadison.FreeBlocks.letterPreIso`, `OAI.Kadison.FreeBlocks.letterPreMap`, `OAI.Kadison.HilbertSequence.actionHom`, `OAI.Kadison.HilbertSequence.mapVector`, `OAI.Kadison.Kaplansky.starHomNet`, `OAI.Kadison.TracialSequence.vectorCLM`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_BoundedSequenceClosed`, `Commutator_EndpointGNS2`, `Commutator_FreeBlockTensor`, `Commutator_FreeSymmetry11`, `Commutator_HilbertSequenceOperator`, `Commutator_KaplanskyFullRange`, `Commutator_KaplanskyStarHomNet`, `Commutator_TracialSequence`.
--
--   **Imports.** It imports the bundles `OAIQ039C032`, `OAIQ039C034`, `OAIQ039C036` and `OAIQ039C037` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C055`, `OAIQ039C056` and `OAIQ039C058`; the statements `OAI.Kadison.FreeBlocks.norm_base_mul` and `OAI.Kadison.FreeBlocks.repeated_norm`; the proofs of `OAI.Kadison.FreeBlocks.gns_vectorState` and `OAI.Kadison.TracialGNS.word_multiplicity_both`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C032
import Definitions.Def_OAIQ039C034
import Definitions.Def_OAIQ039C036
import Definitions.Def_OAIQ039C037

section
-- module Solutions.OAIQ039_CM.Commutator_BoundedSequenceClosed
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable {A H : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (ω : Ultrafilter ℕ) (v : A →L[ℂ] H)

def mapVector (a : ℕ →ᵇ A) : Space ω H := (mapPre ω v a : Space ω H)

omit [InnerProductSpace ℂ H] in
@[simp] lemma seq_sub' (a b : Pre ω H) (i : ℕ) : (a-b).seq i=a.seq i-b.seq i := rfl

lemma norm_map_difference_tendsto (a b : ℕ →ᵇ A) :
    Tendsto (fun i => ‖v (a i)-v (b i)‖) (ω : Filter ℕ)
      (𝓝 ‖mapVector ω v a-mapVector ω v b‖) := by
  simpa only [mapVector,←Completion.coe_sub,Completion.norm_coe,seq_sub',mapPre,BoundedContinuousFunction.comp_apply] using
    tendsto_norm ω H (mapPre ω v a-mapPre ω v b)

theorem bounded_image_isClosed (hω : (ω : Filter ℕ)≤atTop)
    (K : Set A) (C : ℝ) (hK : ∀ a∈K, ‖a‖≤C) :
    IsClosed {x : Space ω H | ∃ a : ℕ →ᵇ A, (∀ i, a i∈K) ∧ mapVector ω v a=x} := by
  classical
  apply isClosed_of_closure_subset
  intro x hx
  let ε (n : ℕ) : ℝ := (1/2:ℝ)^n
  have hε (n : ℕ) : 0<ε n := pow_pos (by norm_num) n
  have hanti {j k : ℕ} (hjk : j≤k) : ε k≤ε j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hjk
  have hn (n : ℕ) : ∃ a : ℕ →ᵇ A, (∀ i, a i∈K) ∧ ‖mapVector ω v a-x‖<ε n := by
    obtain ⟨y,⟨a,ha,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp hx (ε n) (hε n)
    exact ⟨a,ha,by simpa only [dist_eq_norm,norm_sub_rev] using hy⟩
  choose f hf he using hn
  have hpair (j k : ℕ) (hjk : j≤k) :
      ∀ᶠ i in (ω : Filter ℕ), ‖v (f j i)-v (f k i)‖≤3*ε j := by
    have hlt : ‖mapVector ω v (f j)-mapVector ω v (f k)‖<3*ε j := by
      have h := norm_sub_le_norm_sub_add_norm_sub (mapVector ω v (f j)) x (mapVector ω v (f k))
      rw [norm_sub_rev x] at h
      have hj := he j
      have hk := he k
      have hk' := hanti hjk
      have hp := hε j
      linarith
    exact (norm_map_difference_tendsto ω v (f j) (f k)).eventually (gt_mem_nhds hlt) |>.mono
      (fun _ hi => le_of_lt hi)
  let p (n i : ℕ) : Prop := ∀ j≤n, ∀ k≤n, j≤k → ‖v (f j i)-v (f k i)‖≤3*ε j
  have hp (n : ℕ) : ∀ᶠ i in (ω : Filter ℕ), p n i := by
    have hh : ∀ᶠ i in (ω : Filter ℕ), ∀ j∈Finset.range (n+1),
        ∀ k∈Finset.range (n+1), j≤k → ‖v (f j i)-v (f k i)‖≤3*ε j := by
      apply (eventually_all_finset (Finset.range (n+1))).mpr
      intro j _
      apply (eventually_all_finset (Finset.range (n+1))).mpr
      intro k _
      by_cases hjk : j≤k
      · exact (hpair j k hjk).mono (fun _ hi _ => hi)
      · exact Eventually.of_forall (fun _ hi => (hjk hi).elim)
    filter_upwards [hh] with i hi
    intro j hj k hk hjk
    exact hi j (Finset.mem_range.mpr (by omega)) k (Finset.mem_range.mpr (by omega)) hjk
  obtain ⟨d,hd,hreq⟩ := UltrafilterDiagonal.depth hω p hp
  let a : ℕ →ᵇ A := BoundedContinuousFunction.mkOfDiscrete (fun i => f (d i/2) i) (2*C)
    (fun i j => (dist_le_norm_add_norm _ _).trans (by
      have hi := hK _ (hf (d i/2) i)
      have hj := hK _ (hf (d j/2) j)
      linarith))
  have ha (i : ℕ) : a i∈K := hf (d i/2) i
  have hnorm (j : ℕ) : ‖mapVector ω v a-mapVector ω v (f j)‖≤3*ε j := by
    apply le_of_tendsto (norm_map_difference_tendsto ω v a (f j))
    filter_upwards [hd.eventually (eventually_ge_atTop (2*j+2))] with i hi
    have hleft : j≤d i/2 := by omega
    have hright : d i/2<d i := by omega
    have hh := hreq i (d i/2) hright j hleft (d i/2) (le_refl _) hleft
    simpa only [a,BoundedContinuousFunction.mkOfDiscrete_apply,norm_sub_rev] using hh
  have hnorm' (j : ℕ) : ‖mapVector ω v a-x‖≤4*ε j := by
    have h := norm_sub_le_norm_sub_add_norm_sub (mapVector ω v a) (mapVector ω v (f j)) x
    have h1 := hnorm j
    have h2 := he j
    linarith
  have hlim : Tendsto (fun j => 4*ε j) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)))
  have hz : ‖mapVector ω v a-x‖≤0 := ge_of_tendsto hlim (Eventually.of_forall hnorm')
  exact ⟨a,ha,sub_eq_zero.mp (norm_le_zero_iff.mp hz)⟩

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_EndpointGNS2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.TracialGNS

open PreHilbert

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

omit [Nonempty I] in
@[simp] lemma stageRepresentation_vacuum (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (a : Matrix I I ℂ) :
    stageRepresentation τ φ a (vacuum τ) = stageVector τ φ a := by
  change τ.gnsStarAlgHom (φ a) (τ.toPreGNS 1 : τ.GNS) = (τ.toPreGNS (φ a) : τ.GNS)
  rw [left_coe, mul_one]

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

variable (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

include hfree hij

def blockIsometry (n : ℕ) : blockTensor t S i j n →ₗᵢ[ℂ] preSpace t :=
  (blockReadPre t S n).isometryOfInner (inner_blockReadPre t S hfree hij n)

def blockEmbedding (n : ℕ) : Completion (blockTensor t S i j n) →ₗᵢ[ℂ] t.functional.GNS where
  toLinearMap := (blockIsometry t S hfree hij n).toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry11
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace

open scoped ComplexOrder InnerProductSpace

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι) (hS : S i=f.range)

lemma inner_pre_one (x : preSpace (pullbackState t f hf)) :
    inner ℂ ((pullbackState t f hf).functional.toPreGNS 1) x =
      (pullbackState t f hf).functional ((pullbackState t f hf).functional.ofPreGNS x) := by
  simp only [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_one, one_mul]

def letterPreMap :
    HilbertCompletion.centered ((pullbackState t f hf).functional.toPreGNS 1) →ₗᵢ[ℂ]
      letterSpace t S i where
  toLinearMap :=
    { toFun := fun x => ⟨factorPreMap t f hf S i hS (x : preSpace (pullbackState t f hf)),
        (factorPreMap t f hf S i hS (x : preSpace (pullbackState t f hf))).property, by
          have hx := Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property
          rw [inner_pre_one] at hx
          exact hx⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact congrArg (fun z : factorSpace t S i => (z : preSpace t))
          ((factorPreMap t f hf S i hS).map_add
            (x : preSpace (pullbackState t f hf)) (y : preSpace (pullbackState t f hf)))
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact congrArg (fun z : factorSpace t S i => (z : preSpace t))
          ((factorPreMap t f hf S i hS).map_smul c (x : preSpace (pullbackState t f hf))) }
  norm_map' x := (factorPreMap t f hf S i hS).norm_map x

lemma letterPreMap_surjective : Function.Surjective (letterPreMap t f hf S i hS) := by
  intro y
  obtain ⟨x,hx⟩ := factorPreMap_surjective t f hf S i hS ⟨y,y.property.1⟩
  have hx0 : (pullbackState t f hf).functional ((pullbackState t f hf).functional.ofPreGNS x)=0 := by
    have hx' := congrArg (fun z : factorSpace t S i => t.functional (t.functional.ofPreGNS z)) hx
    exact hx'.trans y.property.2
  refine ⟨⟨x,?_⟩,?_⟩
  · rwa [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_pre_one]
  · apply Subtype.ext
    change ((factorPreMap t f hf S i hS) x : preSpace t)=(y : preSpace t)
    exact congrArg (fun z : factorSpace t S i => (z : preSpace t)) hx

def letterPreIso : HilbertCompletion.centered ((pullbackState t f hf).functional.toPreGNS 1) ≃ₗᵢ[ℂ]
    letterSpace t S i :=
  LinearIsometryEquiv.ofSurjective (letterPreMap t f hf S i hS)
    (letterPreMap_surjective t f hf S i hS)

lemma pullback_pre_one_norm : ‖(pullbackState t f hf).functional.toPreGNS 1‖=1 := by
  rw [PositiveLinearMap.preGNS_norm_def]
  simp [map_one, t.normalized]

def letterGNSIso : Completion (letterSpace t S i) ≃ₗᵢ[ℂ]
    HilbertCompletion.centered
      (((pullbackState t f hf).functional.toPreGNS 1 : preSpace (pullbackState t f hf)) :
        (pullbackState t f hf).functional.GNS) :=
  (HilbertCompletion.congr (letterPreIso t f hf S i hS)).symm |>.trans
    (HilbertCompletion.centeredEquiv _ (pullback_pre_one_norm t f hf))

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertSequenceOperator
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable (ω : Ultrafilter ℕ)

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

variable [CompleteSpace E]

def actionHom : (ℕ →ᵇ (E →L[ℂ] E)) →⋆ₐ[ℂ] (Space ω E →L[ℂ] Space ω E) where
  toFun := act ω
  map_one' := act_one ω
  map_zero' := act_zero ω
  map_add' := act_add ω
  map_mul' := act_mul ω
  map_star' := act_star ω
  commutes' r := by
    change act ω (r • (1 : ℕ →ᵇ (E →L[ℂ] E)))=r • (1 : Space ω E →L[ℂ] Space ω E)
    rw [act_smul,act_one]

end Kadison.HilbertSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFullRange
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open Filter

namespace Kadison.Kaplansky

open OperatorAmplification CyclicColumns CyclicSpatial

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions_1
variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma matrixUnit_mem_matrixRange (i j : Fin 2) :
    matrixUnit (H:=H) (Fin 2) i j ∈ (matrixRepresentation (ι:=Fin 2) φ).range := by
  let X : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix
    (fun k l => if k=i ∧ l=j then 1 else 0)
  refine ⟨X,?_⟩
  ext x k
  change (∑ l,φ (X k l) (x l))=single (Fin 2) i (x j) k
  change (∑ l,φ (if k=i ∧ l=j then 1 else 0) (x l))=single (Fin 2) i (x j) k
  by_cases hk : k=i
  · fin_cases j <;> simp [hk,single_apply]
  · simp [hk,single_apply]

lemma diagonal_mem_matrixRange (a : A) :
    diagonal (H:=H) (Fin 2) (φ a) ∈ (matrixRepresentation (ι:=Fin 2) φ).range := by
  let X : CStarMatrix (Fin 2) (Fin 2) A := CStarMatrix.ofMatrix
    (fun k l => if k=l then a else 0)
  refine ⟨X,?_⟩
  ext x k
  change (∑ l,φ (if k=l then a else 0) (x l))=φ a (x k)
  fin_cases k <;> simp

lemma offDiagonal_matrixRange_bicommutant {T : H →L[ℂ] H}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range φ))) :
    offDiagonal T∈Set.centralizer (Set.centralizer
      (Set.range (matrixRepresentation (ι:=Fin 2) φ))) := by
  intro R hR
  have hU : ∀ i j,matrixUnit (Fin 2) i j*R=R*matrixUnit (Fin 2) i j :=
    fun i j => hR _ (matrixUnit_mem_matrixRange φ i j)
  let a := entry (Fin 2) R 0 0
  have he : R=diagonal (H:=H) (Fin 2) a := diagonal_of_matrixUnits (Fin 2) 0 R hU
  have ha : a∈Set.centralizer (Set.range φ) := by
    rintro _ ⟨b,rfl⟩
    exact entry_commutes (Fin 2) R (φ b) (hR _ (diagonal_mem_matrixRange φ b)) 0 0
  rw [he]
  apply commutes_of_entries (Fin 2)
  intro i j
  rw [entry_offDiagonal]
  split_ifs
  · exact hT a ha
  · exact star_bicommutant φ.range hT a ha
  · simp

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyStarHomNet
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.Kaplansky

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable (T : H →L[ℂ] H)
  (hT : T∈Set.centralizer (Set.centralizer (Set.range φ)))
  (hsT : IsSelfAdjoint T) (hnT : ‖T‖ ≤ 1)

include hT hsT hnT in
lemma starHom_net_approx_exists (j : Finset H × ℕ) : ∃ a : A,
    ‖a‖ ≤ 1 ∧ ∀ x∈j.1,‖φ a x-T x‖<(j.2+1:ℝ)⁻¹ := by
  classical
  obtain ⟨a,_,hna,he⟩ := range_selfAdjoint_contraction_finite_approx j.1 φ hT hsT hnT
    (fun x => (x:H)) ((j.2+1:ℝ)⁻¹) (by positivity)
  exact ⟨a,hna,fun x hx => he ⟨x,hx⟩⟩

def starHomNet (j : Finset H × ℕ) : A :=
  (starHom_net_approx_exists φ T hT hsT hnT j).choose

lemma starHomNet_spec (j : Finset H × ℕ) :
    ‖starHomNet φ T hT hsT hnT j‖ ≤ 1 ∧
      ∀ x∈j.1,‖φ (starHomNet φ T hT hsT hnT j) x-T x‖<(j.2+1:ℝ)⁻¹ :=
  (starHom_net_approx_exists φ T hT hsT hnT j).choose_spec

end Kadison.Kaplansky

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

def vectorCLM : A →L[ℂ] τ.GNS :=
  (algebraVector τ).mkContinuous ‖vacuum τ‖ (fun a => by
    rw [algebraVector_apply,←left_vacuum]
    exact ((τ.gnsStarAlgHom a).le_opNorm _).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom a)
        (norm_nonneg _)))

end Kadison.TracialSequence

end

end
end

end OAI
end


