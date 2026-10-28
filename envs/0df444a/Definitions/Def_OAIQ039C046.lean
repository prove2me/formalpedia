-- Prove2me | Definitions.Def_OAIQ039C046
-- name    : OAIQ039C046
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:26:05.607913+00:00
-- url     : https://prove2.me/theorems/bd5e9ac0-3419-41e3-acd0-e0e8af76a47f
-- title:
--   Definitions bundle OAIQ039C046 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 8 definitions, 1 instance and 15 theorems. The definitions and types are `OAI.Kadison.FinitePatching.PartialUnitary.toLink`, `OAI.Kadison.FreeBlocks.factorBounded`, `OAI.Kadison.FreeBlocks.factorTrace`, `OAI.Kadison.FreeWordAction.letterIso`, `OAI.Kadison.FreeWordAction.letterLinear`, `OAI.Kadison.FreeWordAction.mapParams`, `OAI.Kadison.FreeWordAction.tensorIso`, `OAI.Kadison.FreeWordTensor.hilbertWordSpan`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FactorComparison`, `Commutator_FactorCorner`, `Commutator_FiniteFactorComparison`, `Commutator_FreeAction`, `Commutator_FreeCovariance`, `Commutator_FreeSymmetry14`, `Commutator_FreeWordDecomposition`, `Commutator_FreeWordTensor`, `Commutator_HankelAlgebra`, `Commutator_MatrixAlgebraDensity`, `Commutator_PartialIsometryMaximal`, `Commutator_PartialUnitaryChain`, `Commutator_PartialUnitaryOrder`, `Commutator_Regroup`.
--
--   **Imports.** It imports the bundles `OAIQ039C033`, `OAIQ039C034`, `OAIQ039C035`, `OAIQ039C036` and `OAIQ039C037` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C055`, `OAIQ039C056` and `OAIQ039C058`; the statements `OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership` and `OAI.Kadison.FreeBlocks.norm_base_mul`; the proofs of `OAI.Kadison.AtomicFactor.exists_decomposition`, `OAI.Kadison.FinitePatching.PartialUnitary.chain_upper_with_L2_and_membership`, `OAI.Kadison.FinitePatching.Words.momentBound_completed`, `OAI.Kadison.MatrixDiffuse.noMinimal_of_matrix_stages`, `OAI.Kadison.PartialIsometryOrder.EqualPartition.rank_add_le_card` and `OAI.Kadison.PartialIsometryOrder.exists_partialDecomposition`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C033
import Definitions.Def_OAIQ039C034
import Definitions.Def_OAIQ039C035
import Definitions.Def_OAIQ039C036
import Definitions.Def_OAIQ039C037

section
-- module Solutions.OAIQ039_CM.Commutator_FactorCorner
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FactorCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_linking_partialIsometry (M : VonNeumannAlgebra H) (hf : IsFactor M)
    {e f : H →L[ℂ] H} (he : e∈M) (hfM : f∈M)
    (hpe : IsStarProjection e) (hpf : IsStarProjection f) (hne : e≠0) (hnf : f≠0) :
    ∃ v∈M, v≠0 ∧ v*star v*v=v ∧ star v*v≤e ∧ v*star v≤f := by
  obtain ⟨a,ha,hna⟩ := exists_nonzero_corner M hf he hne hnf
  let x := f*a*e
  have hx : x∈M := M.mul_mem (M.mul_mem hfM ha) he
  have hfx : f*x=x := by dsimp only [x]; rw [←mul_assoc,←mul_assoc,hpf.isIdempotentElem.eq]
  have hxe : x*e=x := by dsimp only [x]; rw [mul_assoc,hpe.isIdempotentElem.eq]
  refine ⟨Polar.partialIsometry x,Polar.partialIsometry_mem_vonNeumann M hx,?_,
    Polar.partialIsometry_triple x,?_,?_⟩
  · intro hzero
    apply hna
    have hfact := Polar.factorization x
    rw [hzero,zero_mul] at hfact
    exact hfact.symm
  · rw [Polar.partialIsometry_initial]
    exact Polar.rightSupport_le x e hpe hxe
  · exact Polar.leftSupport_le x f hpf hfx

end Kadison.FactorCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialIsometryMaximal
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) {e f : H →L[ℂ] H}

variable (he : IsStarProjection e) (hf : IsStarProjection f)

include he hf

theorem chain_has_upper (c : Set (Link M e f)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    BddAbove c := by
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  let ω : Ultrafilter c := Ultrafilter.of atTop
  have hω : (ω : Filter c)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨W,hnW,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω (fun v : c => v.val.val)
    1 zero_le_one (fun v => v.val.norm_le_one)
  have hWM : W∈M := WeakOperatorLimit.mem_vonNeumann hlim M
    (Filter.Eventually.of_forall fun v => v.val.mem)
  have hWe : W*e=W := by
    have h := WeakOperatorLimit.intertwine hlim e 1 (Filter.Eventually.of_forall
      fun v => by simpa only [one_mul] using v.val.mul_source he)
    simpa only [one_mul] using h
  have hfW : f*W=W := by
    have h := WeakOperatorLimit.intertwine hlim 1 f (Filter.Eventually.of_forall
      fun v => by simpa only [mul_one] using (v.val.target_mul hf).symm)
    simpa only [mul_one] using h.symm
  let u : Link M e f :=
    { val := Polar.partialIsometry W
      mem := Polar.partialIsometry_mem_vonNeumann M hWM
      triple := Polar.partialIsometry_triple W
      source_le := by rw [Polar.partialIsometry_initial]; exact Polar.rightSupport_le W e he hWe
      target_le := Polar.leftSupport_le W f hf hfW }
  refine ⟨u,?_⟩
  intro v hv
  have hev : ∀ᶠ w : c in (ω : Filter c), v≤w.val :=
    (Filter.eventually_ge_atTop (⟨v,hv⟩ : c)).filter_mono hω
  have hWv : W*v.initial=v.val := WeakOperatorLimit.right_eq hlim v.initial v.val
    (hev.mono fun w hw => (Link.le_def v w.val).mp hw |>.2)
  have hExt := Polar.partialIsometry_extends hnW v.triple hWv
  apply (Link.le_def v u).mpr
  constructor
  · change v.initial ≤ star (Polar.partialIsometry W)*Polar.partialIsometry W
    rw [Polar.partialIsometry_initial]
    exact hExt.2
  · exact hExt.1

theorem exists_maximal : ∃ v : Link M e f, IsMax v := by
  let v0 : Link M e f :=
    { val := 0
      mem := M.zero_mem
      triple := by simp
      source_le := by simpa using he.nonneg
      target_le := by simpa using hf.nonneg }
  let : Nonempty (Link M e f) := ⟨v0⟩
  exact zorn_le_nonempty (fun c hc hn => chain_has_upper M he hf c hc hn)

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorComparison
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem factor_comparison (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) :
    ∃ v : Link M e f, v.initial=e ∨ v.final=f := by
  obtain ⟨v,hv⟩ := exists_maximal M he hf
  refine ⟨v,?_⟩
  by_contra h
  have hresE : e-v.initial≠0 := fun hh => h (Or.inl (sub_eq_zero.mp hh).symm)
  have hresF : f-v.final≠0 := fun hh => h (Or.inr (sub_eq_zero.mp hh).symm)
  have hmemE : e-v.initial∈M := M.sub_mem heM (M.mul_mem (M.star_mem' v.mem) v.mem)
  have hmemF : f-v.final∈M := M.sub_mem hfM (M.mul_mem v.mem (M.star_mem' v.mem))
  obtain ⟨w,hwM,hwn,hwt,hwi,hwf⟩ := FactorCorner.exists_linking_partialIsometry M hM
    hmemE hmemF (v.residual_source_projection he) (v.residual_target_projection hf) hresE hresF
  let w' : Link M (e-v.initial) (f-v.final) := ⟨w,hwM,hwt,hwi,hwf⟩
  have hvu := v.le_extend he hf w'
  have heq : v.extend he hf w'=v := le_antisymm (hv hvu) hvu
  have hval := congrArg Link.val heq
  change v.val+w=v.val at hval
  exact hwn (add_left_cancel (hval.trans (add_zero v.val).symm))

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorComparison
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_factor_comparison (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f)
    (hle : τ ⟨e,heM⟩≤τ ⟨f,hfM⟩) :
    ∃ v : Link M e f, v.initial=e := by
  obtain ⟨v,hv⟩ := factor_comparison M hM heM hfM he hf
  refine ⟨v,?_⟩
  rcases hv with hv|hv
  · exact hv
  · have htf : (⟨v.final,v.final_mem⟩ : M)=⟨f,hfM⟩ := Subtype.ext hv
    have hti : τ ⟨v.initial,v.initial_mem⟩=τ ⟨f,hfM⟩ := by
      rw [v.trace_initial_final τ hτ,htf]
    have hmem : e-v.initial∈M := M.sub_mem heM v.initial_mem
    have hnonneg : 0≤τ ⟨e-v.initial,hmem⟩ := τ.map_nonneg
      (show (0 : M)≤⟨e-v.initial,hmem⟩ from sub_nonneg.mpr v.source_le)
    have hzero : τ ⟨e-v.initial,hmem⟩=0 := by
      apply le_antisymm ?_ hnonneg
      change τ ((⟨e,heM⟩ : M)-⟨v.initial,v.initial_mem⟩)≤0
      rw [map_sub,hti]
      exact sub_nonpos.mpr hle
    exact (sub_eq_zero.mp (faithful_projection M τ hfaith hmem
      (v.residual_source_projection he) hzero)).symm

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeWordTensor
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A)

attribute [instance] Space.normed Space.inner

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

include hfree

lemma wordFamily_orthogonal :
    OrthogonalFamily ℂ (wordSpace t S) (wordInclusion t S hfree) := by
  intro is js hne x y
  exact wordEmbedding_orthogonal t S hfree is.val js.val is.property js.property
    (fun h => hne (Subtype.ext h)) x y

end Kadison.FreeWordTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeWordDecomposition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

namespace Kadison.FreeWordTensor

open scoped InnerProductSpace _root_.Topology

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

noncomputable def hilbertWordSpan : Submodule ℂ t.functional.GNS :=
  ⨆ is : ColorSeq ι, LinearMap.range (wordInclusion t S hfree is).toLinearMap

lemma bounded_word_mem (w : List (FreeMoments.Letter S t.functional.toLinearMap))
    (hw : FreeMoments.Reduced w) :
    (t.functional.toPreGNS (FreeMoments.word w) : t.functional.GNS) ∈
      hilbertWordSpan t S hfree := by
  let is : ColorSeq ι := ⟨w.map FreeMoments.Letter.color, (List.isChain_map _).mpr hw⟩
  apply Submodule.mem_iSup_of_mem is
  use (pure t S is.val (paramsOfLetters t S w) : wordSpace t S is)
  change wordEmbedding t S hfree is.val is.property _ = _
  rw [wordEmbedding_coe, readPre_pure]
  simp only [is, letters_paramsOfLetters]

end Kadison.FreeWordTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeAction
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (α : ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ i a, a∈S i → α i a∈S i)
  (hτ : ∀ i a, t.functional (α i a)=t.functional a)

lemma reduced_map {w : List (Letter S t.functional.toLinearMap)} (hw : Reduced w) :
    Reduced (w.map (letter t S α hmem hτ)) := (List.isChain_map _).mpr hw

def letterLinear (i : ι) : letterSpace t S i →ₗ[ℂ] letterSpace t S i where
  toFun x := ⟨t.functional.toPreGNS (α i (letterValue t S i x)),
    hmem _ _ x.property.1, by exact (hτ _ _).trans x.property.2⟩
  map_add' x y := by apply Subtype.ext; simp [map_add]
  map_smul' c x := by apply Subtype.ext; simp [map_smul]

lemma letterLinear_value (i : ι) (x : letterSpace t S i) :
    letterValue t S i (letterLinear t S α hmem hτ i x)=α i (letterValue t S i x) := rfl

lemma letterLinear_inner (i : ι) (x y : letterSpace t S i) :
    inner ℂ (letterLinear t S α hmem hτ i x) (letterLinear t S α hmem hτ i y)=inner ℂ x y := by
  rw [inner_letter,inner_letter,letterLinear_value,letterLinear_value,←map_star,←map_mul,hτ]

def letterIso (i : ι) : letterSpace t S i →ₗᵢ[ℂ] letterSpace t S i where
  toLinearMap := letterLinear t S α hmem hτ i
  norm_map' x := by
    rw [norm_eq_sqrt_re_inner (𝕜:=ℂ),norm_eq_sqrt_re_inner (𝕜:=ℂ),
      letterLinear_inner]

def tensorIso : ∀ is : List ι, tensor t S is →ₗᵢ[ℂ] tensor t S is
  | [] => LinearIsometry.id
  | i::is => TensorProduct.mapIsometry (letterIso t S α hmem hτ i) (tensorIso is)

def mapParams : ∀ is, Params t S is → Params t S is
  | [], _ => PUnit.unit
  | i::is, x => (letterIso t S α hmem hτ i x.1,mapParams is x.2)

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_Regroup
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

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped TensorProduct InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

@[simp] lemma levelShuffle_pure (n : ℕ) (a : aLetters t S i) (x : BlockParams t S i j n) :
    levelShuffle t S n ((HilbertCompletion.coeIsometry (endpointTensor t S i j n)) (a ⊗ₜ[ℂ] blockPure t S n x)) =
      ((((a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) : scalarLevel t S i n) ⊗ₜ[ℂ]
        (paramJ t S n x : multiplicityLevel t S j n)) : Completion (scalarLevel t S i n ⊗[ℂ] multiplicityLevel t S j n)) := by
  let y : endpointTensor t S i j n := a ⊗ₜ[ℂ] blockPure t S n x
  change HilbertCompletion.tensor ((HilbertCompletion.congr (endpointShuffle t S n)) (y : Completion (endpointTensor t S i j n))) = _
  rw [HilbertCompletion.congr_coe]
  change HilbertCompletion.tensor ((endpointShuffle t S n (a ⊗ₜ[ℂ] blockPure t S n x)) : Completion ((aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n) ⊗[ℂ] multiplicityTensor t S j n)) = _
  have he : endpointShuffle t S n (a ⊗ₜ[ℂ] blockPure t S n x) =
      (a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) ⊗ₜ[ℂ] paramJ t S n x :=
    endpointShuffle_pure t S n (a : factorSpace t S i) x
  exact (congrArg (fun z : (aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n) ⊗[ℂ]
      multiplicityTensor t S j n => HilbertCompletion.tensor
        (E := aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n)
        (F := multiplicityTensor t S j n)
        (z : Completion ((aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n) ⊗[ℂ]
          multiplicityTensor t S j n))) he).trans
    (HilbertCompletion.tensor_coe_tmul
      (E := aLetters t S i ⊗[ℂ] PreHilbert.power (dLetters t S i) n)
      (F := multiplicityTensor t S j n)
      (a ⊗ₜ[ℂ] PreHilbert.pure (dLetters t S i) n (paramD t S n x)) (paramJ t S n x))

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry14
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

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

abbrev factorTrace := (pullbackState t f hf).functional

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCovariance
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
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap
open scoped InnerProductSpace ENNReal
open scoped ComplexOrder InnerProductSpace TensorProduct
open UniformSpace ContinuousLinearMap

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

def factorBounded (d : D) : factorSpace t S i :=
  factorPreMap t f hf S i hS ((pullbackState t f hf).functional.toPreGNS d)

@[simp] lemma factorBounded_value (d : D) :
    factorValue t S i (factorBounded t f hf S i hS d)=f d := rfl

@[simp] lemma factorBounded_GNS (d : D) :
    factorGNSIso t f hf S i hS
      (HilbertCompletion.coeIsometry (aLetters t S i) (factorBounded t f hf S i hS d)) =
      TracialGNS.algebraVector (factorTrace t f hf) d := by
  exact factorGNSIso_coe t f hf S i hS d

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

@[simp] lemma paired_append (s : Letter S τ) (v z : List (Letter S τ)) :
    paired s (v++z)=paired s v++paired s z := by simp [paired]

end Kadison.FreeMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixAlgebraDensity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.OperatorAmplification

open CyclicColumns CyclicSpatial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι]

attribute [local instance] OAI.Kadison.OperatorAmplification.matrixAlgebraDensityDecidableEq
variable (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]

attribute [local instance] OAI.Kadison.OperatorAmplification.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
attribute [local instance] OAI.Kadison.OperatorAmplification.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions
lemma fullMatrixAlgebra_closed : IsClosed (fullMatrixAlgebra ι S :
    Set (SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)) := by
  exact (NonUnitalStarAlgHom.isometry (matrixRepresentation (ι:=ι) S.subtype)
    (matrixRepresentation_injective S.subtype Subtype.val_injective)).isClosedEmbedding.isClosed_range

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryOrder
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance instPartialOrder : PartialOrder (PartialUnitary A) where
  le v w := v.support ≤ w.support ∧ w.val*v.support=v.val
  le_refl v := ⟨le_rfl,v.mul_support⟩
  le_trans v w u hvw hwu := by
    refine ⟨hvw.1.trans hwu.1,?_⟩
    have h := (v.projection.le_iff_mul_eq_right w.projection).mp hvw.1
    calc
      _=u.val*(w.support*v.support) := by rw [h]
      _=v.val := by rw [←mul_assoc,hwu.2,hvw.2]
  le_antisymm v w hvw hwv := by
    apply ext
    have h := le_antisymm hvw.1 hwv.1
    calc
      v.val=w.val*v.support := hvw.2.symm
      _=w.val := by rw [h,w.mul_support]

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryChain
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter ContinuousLinearMapWOT

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.FinitePatching

namespace PartialUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def toLink (v : PartialUnitary M) : PartialIsometryOrder.Link M 1 1 where
  val := v.val
  mem := v.val.property
  triple := congrArg Subtype.val (show v.val*star v.val*v.val=v.val by
    rw [v.mul_star,v.support_mul])
  source_le := by
    have he : star (v.val : H →L[ℂ] H)*(v.val : H →L[ℂ] H)=v.support :=
      congrArg Subtype.val v.star_mul
    rw [he]
    exact (v.projection.map M.toStarSubalgebra.subtype).le_one
  target_le := by
    have he : (v.val : H →L[ℂ] H)*star (v.val : H →L[ℂ] H)=v.support :=
      congrArg Subtype.val v.mul_star
    rw [he]
    exact (v.projection.map M.toStarSubalgebra.subtype).le_one

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end


