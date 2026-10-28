-- Prove2me | Definitions.Def_OAIQ039C055
-- name    : OAIQ039C055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:29:36.742296+00:00
-- url     : https://prove2.me/theorems/2a03c91b-fc47-404f-b582-d0faeb09cab1
-- title:
--   Definitions bundle OAIQ039C055 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 32 declarations of OpenAI's Lean: 13 definitions and 19 theorems. The definitions and types are `OAI.Kadison.FreeBlocks.ambientOperators`, `OAI.Kadison.FreeBlocks.baseAction`, `OAI.Kadison.FreeBlocks.baseEmbedding`, `OAI.Kadison.FreeBlocks.baseSpace`, `OAI.Kadison.FreeBlocks.dihedralColumn`, `OAI.Kadison.FreeBlocks.factorOperators`, `OAI.Kadison.FreeBlocks.repeatInsertion`, `OAI.Kadison.FreeBlocks.repeatPre`, `OAI.Kadison.FreeBlocks.repeatPreIsometry`, `OAI.Kadison.FreeBlocks.repeatedParams`, `OAI.Kadison.FreeWordAction.action`, `OAI.Kadison.FreeWordAction.equiv`, `OAI.Kadison.FreeWordAction.representation`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FreeAction`, `Commutator_FreeActionCovariance`, `Commutator_FreeActionGroup`, `Commutator_FreeActionUnitary`, `Commutator_FreeHilbertEntries`, `Commutator_FreeRepeatedWords`, `Commutator_FreeSymmetrization`, `Commutator_FreeWordDecomposition`, `Commutator_KaplanskyFull`.
--
--   **Imports.** It imports the bundles `OAIQ039C043`, `OAIQ039C045`, `OAIQ039C046` and `OAIQ039C047` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C059`, `OAIQ039C060`, `OAIQ039C063`, `OAIQ039C064` and `OAIQ039C065`; the statements `OAI.Kadison.FreeBlocks.normal_free_corner_bound` and `OAI.Kadison.FreeBlocks.normal_free_original_bound`; the proof of `OAI.Kadison.FreeBlocks.normal_free_original_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C043
import Definitions.Def_OAIQ039C045
import Definitions.Def_OAIQ039C046
import Definitions.Def_OAIQ039C047

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

lemma generated_mem_span {a : A} (ha : a ∈ iSup S) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ hilbertWordSpan t S hfree := by
  have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
    change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
    rw [FreeMoments.reducedAlgebra_eq_iSup]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, hw, rfl⟩ := ha
    exact bounded_word_mem t S hfree w hw
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using
      (hilbertWordSpan t S hfree).add_mem ha hb
  | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using
      (hilbertWordSpan t S hfree).smul_mem c ha

lemma total_words_from_generation
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    (hilbertWordSpan t S hfree).topologicalClosure = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using Completion.induction_on with
  | hp => exact (hilbertWordSpan t S hfree).isClosed_topologicalClosure
  | ih x =>
    let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
    have h := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
      (hgen (t.functional.ofPreGNS x)) ξ
    have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS x) ξ =
        (x : t.functional.GNS) := by
      simp [ξ, PositiveLinearMap.gnsStarAlgHom]
    rw [heq] at h
    apply Submodule.topologicalClosure_mono ?_ h
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := ha
    simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using generated_mem_span t S hfree hb

theorem isHilbertSum_of_generation
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    IsHilbertSum ℂ (wordSpace t S) (wordInclusion t S hfree) := by
  apply IsHilbertSum.mk (wordFamily_orthogonal t S hfree)
  change ⊤ ≤ (hilbertWordSpan t S hfree).topologicalClosure
  rw [total_words_from_generation t S hfree hgen]

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

lemma tensorIso_pure : ∀ is (x : Params t S is),
    tensorIso t S α hmem hτ is (pure t S is x)=pure t S is (mapParams t S α hmem hτ is x)
  | [], _ => rfl
  | i::is,x => by
      change (letterIso t S α hmem hτ i x.1) ⊗ₜ[ℂ]
        (tensorIso t S α hmem hτ is (pure t S is x.2)) = _
      rw [tensorIso_pure is x.2]
      rfl

lemma mapParams_letters : ∀ is (x : Params t S is),
    letters t S is (mapParams t S α hmem hτ is x)=
      (letters t S is x).map (letter t S α hmem hτ)
  | [], _ => rfl
  | i::is,x => by
      change asLetter t S i (letterIso t S α hmem hτ i x.1) :: _ = _ :: _
      congr 1
      exact mapParams_letters is x.2

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

def action : t.functional.GNS →ₗᵢ[ℂ] t.functional.GNS :=
  HilbertDiagonal.onSum (wordSpace t S) (wordInclusion t S hfree)
    (isHilbertSum_of_generation t S hfree hgen)
    (fun is => completionIsometry (tensorIso t S α hmem hτ is.val))

lemma action_word (w : List (Letter S t.functional.toLinearMap)) (hw : Reduced w) :
    action t S α hmem hτ hfree hgen (t.functional.toPreGNS (word w) : t.functional.GNS) =
      (t.functional.toPreGNS (word (w.map (letter t S α hmem hτ))) : t.functional.GNS) := by
  let is : ColorSeq ι := ⟨w.map Letter.color,(List.isChain_map _).mpr hw⟩
  have hv : (t.functional.toPreGNS (word w) : t.functional.GNS)=
      wordInclusion t S hfree is (pure t S is.val (paramsOfLetters t S w) : wordSpace t S is) := by
    change _=wordEmbedding t S hfree is.val is.property _
    rw [wordEmbedding_coe,readPre_pure]
    simp only [is,letters_paramsOfLetters]
  rw [hv]
  unfold action
  rw [HilbertDiagonal.onSum_insert,completionIsometry_coe,tensorIso_pure]
  change wordEmbedding t S hfree is.val is.property _ = _
  rw [wordEmbedding_coe,readPre_pure,mapParams_letters]
  simp only [is,letters_paramsOfLetters]

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionCovariance
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

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

include hfree hgen in
lemma ext_reduced {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F G : t.functional.GNS →L[ℂ] E)
    (hw : ∀ w : List (Letter S t.functional.toLinearMap), Reduced w →
      F (TracialGNS.algebraVector t.functional (word w))=
      G (TracialGNS.algebraVector t.functional (word w))) : F=G := by
  apply ActualHilbertSum.map_ext (wordSpace t S) (wordInclusion t S hfree)
    (isHilbertSum_of_generation t S hfree hgen)
  intro is
  ext x
  change F (wordEmbedding t S hfree is.val is.property x) = G (wordEmbedding t S hfree is.val is.property x)
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    simp only [wordEmbedding_coe]
    have hs : x∈Submodule.span ℂ (Set.range (pure t S is.val)) := by rw [span_pure]; trivial
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p,rfl⟩ := hy
      rw [readPre_pure]
      exact hw _ (letters_reduced t S is.val p is.property)
    | zero => simp [Completion.coe_zero]
    | add x y _ _ hx hy => simp only [map_add, Completion.coe_add] at *; exact congrArg₂ (·+·) hx hy
    | smul c x _ hx => simp only [map_smul, Completion.coe_smul] at *; exact congrArg (c • ·) hx

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionGroup
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

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable {G : Type*} [Monoid G] (α : G → ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ g i a, a∈S i → α g i a∈S i)
  (hτ : ∀ g i a, t.functional (α g i a)=t.functional a)

lemma action_one (h1 : ∀ i a, α 1 i a=a) :
    action t S (α 1) (hmem 1) (hτ 1) hfree hgen=LinearIsometry.id := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply ext_reduced t S hfree hgen
  intro w hw
  change action t S (α 1) (hmem 1) (hτ 1) hfree hgen
    (TracialGNS.algebraVector t.functional (word w))=TracialGNS.algebraVector t.functional (word w)
  simp only [TracialGNS.algebraVector_apply]
  rw [action_word t S _ _ _ hfree hgen w hw]
  congr 2
  simp only [word,List.map_map,Function.comp_def,letter_val,h1]

lemma action_mul (hmul : ∀ g h i a, α (g*h) i a=α g i (α h i a)) (g h : G) :
    action t S (α (g*h)) (hmem (g*h)) (hτ (g*h)) hfree hgen=
      (action t S (α g) (hmem g) (hτ g) hfree hgen).comp
        (action t S (α h) (hmem h) (hτ h) hfree hgen) := by
  apply LinearIsometry.toContinuousLinearMap_injective
  apply ext_reduced t S hfree hgen
  intro w hw
  change action t S (α (g*h)) (hmem (g*h)) (hτ (g*h)) hfree hgen
    (TracialGNS.algebraVector t.functional (word w))=
      action t S (α g) (hmem g) (hτ g) hfree hgen
        (action t S (α h) (hmem h) (hτ h) hfree hgen
          (TracialGNS.algebraVector t.functional (word w)))
  simp only [TracialGNS.algebraVector_apply]
  rw [action_word t S _ _ _ hfree hgen w hw,action_word t S _ _ _ hfree hgen w hw,
    action_word t S _ _ _ hfree hgen _ (reduced_map t S _ _ _ hw)]
  congr 2
  simp only [word,List.map_map,Function.comp_def,letter_val,letter_color,hmul]

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActionUnitary
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

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable {G : Type*} [Group G] (α : G → ι → A ≃⋆ₐ[ℂ] A)
  (hmem : ∀ g i a, a∈S i → α g i a∈S i)
  (hτ : ∀ g i a, t.functional (α g i a)=t.functional a)
  (h1 : ∀ i a, α 1 i a=a)
  (hmul : ∀ g h i a, α (g*h) i a=α g i (α h i a))

include h1 hmul in
lemma action_inv (g : G) (x : t.functional.GNS) :
    action t S (α g⁻¹) (hmem g⁻¹) (hτ g⁻¹) hfree hgen
      (action t S (α g) (hmem g) (hτ g) hfree hgen x)=x := by
  have h := congrArg (fun T : t.functional.GNS →ₗᵢ[ℂ] t.functional.GNS => T x)
    (action_mul t S hfree hgen α hmem hτ hmul g⁻¹ g)
  rw [inv_mul_cancel,action_one t S hfree hgen α hmem hτ h1] at h
  exact h.symm

def equiv (g : G) : t.functional.GNS ≃ₗᵢ[ℂ] t.functional.GNS where
  toLinearEquiv :=
    { (action t S (α g) (hmem g) (hτ g) hfree hgen).toLinearMap with
      invFun := action t S (α g⁻¹) (hmem g⁻¹) (hτ g⁻¹) hfree hgen
      left_inv := action_inv t S hfree hgen α hmem hτ h1 hmul g
      right_inv := by
        intro x
        change action t S (α g) (hmem g) (hτ g) hfree hgen
          (action t S (α g⁻¹) (hmem g⁻¹) (hτ g⁻¹) hfree hgen x)=x
        simpa only [inv_inv] using action_inv t S hfree hgen α hmem hτ h1 hmul g⁻¹ x }
  norm_map' := (action t S (α g) (hmem g) (hτ g) hfree hgen).norm_map

@[simp] lemma equiv_apply (g : G) (x : t.functional.GNS) :
    equiv t S hfree hgen α hmem hτ h1 hmul g x=
      action t S (α g) (hmem g) (hτ g) hfree hgen x := rfl

def representation : G →* (t.functional.GNS ≃ₗᵢ[ℂ] t.functional.GNS) where
  toFun := equiv t S hfree hgen α hmem hτ h1 hmul
  map_one' := by
    ext x
    change action t S (α 1) (hmem 1) (hτ 1) hfree hgen x=x
    rw [action_one t S hfree hgen α hmem hτ h1]
    rfl
  map_mul' g h := by
    ext x
    change action t S (α (g*h)) (hmem (g*h)) (hτ (g*h)) hfree hgen x=
      action t S (α g) (hmem g) (hτ g) hfree hgen
        (action t S (α h) (hmem h) (hτ h) hfree hgen x)
    rw [action_mul t S hfree hgen α hmem hτ hmul]
    rfl

@[simp] lemma representation_apply (g : G) (x : t.functional.GNS) :
    representation t S hfree hgen α hmem hτ h1 hmul g x=
      action t S (α g) (hmem g) (hτ g) hfree hgen x := rfl

end Kadison.FreeWordAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeHilbertEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

abbrev baseEmbedding : multiplicityLevel t S true 0 →ₗᵢ[ℂ] t.functional.GNS :=
  blockEmbedding t S hfree Bool.false_ne_true 0

def baseAction (a : A) : multiplicityLevel t S true 0 →L[ℂ] multiplicityLevel t S true 0 :=
  (ContinuousLinearMap.adjoint (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
    (baseEmbedding t S hfree).toContinuousLinearMap).comp
    ((t.functional.gnsStarAlgHom a).comp (baseEmbedding t S hfree).toContinuousLinearMap)

def dihedralColumn (e : A) (w : unitary A) (c : ℝ) (n : ℕ) :
    multiplicityLevel t S true 0 →L[ℂ] t.functional.GNS :=
  (c:ℂ) • ((t.functional.gnsStarAlgHom (e*DihedralCorner.wave w (-(n:ℤ)))).comp
    (baseEmbedding t S hfree).toContinuousLinearMap)

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeRepeatedWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι}

def repeatedParams (s : letterSpace t S j) (x : letterSpace t S i)
    (v : factorSpace t S j) : ∀ n, BlockParams t S i j n
  | 0 => v
  | n+1 => ((s,x),repeatedParams s x v n)

@[simp] lemma repeatedParams_D (s : letterSpace t S j) (x : letterSpace t S i)
    (v : factorSpace t S j) (n : ℕ) :
    paramD t S n (repeatedParams t S s x v n)=fun _ => x := by
  induction n with
  | zero => funext k; exact Fin.elim0 k
  | succ n ih =>
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · exact congrFun ih _

def repeatPre (s : letterSpace t S j) : ∀ n,
    factorSpace t S j →ₗ[ℂ] multiplicityTensor t S j n
  | 0 => LinearMap.id
  | n+1 => (TensorProduct.mk ℂ (letterSpace t S j) (multiplicityTensor t S j n) s).comp
      (repeatPre s n)

@[simp] lemma repeatedParams_J (s : letterSpace t S j) (x : letterSpace t S i)
    (v : factorSpace t S j) (n : ℕ) :
    paramJ t S n (repeatedParams t S s x v n)=repeatPre t S s n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change s ⊗ₜ[ℂ] paramJ t S n (repeatedParams t S s x v n)=
      s ⊗ₜ[ℂ] repeatPre t S s n v
    rw [ih]

lemma norm_repeatPre (s : letterSpace t S j) (n : ℕ) (v : factorSpace t S j) :
    ‖repeatPre t S s n v‖=‖s‖^n*‖v‖ := by
  induction n with
  | zero => simp [repeatPre]
  | succ n ih =>
    change ‖s ⊗ₜ[ℂ] repeatPre t S s n v‖=_
    rw [TensorProduct.norm_tmul,ih,pow_succ']
    exact (mul_assoc _ _ _).symm

def repeatPreIsometry (s : letterSpace t S j) (hs : ‖s‖=1) (n : ℕ) :
    factorSpace t S j →ₗᵢ[ℂ] multiplicityTensor t S j n where
  toLinearMap := repeatPre t S s n
  norm_map' v := by rw [norm_repeatPre,hs,one_pow,one_mul]

def repeatInsertion (s : letterSpace t S j) (hs : ‖s‖=1) (n : ℕ) :
    multiplicityLevel t S j 0 →ₗᵢ[ℂ] multiplicityLevel t S j n :=
  HilbertCompletion.map (repeatPreIsometry t S s hs n)

@[simp] lemma repeatInsertion_coe (s : letterSpace t S j) (hs : ‖s‖=1)
    (n : ℕ) (v : factorSpace t S j) :
    repeatInsertion t S s hs n (v : multiplicityLevel t S j 0)=
      (repeatPre t S s n v : multiplicityLevel t S j n) := by
  exact HilbertCompletion.map_coe (repeatPreIsometry t S s hs n) v

@[simp] lemma blockRead_repeated (s : letterSpace t S j) (x : letterSpace t S i)
    (n : ℕ) (v : factorSpace t S j) :
    blockRead t S n (blockPure t S n (repeatedParams t S s x v n))=
      (letterValue t S j s*letterValue t S i x)^n*factorValue t S j v := by
  induction n with
  | zero => simp [repeatedParams,blockPure,blockRead]
  | succ n ih =>
    change letterValue t S j s*(letterValue t S i x*
      blockRead t S n (blockPure t S n (repeatedParams t S s x v n)))=_
    rw [ih,pow_succ']
    simp only [mul_assoc]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetrization
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

abbrev factorOperators : StarSubalgebra ℂ (t.functional.GNS →L[ℂ] t.functional.GNS) :=
  (t.functional.gnsStarAlgHom.comp f).range

def ambientOperators : StarSubalgebra ℂ (t.functional.GNS →L[ℂ] t.functional.GNS) :=
  StarSubalgebra.centralizer ℂ ↑(StarSubalgebra.centralizer ℂ (generatedOperators t S : Set (t.functional.GNS →L[ℂ] t.functional.GNS)))

lemma mem_ambientOperators {a : t.functional.GNS →L[ℂ] t.functional.GNS} :
    a∈ambientOperators t S ↔ a ∈ Set.centralizer (Set.centralizer (generatedOperators t S : Set _)) := by
  change a ∈ (ambientOperators t S : Set _) ↔ _
  rw [ambientOperators,StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]

abbrev baseSpace : Submodule ℂ t.functional.GNS :=
  cyclicSubspace ((S j).map t.functional.gnsStarAlgHom) (TracialGNS.vacuum t.functional)

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_KaplanskyFull
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

namespace Kadison.Kaplansky

open OperatorAmplification

attribute [local instance] OAI.Kadison.Kaplansky.instDecidableEqFinOfNatNat_solutions
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem contraction_finite_approx
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ ‖a‖≤1 ∧ ∀ i, ‖a (x i)-T (x i)‖<ε := by
  let : IsClosed (S : Set (H →L[ℂ] H)) := hS
  obtain ⟨A,hA,_,hnA,he⟩ := selfAdjoint_contraction_finite_approx ι
    (fullMatrixAlgebra (Fin 2) S) (fullMatrixAlgebra_closed (Fin 2) S)
    (offDiagonal_bicommutant S hT) (offDiagonal_selfAdjoint T) (offDiagonal_norm_le hnT)
    (fun i => single (Fin 2) 1 (x i)) ε hε
  refine ⟨entry (Fin 2) A 0 1,(mem_fullMatrixAlgebra_iff (Fin 2) S A).mp hA 0 1,
    (entry_norm_le A 0 1).trans hnA,?_⟩
  intro i
  have h := (PiLp.norm_apply_le
    (A (single (Fin 2) 1 (x i))-offDiagonal T (single (Fin 2) 1 (x i))) 0).trans_lt (he i)
  simpa only [entry_apply,PiLp.sub_apply,offDiagonal_zero,single_apply,ite_true] using h

end Kadison.Kaplansky

end

end
end

end OAI
end


