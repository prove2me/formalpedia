-- Prove2me | Definitions.Def_OAIQ115N022
-- name    : OAIQ115N022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:54:53.98298+00:00
-- url     : https://prove2.me/theorems/4bd95813-e94e-4361-a612-3975af7de253
-- title:
--   Definitions bundle OAIQ115N022 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 14 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N016`, `OAIQ115N029`, `OAIQ115N018`, `OAIQ115N019` and `OAIQ115N020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N025` and `OAIQ115N026`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N016
import Definitions.Def_OAIQ115N029
import Definitions.Def_OAIQ115N018
import Definitions.Def_OAIQ115N019
import Definitions.Def_OAIQ115N020

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.PeakingPairData.pairHNN_cstar _root_.OAI.NaimarkZFC.carOrder _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.constructionIndex_orderBot _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra Matrix

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem modelTrace_isState : IsState B.modelTrace :=
  ⟨atomicTrace_norm B.atoms B.amalgam, atomicTrace_square B.atoms B.amalgam⟩

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A) (τ : A →ₚ[ℂ] ℂ) (t : C →L[ℂ] ℂ)

theorem matrixCorner_trace_expectation
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a)
    (htrace : ∀ x, normalizedMatrixTrace τ (E x) = t x) (x : MatrixHNNCorner φ) :
    τ (matrixCornerExpectation φ E x) =
      cornerTrace (matrixCornerProjection φ) (matrixCornerProjection_isProjection φ) t 2 x := by
  have ht := htrace (x:C)
  rw [matrixCornerExpectation_supported φ E hleft hright,normalizedMatrixTrace_single] at ht
  change τ (matrixCornerExpectation φ E x) = (2:ℝ) • t (x:C)
  rw [← ht]
  simp only [Fintype.card_bool,Nat.cast_ofNat,smul_smul]
  norm_num

end

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem turnCenter_centered (i : Bool) (a : A) :
    (B.input false).expectation (!i) (B.turnCenter i a) = 0 := by
  unfold turnCenter
  rw [map_sub,(B.input false).fix,sub_self]

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

theorem hnn_generated :
    Dense (StarAlgebra.adjoin ℂ (Set.range B.hnnBase ∪ Set.range B.hnnLetter) : Set B.HNNAlgebra) :=
  B.corner_generated

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : PeakingPairData A} {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]
  (X : B.Endpoint ι) (Y : B.Endpoint κ)

theorem Endpoint.cross_decay (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i))
    (hne : ¬ UnitarilyEquivalent (pureGNS X.state X.pure) (pureGNS Y.state Y.pure)) :
    ∀ a ∈ bridgeWordSet B.embedBase B.modelLetter (fun a => B.expectation a = 0),
      Tendsto (fun k : ι × κ => B.embedBase (X.net k.1)*a*B.embedBase (Y.net k.2))
        atTop (𝓝 0) :=
  bridge_cross_decay B.embedBase B.modelLetter (fun a => B.expectation a = 0)
    X.state Y.state X.pure Y.pure X.net Y.net X.positive X.contractive
    Y.positive Y.contractive Y.antitone X.excision Y.excision hne
    (X.model_word_decay Y hs hex)

theorem Endpoint.disjoint_matrix_irrep (hs : B.Separated)
    (hex : ∀ i, X.tag = some i → Y.tag ≠ some (!i))
    (hne : ¬ UnitarilyEquivalent (pureGNS X.state X.pure) (pureGNS Y.state Y.pure))
    (hxval : ∀ k, X.state (X.net k) = 1) (hyval : ∀ k, Y.state (Y.net k) = 1)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : B.Model →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hcξ : ∀ a, ⟪ξ,π (B.embedBase a) ξ⟫_ℂ = X.state a)
    (hcη : ∀ a, ⟪η,π (B.embedBase a) η⟫_ℂ = Y.state a) : False := by
  let : (atTop : Filter (ι × κ)).NeBot := by
    rw [← prod_atTop_atTop_eq]
    infer_instance
  exact no_common_irrep_of_state_decay B.embedBase X.state Y.state
    (bridgeWordSet B.embedBase B.modelLetter (fun a => B.expectation a = 0)) B.model_words_dense
    (fun k : ι × κ => X.net k.1) (fun k : ι × κ => Y.net k.2)
    (fun k => IsSelfAdjoint.of_nonneg (X.positive k.1))
    (fun k => X.contractive k.1) (fun k => Y.contractive k.2)
    (fun k => hxval k.1) (fun k => hyval k.2)
    (X.cross_decay Y hs hex hne) π hπ ξ η hξ hη hcξ hcη

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem exists_endpoint_representative (hs : B.Separated)
    (f : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε) :
    ∃ (ι : Type) (_po : Preorder ι) (_dir : IsDirectedOrder ι) (_ne : Nonempty ι)
      (X : B.Endpoint ι),
      UnitarilyEquivalent (pureGNS X.state X.pure) (pureGNS f hf) ∧
        ∀ k, X.state (X.net k) = 1 := by
  classical
  by_cases he : ∃ i, UnitarilyEquivalent (pureGNS (B.matrixState i) (B.matrixPure i))
      (pureGNS f hf)
  · obtain ⟨i,hi⟩ := he
    refine ⟨ℕ,inferInstance,inferInstance,inferInstance,B.peakEndpoint hs i,hi,?_⟩
    exact (B.matrixPeaks i).2.2.2.1
  · have hne : ∀ i, ¬ UnitarilyEquivalent (pureGNS f hf)
        (pureGNS (B.matrixState i) (B.matrixPure i)) := by
      intro i hi
      exact he ⟨i,UnitarilyEquivalent.symm hi⟩
    exact ⟨B.pureIndex f hf,inferInstance,inferInstance,inferInstance,
      B.otherEndpoint f hf hsmall hne,UnitarilyEquivalent.refl _,
      B.otherEndpoint_value_one f hf hsmall hne⟩

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem matrix_no_unintended_join (hs : B.Separated)
    (f g : CStarMatrix Bool Bool A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hsmallf : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS f hf p ≠ 0 ∧ (B.matrixTrace p).re < ε)
    (hsmallg : ∀ ε : ℝ, 0 < ε → ∃ p : CStarMatrix Bool Bool A,
      IsStarProjection p ∧ pureGNS g hg p ≠ 0 ∧ (B.matrixTrace p).re < ε)
    (hne : ¬ UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (hex : ∀ i, ¬ (UnitarilyEquivalent (pureGNS f hf)
        (pureGNS (B.matrixState i) (B.matrixPure i)) ∧
      UnitarilyEquivalent (pureGNS g hg)
        (pureGNS (B.matrixState (!i)) (B.matrixPure (!i)))))
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : B.Model →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H)
    (hcξ : ∀ a, ⟪ξ,π (B.embedBase a) ξ⟫_ℂ = f a)
    (hcη : ∀ a, ⟪η,π (B.embedBase a) η⟫_ℂ = g a) : False := by
  obtain ⟨ι,poι,dι,nι,X,hX,hvalX⟩ := B.exists_endpoint_representative hs f hf hsmallf
  let : Preorder ι := poι
  let : IsDirectedOrder ι := dι
  let : Nonempty ι := nι
  obtain ⟨κ,poκ,dκ,nκ,Y,hY,hvalY⟩ := B.exists_endpoint_representative hs g hg hsmallg
  let : Preorder κ := poκ
  let : IsDirectedOrder κ := dκ
  let : Nonempty κ := nκ
  have hnXY : ¬ UnitarilyEquivalent (pureGNS X.state X.pure) (pureGNS Y.state Y.pure) := by
    intro h
    exact hne (hX.symm.trans (h.trans hY))
  have heXY : ∀ i, X.tag = some i → Y.tag ≠ some (!i) := by
    intro i hi hj
    have hXi : UnitarilyEquivalent (pureGNS X.state X.pure)
        (pureGNS (B.matrixState i) (B.matrixPure i)) := by
      exact pureGNS_equivalent_of_state_eq _ _ _ _ (X.matchedState i hi)
    have hYj : UnitarilyEquivalent (pureGNS Y.state Y.pure)
        (pureGNS (B.matrixState (!i)) (B.matrixPure (!i))) := by
      exact pureGNS_equivalent_of_state_eq _ _ _ _ (Y.matchedState (!i) hj)
    exact hex i ⟨hX.symm.trans hXi,hY.symm.trans hYj⟩
  obtain ⟨ξ',hξ',hcξ'⟩ := equivalent_pure_coefficient_vector B.embedBase f X.state hf X.pure
    hX.symm π ξ hcξ
  obtain ⟨η',hη',hcη'⟩ := equivalent_pure_coefficient_vector B.embedBase g Y.state hg Y.pure
    hY.symm π η hcη
  exact X.disjoint_matrix_irrep Y hs heXY hnXY hvalX hvalY π hπ ξ' η' hξ' hη' hcξ' hcη'

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

section
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem StateExtensionUnique.of_surjective (φ : A →⋆ₐ[ℂ] B)
    (hs : Function.Surjective φ) (f : A →L[ℂ] ℂ) : StateExtensionUnique φ f := by
  intro F G _ _ hF hG
  ext b
  obtain ⟨a,rfl⟩ := hs b
  exact (congrArg (fun h : A →L[ℂ] ℂ => h a) hF).trans
    (congrArg (fun h : A →L[ℂ] ℂ => h a) hG).symm

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem isPureState_restrict_equiv (e : A ≃⋆ₐ[ℂ] B)
    (f : B →L[ℂ] ℂ) (hf : IsPureState f) :
    IsPureState (restrictState e.toStarAlgHom f) := by
  have hr : restrictState e.symm.toStarAlgHom (restrictState e.toStarAlgHom f) = f := by
    ext b
    exact congrArg f (e.apply_symm_apply b)
  exact unique_lift_pure e.symm.toStarAlgHom f hf _
    (isState_restrict e.toStarAlgHom f hf.1) hr (fun g hg hgr =>
      StateExtensionUnique.of_surjective e.symm.toStarAlgHom e.symm.surjective f
        g _ hg (isState_restrict _ _ hf.1) hgr hr)

end

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} (B : ι → Type*) [∀ i, CStarAlgebra (B i)]
    [∀ i, PartialOrder (B i)] [∀ i, StarOrderedRing (B i)]

theorem pure_inequivalent_of_dense_restrictions
    (φ : ∀ i, B i →⋆ₐ[ℂ] A)
    (hd : Dense (⋃ i, Set.range (φ i)))
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hfr : ∀ i, IsPureState (restrictState (φ i) f))
    (hgr : ∀ i, IsPureState (restrictState (φ i) g))
    (hne : ∀ i, ¬ PureStateEquivalent _ (hfr i) _ (hgr i)) :
    ¬ PureStateEquivalent f hf g hg := by
  apply pure_extensions_inequivalent_of_no_common (StarAlgHom.id ℂ A) f g (g₁ := f) (g₂ := g)
      (hg₁ := hf) (hg₂ := hg) (hr₁ := rfl) (hr₂ := rfl)
  intro K _ _ _ π hπ ξ η hξ hη hcξ hcη
  let L : A →L[ℂ] ℂ := (innerSL ℂ ξ).comp (orbitCLM π η)
  have hL : L = 0 := by
    apply ContinuousLinearMap.ext
    intro a
    apply (closure_minimal ?_ (isClosed_eq L.continuous continuous_const)) (hd a)
    intro b hb
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
    obtain ⟨b,rfl⟩ := hi
    exact inequivalent_pure_mixed_zero _ _ (hfr i) (hgr i) (hne i)
      (π.comp (φ i).toNonUnitalStarAlgHom) ξ η hξ hη
      (fun b => hcξ (φ i b)) (fun b => hcη (φ i b)) b
  have hη0 : η ≠ 0 := norm_ne_zero_iff.mp (hη.trans_ne one_ne_zero)
  have hh : ⟪ξ,ξ⟫_ℂ = 0 :=
    (irreducible_vector_cyclic π hπ η hη0).induction_on
      (p := fun v => ⟪ξ,v⟫_ℂ = 0) ξ
      (isClosed_eq (innerSL ℂ ξ).continuous continuous_const)
      (fun a => congrArg (fun T : A →L[ℂ] ℂ => T a) hL)
  have hz : ξ = 0 := inner_self_eq_zero.mp hh
  simp only [hz,norm_zero,zero_ne_one] at hξ

end

open Topology
section
universe u v

theorem pure_inequivalent_ordinal_chain
    (A : Ordinal.{u} → Type v) [∀ i, CStarAlgebra (A i)]
    [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
    (incl : ∀ {i j : Ordinal.{u}}, i ≤ j → A i →⋆ₐ[ℂ] A j)
    (hcomp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
      (incl hjk).comp (incl hij) = incl (hij.trans hjk))
    (L i₀ : Ordinal.{u})
    (f g : ∀ i, A i →L[ℂ] ℂ) (hf : ∀ i, IsPureState (f i)) (hg : ∀ i, IsPureState (g i))
    (hfr : ∀ {i j} (h : i ≤ j), restrictState (incl h) (f j) = f i)
    (hgr : ∀ {i j} (h : i ≤ j), restrictState (incl h) (g j) = g i)
    (hinit : ¬ PureStateEquivalent (f i₀) (hf i₀) (g i₀) (hg i₀))
    (hnext : ∀ i < L, i₀ ≤ i →
      (¬ PureStateEquivalent (f i) (hf i) (g i) (hg i)) →
      ¬ PureStateEquivalent (f (i+1)) (hf (i+1)) (g (i+1)) (hg (i+1)))
    (hcont : ∀ j ≤ L, Order.IsSuccLimit j →
      Dense (⋃ k : {k : Ordinal.{u} // k < j}, Set.range (incl k.property.le)))
    (j : Ordinal.{u}) (hj : j ≤ L) (hij : i₀ ≤ j) :
    ¬ PureStateEquivalent (f j) (hf j) (g j) (hg j) := by
  induction j using Ordinal.limitRecOn with
  | zero =>
    have he : i₀ = 0 := le_antisymm hij bot_le
    subst i₀
    exact hinit
  | add_one j ih =>
    by_cases he : i₀ = j+1
    · subst i₀; exact hinit
    · have hi : i₀ ≤ j := by
        simpa only [Order.lt_add_one_iff] using (lt_of_le_of_ne hij he)
      exact hnext j ((lt_add_one j).trans_le hj) hi (ih (le_self_add.trans hj) hi)
  | limit j hjlim ih =>
    by_cases he : i₀ = j
    · subst i₀; exact hinit
    · have hi : i₀ < j := lt_of_le_of_ne hij he
      let J := {k : Ordinal.{u} // i₀ ≤ k ∧ k < j}
      have hd : Dense (⋃ k : J, Set.range (incl k.property.2.le)) := by
        apply (hcont j hj hjlim).mono
        intro a ha
        obtain ⟨k,b,rfl⟩ := Set.mem_iUnion.mp ha
        let m : J := ⟨max i₀ k.val,le_max_left _ _,max_lt hi k.property⟩
        apply Set.mem_iUnion.mpr
        refine ⟨m,incl (le_max_right i₀ k.val) b,?_⟩
        exact congrArg (fun φ : A k.val →⋆ₐ[ℂ] A j => φ b)
          (hcomp (le_max_right i₀ k.val) m.property.2.le)
      apply pure_inequivalent_of_dense_restrictions (fun k : J => A k.val)
        (fun k => incl k.property.2.le) hd (f j) (g j) (hf j) (hg j)
        (fun k => by rw [hfr]; exact hf k.val)
        (fun k => by rw [hgr]; exact hg k.val)
      intro k
      simpa only [hfr,hgr] using ih k.val k.property.2 (k.property.2.le.trans hj) k.property.1

end

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra InnerProductSpace

open Filter Topology
open scoped CStarAlgebra
section
namespace HNNWord
variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

theorem reduced_approximation (φ : A →⋆ₐ[ℂ] C) (v : Bool → C)
    (S : Set A) (hS : Dense S) (K : Bool → A → Prop)
    (center : Bool → A →L[ℂ] A)
    (hc : ∀ i a, K i (center i a))
    (hfix : ∀ i a, K i a → center i a = a)
    (hmem : ∀ i a, a ∈ S → center i a ∈ S)
    (w : HNNWord A) (hw : w.Reduced K) :
    ∃ u : ℕ → HNNWord A, (∀ n, (u n).first = w.first) ∧
      (∀ n, (u n).Reduced K) ∧ (∀ n, (u n).AllCoefficients S) ∧
      Tendsto (fun n => (u n).eval φ v) atTop (𝓝 (w.eval φ v)) := by
  induction w with
  | single i a =>
    obtain ⟨b,hb,ht⟩ := mem_closure_iff_seq_limit.mp (hS a)
    refine ⟨fun n => .single i (b n),fun _ => rfl,fun _ => trivial,hb,?_⟩
    exact tendsto_const_nhds.mul ((map_continuous φ).tendsto a |>.comp ht)
  | cons i a w ih =>
    obtain ⟨u,hu₁,hu₂,hu₃,hu₄⟩ := ih hw.2
    obtain ⟨b,hb,ht⟩ := mem_closure_iff_seq_limit.mp (hS a)
    by_cases hi : i = w.first
    · refine ⟨fun n => .cons i (b n) (u n),fun _ => rfl,
        fun n => ⟨Or.inl (hi.trans (hu₁ n).symm),hu₂ n⟩,
        fun n => ⟨hb n,hu₃ n⟩,?_⟩
      exact (tendsto_const_nhds.mul ((map_continuous φ).tendsto a |>.comp ht)).mul hu₄
    · have ha : K i a := hw.1.resolve_left hi
      refine ⟨fun n => .cons i (center i (b n)) (u n),fun _ => rfl,
        fun n => ⟨Or.inr (hc i (b n)),hu₂ n⟩,
        fun n => ⟨hmem i (b n) (hb n),hu₃ n⟩,?_⟩
      have ht' : Tendsto (fun n => center i (b n)) atTop (𝓝 a) := by
        simpa only [hfix i a ha,Function.comp_def] using (center i).continuous.tendsto a |>.comp ht
      exact (tendsto_const_nhds.mul ((map_continuous φ).tendsto a |>.comp ht')).mul hu₄
end HNNWord

end

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open Filter Topology
open scoped InnerProductSpace

open Topology

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Omission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
open scoped CStarAlgebra ComplexOrder

namespace HNNWord
variable {A D I : Type*}

theorem allCoefficients_one_stage (S : I → Set A)
    (hdir : Directed (· ⊆ ·) S) (w : HNNWord A)
    (hw : w.AllCoefficients (⋃ i, S i)) (a : A) (ha : a ∈ ⋃ i, S i) :
    ∃ i, w.AllCoefficients (S i) ∧ a ∈ S i := by
  induction w generalizing a with
  | single s b =>
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hw
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ha
    obtain ⟨k,hik,hjk⟩ := hdir i j
    exact ⟨k,hik hi,hjk hj⟩
  | cons s b w ih =>
    obtain ⟨i,hi,hbi⟩ := ih hw.2 b hw.1
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp ha
    obtain ⟨k,hik,hjk⟩ := hdir i j
    exact ⟨k,⟨hik hbi,hi.mono hik w⟩,hjk hj⟩

end HNNWord

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Cardinal Topology TopologicalSpace

open Cardinal Topology TopologicalSpace

end NaimarkZFC

end

end OAI
end


