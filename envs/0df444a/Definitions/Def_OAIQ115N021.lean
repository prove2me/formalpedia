-- Prove2me | Definitions.Def_OAIQ115N021
-- name    : OAIQ115N021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:45:38.356978+00:00
-- url     : https://prove2.me/theorems/ae9830a9-6f81-43b7-a819-94a9d161372f
-- title:
--   Definitions bundle OAIQ115N021 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 65 declarations of OpenAI's Lean: 18 definitions, 4 inductive types or structures and 43 theorems. The definitions and types are `OAI.NaimarkZFC.ChronologicalData`, `OAI.NaimarkZFC.ChronologicalData.advanceInactive`, `OAI.NaimarkZFC.ChronologicalData.algebra`, `OAI.NaimarkZFC.ChronologicalHistory`, `OAI.NaimarkZFC.ChronologicalStage`, `OAI.NaimarkZFC.ChronologicalStage.Hom`, `OAI.NaimarkZFC.ChronologicalStage.Hom.comp`, `OAI.NaimarkZFC.PeakingPairData.AmbientPresentation`, `OAI.NaimarkZFC.PeakingPairData.HNNAmbientPresentation`, `OAI.NaimarkZFC.PeakingPairData.PairDistinctOn`, `OAI.NaimarkZFC.PeakingPairData.hnnExpectation`, `OAI.NaimarkZFC.PeakingPairData.hnnTrace`, `OAI.NaimarkZFC.PeakingPairData.onSubalgebra`, `OAI.NaimarkZFC.PeakingPairData.pullback`, `OAI.NaimarkZFC.PeakingPairData.push`, `OAI.NaimarkZFC.PeakingPairData.pushedState`, `OAI.NaimarkZFC.PeakingPairData.traceCorner`, `OAI.NaimarkZFC.PeakingPairData.turnRemainderCLM`, `OAI.NaimarkZFC.TracialStage.Hom.comp`, `OAI.NaimarkZFC.TracialStage.Hom.id`, `OAI.NaimarkZFC.TracialStage.Hom.pushPair`, `OAI.NaimarkZFC.TracialStage.positiveTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Homogeneity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Homogeneity.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean), [`Naimark_Recursion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Recursion.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N029` and `OAIQ115N018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N025`, `OAIQ115N026` and `OAIQ115N027`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N029
import Definitions.Def_OAIQ115N018

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.constructionIndex_orderBot _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
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
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem modelExpectation_hnn_word (w : HNNWord A) (a : A)
    (hw : w.Reduced B.turnCentered) :
    B.modelExpectation ((B.cornerBase a*w.eval B.cornerBase B.cornerLetter : B.Corner) : B.Model) = 0 := by
  have hc := HNNWord.matrixCore_centered B.turnCentered
    (fun z => B.expectation z = 0) B.turn_matrix_centered w hw
  have hz := atomicExpectation_sandwich_core_zero B.atoms (by decide : false ≠ true)
    (fun i => matrixSingle i (!i) (1:SequenceDiagonal))
    (fun i => B.amalgam.centered true _ (B.letter_centered i))
    (fun z => B.expectation z = 0)
    (fun z hz => B.amalgam.centered false z hz) B.amalgam w.matrixCore hc
    (matrixSingle false false a*matrixSingle false w.first 1) w.matrixFinal
  change B.modelExpectation (B.embedBase (matrixSingle false false a)*
    (↑(w.eval B.cornerBase B.cornerLetter) : B.Model)) = 0
  rw [HNNWord.eval_matrix_core]
  unfold modelExpectation embedBase embedAux bridgeLetter
  simpa only [map_mul,mul_assoc] using hz

theorem expectCorner_hnn_word (w : HNNWord A) (a : A)
    (hw : w.Reduced B.turnCentered) :
    B.expectCorner (B.cornerBase a*w.eval B.cornerBase B.cornerLetter) = 0 := by
  change (B.modelExpectation
    ((B.cornerBase a*w.eval B.cornerBase B.cornerLetter : B.Corner) : B.Model)) false false = 0
  rw [B.modelExpectation_hnn_word w a hw]
  rfl

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem modelTrace_base (a : CStarMatrix Bool Bool A) :
    B.modelTrace (B.embedBase a) = normalizedMatrixTrace B.trace a := by
  exact atomicTrace_factor B.atoms B.amalgam false a

def traceCorner : B.Corner →L[ℂ] ℂ :=
  cornerTrace (matrixCornerProjection B.embedBase) (matrixCornerProjection_isProjection B.embedBase)
    B.modelTrace 2

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem cornerLetter_diagonal (i : Bool) (a : SequenceDiagonal) :
    B.cornerLetter i*B.cornerBase (B.diagonal (!i) a)*B.cornerLetter (!i) =
      B.cornerBase (B.diagonal i a) :=
  matrixCornerLetter_diagonal B.embedBase B.embedAux B.diagonal B.model_diagonal_agree i a

theorem cornerLetter_turn (i : Bool) (a : A) :
    B.cornerLetter i*B.cornerBase a*B.cornerLetter (!i) =
      B.cornerLetter i*B.cornerBase (B.turnCenter i a)*B.cornerLetter (!i) +
        B.cornerBase (B.turnRemainder i a) :=
  hnn_turn_split B.cornerBase.toRingHom (fun i => (B.diagonal i).toRingHom)
    B.cornerLetter (fun i => (B.input false).expectation i) B.cornerLetter_diagonal i a

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

def hnnTrace : B.HNNAlgebra →L[ℂ] ℂ := B.traceCorner
def hnnExpectation : B.HNNAlgebra →L[ℂ] A := B.expectCorner

theorem hnnLetter_star (i : Bool) : star (B.hnnLetter i) = B.hnnLetter (!i) :=
  B.cornerLetter_star i
theorem hnnLetter_turn (i : Bool) (a : A) :
    B.hnnLetter i*B.hnnBase a*B.hnnLetter (!i) =
      B.hnnLetter i*B.hnnBase (B.turnCenter i a)*B.hnnLetter (!i) + B.hnnBase (B.turnRemainder i a) :=
  B.cornerLetter_turn i a
theorem hnnExpectation_base (a : A) : B.hnnExpectation (B.hnnBase a) = a := B.expectCorner_base a
theorem hnnExpectation_word (u : HNNWord A) (a : A) (hu : u.Reduced B.turnCentered) :
    B.hnnExpectation (B.hnnBase a*u.eval B.hnnBase B.hnnLetter) = 0 := B.expectCorner_hnn_word u a hu

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

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
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem PureUEP.comp {φ : A →⋆ₐ[ℂ] B} {ψ : B →⋆ₐ[ℂ] C}
    (hφ : PureUEP φ) (hψ : PureUEP ψ) : PureUEP (ψ.comp φ) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  intro f hf F G hF hG hrF hrG
  let fB := restrictState ψ F
  have hfB : IsState fB := isState_restrict ψ F hF
  have hrB : restrictState φ fB = f := by
    change restrictState φ (restrictState ψ F) = f
    rw [restrictState_comp,hrF]
  have huni : ∀ g : B →L[ℂ] ℂ, IsState g → restrictState φ g = f → g = fB :=
    fun g hg hr => hφ f hf g fB hg hfB hr hrB
  have hpB : IsPureState fB := unique_lift_pure φ f hf fB hfB hrB huni
  have heq : restrictState ψ G = fB :=
    huni _ (isState_restrict ψ G hG) (by rw [restrictState_comp,hrG])
  exact hψ fB hpB F G hF hG rfl heq

theorem PureUEP.id : PureUEP (StarAlgHom.id ℂ A) := by
  intro f _ F G _ _ hF hG
  have hF' : F = f := by
    ext a
    exact congrArg (fun h : A →L[ℂ] ℂ => h a) hF
  have hG' : G = f := by
    ext a
    exact congrArg (fun h : A →L[ℂ] ℂ => h a) hG
  exact hF'.trans hG'.symm

end

open scoped CStarAlgebra ComplexOrder

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem StateExtensionUnique.postcomp_equiv
    {φ : A →⋆ₐ[ℂ] B} {f : A →L[ℂ] ℂ} (hu : StateExtensionUnique φ f)
    (e : B ≃⋆ₐ[ℂ] C) : StateExtensionUnique (e.toStarAlgHom.comp φ) f := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  intro F G hF hG hrF hrG
  have he := hu (restrictState e.toStarAlgHom F) (restrictState e.toStarAlgHom G)
    (isState_restrict _ _ hF) (isState_restrict _ _ hG)
    (by rw [restrictState_comp]; exact hrF) (by rw [restrictState_comp]; exact hrG)
  ext c
  obtain ⟨b,rfl⟩ := e.surjective c
  exact congrArg (fun h : B →L[ℂ] ℂ => h b) he

theorem PureUEP.postcomp_equiv {φ : A →⋆ₐ[ℂ] B}
    (hu : PureUEP φ) (e : B ≃⋆ₐ[ℂ] C) : PureUEP (e.toStarAlgHom.comp φ) :=
  fun f hf => (hu f hf).postcomp_equiv e

end

open Topology

open Topology
section

theorem BridgeSuccessor.properties {A C : Type} [CStarAlgebra A] [CStarAlgebra C]
    [PartialOrder A] [StarOrderedRing A] {φ : A →⋆ₐ[ℂ] C}
    (h : BridgeSuccessor φ) (hA : IsSimpleCStar A) :
    Function.Injective φ ∧ IsSimpleCStar C ∧ PureUEP φ := by
  cases h with
  | identity e he =>
    have hh : φ = e.toStarAlgHom := by ext a; exact (he a).symm
    rw [hh]
    refine ⟨e.injective,hA.of_equiv e,?_⟩
    simpa only [StarAlgHom.comp_id] using (PureUEP.id (A := A)).postcomp_equiv e
  | hnn B hs e he =>
    have hh : φ = e.toStarAlgHom.comp B.hnnBase := by ext a; exact (he a).symm
    rw [hh]
    exact ⟨e.injective.comp B.hnnBase_injective,(B.hnn_simple hs hA).of_equiv e,
      (show PureUEP B.hnnBase from fun f hf => B.hnn_unique hs hA f hf).postcomp_equiv e⟩

universe u
variable (A : Ordinal.{u} → Type) [∀ i, CStarAlgebra (A i)]
    [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
    (incl : ∀ {i j : Ordinal.{u}}, i ≤ j → A i →⋆ₐ[ℂ] A j)
    (L : Ordinal.{u})
    (hbase : IsSimpleCStar (A 0))
    (hnext : ∀ i < L, BridgeSuccessor (incl (show i ≤ i+1 by exact le_self_add)))
    (hi : ∀ {i j} (h : i ≤ j), Function.Injective (incl h))
    (hcont : ∀ j ≤ L, Order.IsSuccLimit j →
      Dense (⋃ k : {k : Ordinal.{u} // k < j}, Set.range (incl k.property.le)))

include hbase hnext hi hcont in

theorem bridge_ordinal_simple (j : Ordinal.{u}) (hj : j ≤ L) : IsSimpleCStar (A j) := by
  induction j using Ordinal.limitRecOn with
  | zero => exact hbase
  | add_one j ih =>
    have hjL : j < L := (lt_add_one j).trans_le hj
    exact ((hnext j hjL).properties (ih hjL.le)).2.1
  | limit j hjlim ih =>
    let J := {k : Ordinal.{u} // k < j}
    let : Nonempty J := ⟨⟨0,hjlim.ne_bot.bot_lt⟩⟩
    exact simple_of_dense_stage_ranges (fun k : J => A k.val)
      (fun k => ih k.val k.property (k.property.le.trans hj))
      (fun k => incl k.property.le)
      (fun k => NonUnitalStarAlgHom.isometry _ (hi k.property.le)) (hcont j hj hjlim)

end

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem Peaks.extend {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (φ : A →⋆ₐ[ℂ] C) (hu : StateExtensionUnique φ f)
    (F : C →L[ℂ] ℂ) (hF : IsState F) (hr : restrictState φ F = f) :
    Peaks (fun n => φ (p n)) F := by
  refine ⟨fun n => (hp.1 n).map φ, fun m n h => OrderHomClass.mono φ (hp.2.1 h),
    hF, ?_, ?_⟩
  · intro n
    change restrictState φ F (p n) = 1
    rw [hr]
    exact hp.2.2.2.1 n
  · intro G hG hGp
    have hGres : restrictState φ G = f := hp.2.2.2.2 _ (isState_restrict φ G hG) hGp
    exact hu G F hG hF hGres hr

theorem Peaks.restrict (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
    {p : ℕ → A} {F : C →L[ℂ] ℂ} (hp : Peaks (fun n => φ (p n)) F) :
    Peaks p (restrictState φ F) ∧ StateExtensionUnique φ (restrictState φ F) := by
  have hn (G : C →L[ℂ] ℂ) (hG : IsState G)
      (hr : restrictState φ G = restrictState φ F) : G = F := by
    apply hp.2.2.2.2 G hG
    intro n
    change restrictState φ G (p n) = 1
    rw [hr]
    exact hp.2.2.2.1 n
  refine ⟨⟨?_, ?_, isState_restrict φ F hp.2.2.1, hp.2.2.2.1, ?_⟩, ?_⟩
  · intro n
    refine ⟨?_, ?_⟩
    · apply hφ
      rw [map_mul]
      exact (hp.1 n).isIdempotentElem
    · apply hφ
      rw [map_star]
      exact (hp.1 n).isSelfAdjoint
  · intro m n h
    apply sub_nonneg.mp
    apply (faithfulStarHom_nonneg_iff φ hφ (p m-p n)).mp
    rw [map_sub]
    exact sub_nonneg.mpr (hp.2.1 h)
  · intro g hg hgp
    obtain ⟨G,hG,hr⟩ := exists_state_extension_of_injective φ hφ g hg
    have he : G = F := hp.2.2.2.2 G hG (fun n => by
      change restrictState φ G (p n) = 1
      rw [hr]
      exact hgp n)
    rw [← hr,he]
  · intro G H hG hH hrG hrH
    exact (hn G hG hrG).trans (hn H hH hrH).symm

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (D : PeakingPairData A) (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
  (τ : C →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ) (hn : τ 1 = 1)
  (hf : ∀ a, τ (star a*a) = 0 → a = 0)
  (ht : ∀ a, τ (φ a) = D.trace a)
  (hu : ∀ i, StateExtensionUnique φ (D.state i))

def pushedState (i : Bool) : C →L[ℂ] ℂ :=
  Classical.choose ((hu i).exists_unique_pure hφ (D.peaks i).isPureState)

theorem pushedState_isPure (i : Bool) : IsPureState (D.pushedState φ hφ hu i) :=
  (Classical.choose_spec ((hu i).exists_unique_pure hφ (D.peaks i).isPureState)).1

theorem pushedState_restrict (i : Bool) :
    restrictState φ (D.pushedState φ hφ hu i) = D.state i :=
  (Classical.choose_spec ((hu i).exists_unique_pure hφ (D.peaks i).isPureState)).2.1

def push : PeakingPairData C where
  trace := τ
  tracial := htr
  normalized := hn
  faithful := hf
  peak i n := φ (D.peak i n)
  state := D.pushedState φ hφ hu
  peaks i := (D.peaks i).extend φ (hu i) _ (D.pushedState_isPure φ hφ hu i).1
    (D.pushedState_restrict φ hφ hu i)
  peak_zero i := by rw [D.peak_zero,map_one]
  atom_positive i n := by
    change 0 < (τ (φ (D.peak i n)-φ (D.peak i (n+1)))).re
    rw [← map_sub,ht]
    exact D.atom_positive i n
  trace_null i := by
    simpa only [ht] using D.trace_null i
  matched i n := by rw [ht,ht,D.matched]

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

variable (ι : A →⋆ₐ[ℂ] C) (hp : ∀ i n, ι (B.peak i n) = D.peak i n)

include hp in
theorem state_natural (i : Bool) : restrictState ι (D.state i) = B.state i := by
  apply (B.peaks i).2.2.2.2 _ (isState_restrict ι _ (D.peaks i).2.2.1)
  intro n
  change D.state i (ι (B.peak i n)) = 1
  rw [hp]
  exact (D.peaks i).2.2.2.1 n

include hp in
theorem expectation_natural (ht : ∀ a, D.trace (ι a) = B.trace a) (i : Bool) (a : A) :
    (D.input false).expectation i (ι a) = (B.input false).expectation i a := by
  ext x
  induction x using OnePoint.rec with
  | infty =>
    rw [D.expectation_infty,B.expectation_infty]
    exact congrArg (fun f : A →L[ℂ] ℂ => f a) (B.state_natural D ι hp i)
  | coe n =>
    rw [D.expectation_nat,B.expectation_nat,← B.atom_natural D ι hp i n,
      ← map_mul,← map_mul,ht,ht]

end PeakingPairData

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Extension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open UniformSpace
open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (D : PeakingPairData C) (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ)
  (p : Bool → ℕ → A) (hp : ∀ i n, φ (p i n) = D.peak i n)

def pullback : PeakingPairData A where
  trace := positivePullback D.trace φ
  tracial a b := by simp only [positivePullback_apply,map_mul]; exact D.tracial _ _
  normalized := by simpa only [positivePullback_apply,map_one] using D.normalized
  faithful a ha := by
    apply hφ
    rw [map_zero]
    apply D.faithful
    simpa only [positivePullback_apply,map_mul,map_star] using ha
  peak := p
  state i := restrictState φ (D.state i)
  peaks i := ((D.pulled_peaks φ p hp i).restrict φ hφ).1
  peak_zero i := by apply hφ; rw [hp,D.peak_zero,map_one]
  atom_positive i n := by
    change 0 < (D.trace (φ (p i n-p i (n+1)))).re
    rw [map_sub,hp,hp]
    exact D.atom_positive i n
  trace_null i := by
    simpa only [positivePullback_apply,hp] using D.trace_null i
  matched i n := by
    change D.trace (φ (p i n)) = D.trace (φ (p false n))
    rw [hp,hp,D.matched]

include hφ hp in
theorem pullback_unique (i : Bool) :
    StateExtensionUnique φ (restrictState φ (D.state i)) :=
  ((D.pulled_peaks φ p hp i).restrict φ hφ).2

end PeakingPairData

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

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

@[simp] theorem turnCenterCLM_apply (i : Bool) (a : A) :
    B.turnCenterCLM i a = B.turnCenter i a := rfl

end PeakingPairData

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
-- module Solutions.OAIQ115_Naimark.Naimark_Stages
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section

attribute [instance] TracialStage.cstar TracialStage.order TracialStage.starOrder

namespace TracialStage

variable (X : TracialStage)

namespace Hom
variable {X Y Z W : TracialStage}

def id (X : TracialStage) : Hom X X where
  map := StarAlgHom.id ℂ X
  injective := Function.injective_id
  trace_map _ := rfl
  base_map _ := rfl
  uep := PureUEP.id

def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  map := g.map.comp f.map
  injective := g.injective.comp f.injective
  trace_map a := by rw [StarAlgHom.comp_apply,g.trace_map,f.trace_map]
  base_map a := by rw [StarAlgHom.comp_apply,f.base_map,g.base_map]
  uep := f.uep.comp g.uep

@[simp] lemma comp_map (g : Hom Y Z) (f : Hom X Y) : (g.comp f).map = g.map.comp f.map := rfl
@[simp] lemma id_map : (id X).map = StarAlgHom.id ℂ X := rfl

end Hom

end TracialStage
end

open scoped CStarAlgebra ComplexOrder
namespace TracialStage
attribute [local instance 2000] PeakingPairData.hnnCStar 
variable (X : TracialStage)

def positiveTrace : X →ₚ[ℂ] ℂ := positiveOfSquares X.trace X.traceState.2

lemma positiveTrace_normalized : X.positiveTrace 1 = 1 := ((isState_iff X.trace).mp X.traceState).1
lemma positiveTrace_faithful (a : X) (h : X.positiveTrace (star a*a) = 0) : a = 0 := by
  by_contra ha
  have hh := X.traceFaithful a ha
  change X.trace (star a*a) = 0 at h
  rw [h,Complex.zero_re] at hh
  exact (lt_irrefl 0) hh

end TracialStage

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Homogeneity
attribute [-instance] _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Filter Topology
open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (G : PeakingPairData A) (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
  (hp : ∀ i n, G.peak i n ∈ S)

attribute [local instance] OAI.NaimarkZFC.PeakingPairData.ambientSubalgebraOrder
attribute [local instance] OAI.NaimarkZFC.PeakingPairData.ambientSubalgebraStarOrder
def onSubalgebra : PeakingPairData S :=
  G.pullback S.subtype Subtype.val_injective (fun i n => ⟨G.peak i n,hp i n⟩)
    (fun _ _ => rfl)

@[simp] lemma onSubalgebra_peak (i : Bool) (n : ℕ) :
    ((G.onSubalgebra S hp).peak i n : A) = G.peak i n := rfl
@[simp] lemma onSubalgebra_trace (a : S) : (G.onSubalgebra S hp).trace a = G.trace a := rfl
@[simp] lemma onSubalgebra_state (i : Bool) (a : S) :
    (G.onSubalgebra S hp).state i a = G.state i a := rfl

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar 
variable {S R T U A : Type}
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def HNNAmbientPresentation (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A) : Prop :=
  ∃ B : PeakingPairData S,
    (∀ i n, b (B.peak i n) = G.peak i n) ∧
    (∀ a : S, B.trace a = G.trace (b a)) ∧
    ∃ e : B.HNNAlgebra ≃⋆ₐ[ℂ] T,
      (∀ a, t (e (B.hnnBase a)) = b a) ∧
      (∀ i, t (e (B.hnnLetter i)) = z i) ∧
      (∀ a, G.trace (t (e a)) = B.hnnTrace a)

end

end PeakingPairData

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

namespace PeakingPairData

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def AmbientPresentation (G : PeakingPairData A)
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] (_hp : ∀ i n, G.peak i n ∈ S)
    (z : A) (T : StarSubalgebra ℂ A) [IsClosed (T : Set A)] : Prop :=
  G.HNNAmbientPresentation S.subtype T.subtype (starPair z)

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma AmbientPresentation.congr (G : PeakingPairData A)
    (S S' T T' : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (S' : Set A)]
    [IsClosed (T : Set A)] [IsClosed (T' : Set A)]
    (pS : ∀ i n, G.peak i n ∈ S) (pS' : ∀ i n, G.peak i n ∈ S')
    (z : A) (hS : S = S') (hT : T = T')
    (h : G.AmbientPresentation S pS z T) : G.AmbientPresentation S' pS' z T' := by
  subst S'
  subst T'
  exact h

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [partialOrderC : PartialOrder C] [starOrderedRingC : StarOrderedRing C]

def turnRemainderCLM (B : PeakingPairData A) (i : Bool) : A →L[ℂ] A :=
  (starAlgHomCLM (B.diagonal i)).comp ((B.input false).expectation (!i))

@[simp] lemma turnRemainderCLM_apply (B : PeakingPairData A) (i : Bool) (a : A) :
    B.turnRemainderCLM i a = B.turnRemainder i a := rfl

end PeakingPairData

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
section
attribute [local irreducible] PeakingPairData.HNNAlgebra
universe u
variable {A : Type} [CStarAlgebra A]

lemma omittedIndices_zero (j : Ordinal.{u}) (S : Set Ordinal.{u}) :
    omittedIndices j S 0 = Set.Iio j := by
  ext k
  simp [omittedIndices]

end

open Topology

open Topology

open Topology

open Topology
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar 
variable {A S T : Type}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]

lemma states_eq_of_ambient_peaks (G : PeakingPairData A)
    (B E : PeakingPairData S) (b : S →⋆ₐ[ℂ] A)
    (hpB : ∀ i n, b (B.peak i n) = G.peak i n)
    (hpE : ∀ i n, b (E.peak i n) = G.peak i n) (i : Bool) : B.state i = E.state i :=
  (B.state_natural G b hpB i).symm.trans (E.state_natural G b hpE i)

omit partialOrderT starOrderedRingT in
lemma HNNAmbientPresentation.bridge [PartialOrder T] [StarOrderedRing T] (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (ht : Function.Injective t) (ψ : S →⋆ₐ[ℂ] T) (hψ : ∀ a, t (ψ a) = b a)
    (h : G.HNNAmbientPresentation b t z) (E : PeakingPairData S)
    (hpE : ∀ i n, b (E.peak i n) = G.peak i n)
    (hne : ¬ PureStateEquivalent (E.state false) (E.peaks false).isPureState
      (E.state true) (E.peaks true).isPureState) : BridgeSuccessor ψ := by
  obtain ⟨B,hpB,_,e,heb,_,_⟩ := h
  have hnB : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState := by
    simpa only [states_eq_of_ambient_peaks G B E b hpB hpE] using hne
  refine BridgeSuccessor.hnn B (B.separated_of_inequivalent hnB) e (fun a => ?_)
  exact ht ((heb a).trans (hψ a).symm)

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma ambient_identity_bridge [PartialOrder A] [StarOrderedRing A] (S T : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)] (hST : S ≤ T) (he : S = T) :
    BridgeSuccessor (StarSubalgebra.inclusion hST) := by
  subst T
  exact BridgeSuccessor.identity (StarAlgEquiv.refl ℂ S) (fun _ => rfl)

lemma AmbientPresentation.bridge (G : PeakingPairData A)
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    (pS : ∀ i n, G.peak i n ∈ S) (z : A) (hST : S ≤ T)
    (h : G.AmbientPresentation S pS z T)
    (hne : ¬ PureStateEquivalent ((G.onSubalgebra S pS).state false)
      ((G.onSubalgebra S pS).peaks false).isPureState ((G.onSubalgebra S pS).state true)
      ((G.onSubalgebra S pS).peaks true).isPureState) :
    BridgeSuccessor (StarSubalgebra.inclusion hST) :=
  HNNAmbientPresentation.bridge G S.subtype T.subtype (starPair z)
    Subtype.val_injective (StarSubalgebra.inclusion hST) (fun _ => rfl) h
    (G.onSubalgebra S pS) (fun _ _ => rfl) hne

end

end PeakingPairData

open Topology
namespace PeakingPairData

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
theorem ambient_bridge_ordinal_simple [PartialOrder A] [StarOrderedRing A]
    (C : Ordinal.{u} → StarSubalgebra ℂ A) [∀ i, IsClosed (C i : Set A)]
    (hm : Monotone C) (L : Ordinal.{u}) (h0 : IsSimpleCStar (C 0))
    (hn : ∀ i < L, BridgeSuccessor (StarSubalgebra.inclusion (hm (show i ≤ i+1 from le_self_add))))
    (hc : ∀ k ≤ L, Order.IsSuccLimit k →
      (C k : Set A) = closure (⋃ i : {i : Ordinal.{u} // i < k}, (C i.val : Set A)))
    (k : Ordinal.{u}) (hk : k ≤ L) : IsSimpleCStar (C k) :=
  bridge_ordinal_simple (fun i => C i)
    (fun {_ _} h => StarSubalgebra.inclusion (hm h)) L h0 hn
    (fun h => StarSubalgebra.inclusion_injective (hm h))
    (fun k hk hl => dense_subalgebra_inclusion_ranges _ _ _ (hc k hk hl)) k hk

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def PairDistinctOn (G : PeakingPairData A) (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (hp : ∀ i n, G.peak i n ∈ S) : Prop :=
  ¬ PureStateEquivalent ((G.onSubalgebra S hp).state false)
    ((G.onSubalgebra S hp).peaks false).isPureState ((G.onSubalgebra S hp).state true)
    ((G.onSubalgebra S hp).peaks true).isPureState

end

end PeakingPairData

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma dependency_peaks_omitted
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (I : Ordinal.{u} → Set Ordinal.{u}) (S : Set Ordinal.{u})
    (hclosed : DependencyClosed I S)
    (k j : Ordinal.{u}) (hkS : k ∈ S) (hI : I k ⊆ Set.Iio k)
    (hp : ∀ i n, (Q k).peak i n ∈ generatedFamily base v (I k)) :
    ∀ i n, (Q k).peak i n ∈ omittedAlgebra base v j S k := by
  intro i n
  exact generatedFamily_mono base v (fun x hx => Or.inr ⟨hclosed k hkS hx,hI hx⟩) (hp i n)

end PeakingPairData

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

section
-- module Solutions.OAIQ115_Naimark.Naimark_Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

structure ChronologicalHistory (X : TracialStage) (δ : Ordinal.{0}) where
  generator : Ordinal.{0} → X
  active : Set Ordinal.{0}
  active_lt : active ⊆ Set.Iio δ
  dependency : Ordinal.{0} → Set Ordinal.{0}
  lower : ∀ k < δ, dependency k ⊆ Set.Iio k
  countable : ∀ k < δ, (dependency k).Countable
  pair : Ordinal.{0} → PeakingPairData X
  trace : ∀ k a, (pair k).trace a = X.trace a
  leftPeak : ∀ k n, (pair k).peak false n = X.base (carPeak n)
  supported : ∀ k < δ, k ∈ active → ∀ i n,
    (pair k).peak i n ∈ generatedFamily (Set.range X.base) generator (dependency k)
  peak_mem : ∀ k ∈ active, ∀ i n,
    (pair k).peak i n ∈ generatedFamily (Set.range X.base) generator (Set.Iio k)
  chronological : ∀ k < δ, ∀ hk : k ∈ active,
    (pair k).AmbientPresentation (generatedFamily (Set.range X.base) generator (Set.Iio k))
      (peak_mem k hk) (generator k)
      (generatedFamily (Set.range X.base) generator (Set.Iio (k+1)))
  inactive : ∀ k, k ∉ active → generator k = 1
  inequivalent : ∀ k < δ, ∀ hk : k ∈ active,
    (pair k).PairDistinctOn (generatedFamily (Set.range X.base) generator (Set.Iio k))
      (peak_mem k hk)

structure ChronologicalData (X : TracialStage) (δ : Ordinal.{0}) extends ChronologicalHistory X δ where
  generated : generatedFamily (Set.range X.base) generator (Set.Iio δ) = ⊤

namespace ChronologicalData
variable {X : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalData X δ)

abbrev algebra (S : Set Ordinal.{0}) := generatedFamily (Set.range X.base) D.generator S

end ChronologicalData
end

section
open CategoryTheory
attribute [local instance] generatedFamily_isClosed

structure ChronologicalStage where
  stage : TracialStage
  height : Ordinal.{0}
  history : ChronologicalData stage height

namespace ChronologicalStage

@[ext] structure Hom (X Y : ChronologicalStage) where
  embedding : TracialStage.Hom X.stage Y.stage
  height_le : X.height ≤ Y.height
  generator : ∀ k < X.height,
    embedding.map (X.history.generator k) = Y.history.generator k
  active : ∀ k < X.height, k ∈ X.history.active ↔ k ∈ Y.history.active
  dependency : ∀ k < X.height, X.history.dependency k = Y.history.dependency k
  peak : ∀ k < X.height, ∀ i n,
    embedding.map ((X.history.pair k).peak i n) = (Y.history.pair k).peak i n

namespace Hom
variable {X Y Z : ChronologicalStage}

def comp (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  embedding := g.embedding.comp f.embedding
  height_le := f.height_le.trans g.height_le
  generator k hk := by
    change g.embedding.map (f.embedding.map (X.history.generator k)) = _
    rw [f.generator k hk,g.generator k (hk.trans_le f.height_le)]
  active k hk := (f.active k hk).trans (g.active k (hk.trans_le f.height_le))
  dependency k hk := (f.dependency k hk).trans (g.dependency k (hk.trans_le f.height_le))
  peak k hk i n := by
    change g.embedding.map (f.embedding.map ((X.history.pair k).peak i n)) = _
    rw [f.peak k hk,g.peak k (hk.trans_le f.height_le)]

@[simp] lemma comp_embedding (g : Hom Y Z) (f : Hom X Y) :
    (g.comp f).embedding = g.embedding.comp f.embedding := rfl
end Hom

end ChronologicalStage
end

open Topology
section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

@[simp] lemma closedMapEquiv_apply (S : StarSubalgebra ℂ A) (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (a : S) : (closedMapEquiv S φ hφ a : B) = φ a := rfl

end

open Topology
section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

namespace TracialStage.Hom
variable {X Y : TracialStage} (φ : TracialStage.Hom X Y)

def pushPair (P : PeakingPairData X) (ht : ∀ a, P.trace a = X.trace a) : PeakingPairData Y :=
  P.push φ.map φ.injective Y.positiveTrace Y.tracial Y.positiveTrace_normalized
    Y.positiveTrace_faithful (fun a => (φ.trace_map a).trans (ht a).symm)
    (fun i => φ.uep _ (P.peaks i).isPureState)

@[simp] lemma pushPair_peak (P : PeakingPairData X) (ht : ∀ a, P.trace a = X.trace a)
    (i : Bool) (n : ℕ) : (φ.pushPair P ht).peak i n = φ.map (P.peak i n) := rfl
@[simp] lemma pushPair_trace (P : PeakingPairData X) (ht : ∀ a, P.trace a = X.trace a)
    (a : Y) : (φ.pushPair P ht).trace a = Y.trace a := rfl

end TracialStage.Hom

end

open Topology

open Topology

open Topology

section
attribute [local instance] generatedFamily_isClosed
namespace ChronologicalData
variable {X : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalData X δ)

def advanceInactive : ChronologicalData X (δ+1) where
  generator := D.generator
  active := D.active
  active_lt := D.active_lt.trans (Set.Iio_subset_Iio (le_add_right (le_rfl : δ ≤ δ)))
  dependency k := if k < δ then D.dependency k else ∅
  lower k _ := by
    split_ifs with h
    · exact D.lower k h
    · exact Set.empty_subset _
  countable k _ := by
    split_ifs with h
    · exact D.countable k h
    · exact Set.countable_empty
  pair := D.pair
  trace := D.trace
  leftPeak := D.leftPeak
  supported k _ ha i n := by
    rw [ite_eq_left (show k < δ from D.active_lt ha)]
    exact D.supported k (D.active_lt ha) ha i n
  peak_mem := D.peak_mem
  chronological k _ ha := D.chronological k (D.active_lt ha) ha
  inactive := D.inactive
  inequivalent k _ ha := D.inequivalent k (D.active_lt ha) ha
  generated := by
    apply top_unique
    rw [← D.generated]
    exact generatedFamily_mono _ _ (Set.Iio_subset_Iio (le_add_right (le_rfl : δ ≤ δ)))
end ChronologicalData
end

open CategoryTheory

open CategoryTheory

open CategoryTheory Topology

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory Cardinal Classical

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct

open Cardinal Ordinal

open CategoryTheory Topology

open CategoryTheory Cardinal

universe u v w

end NaimarkZFC

end

end OAI
end


