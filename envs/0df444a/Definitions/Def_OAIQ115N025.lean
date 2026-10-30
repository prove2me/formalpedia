-- Prove2me | Definitions.Def_OAIQ115N025
-- name    : OAIQ115N025
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:19:21.83691+00:00
-- url     : https://prove2.me/theorems/fad7ab07-219d-4c54-923b-3e7abefcfeb5
-- title:
--   Definitions bundle OAIQ115N025 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 66 declarations of OpenAI's Lean: 2 definitions and 64 theorems. The definitions and types are `OAI.NaimarkZFC.PeakingPairData.OmittedModel`, `OAI.NaimarkZFC.PeakingPairData.pairHNNExpect`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Homogeneity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Homogeneity.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N021`, `OAIQ115N022` and `OAIQ115N023` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ115N028`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N021
import Definitions.Def_OAIQ115N022
import Definitions.Def_OAIQ115N023

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.PeakingPairData.pairHNN_cstar _root_.OAI.NaimarkZFC.carOrder _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
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

theorem traceCorner_base (a : A) : B.traceCorner (B.cornerBase a) = B.trace a := by
  change (2:ℝ) • B.modelTrace (B.embedBase (matrixSingle false false a)) = B.trace a
  rw [B.modelTrace_base,normalizedMatrixTrace_single]
  simp only [Fintype.card_bool, Nat.cast_ofNat, smul_smul]
  norm_num

theorem traceCorner_isState : IsState B.traceCorner := by
  apply cornerTrace_isState _ _ B.modelTrace B.modelTrace_isState 2 (by norm_num)
  change (2:ℝ) • B.modelTrace (B.embedBase (matrixSingle false false (1:A))) = 1
  rw [B.modelTrace_base,normalizedMatrixTrace_single,B.normalized]
  norm_num

theorem traceCorner_faithful (a : B.Corner) (ha : B.traceCorner (star a*a) = 0) : a = 0 :=
  cornerTrace_faithful _ _ B.modelTrace 2 (by norm_num)
    (atomicTrace_faithful B.atoms B.amalgam) a ha

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem traceCorner_expectation (x : B.Corner) :
    B.trace (B.expectCorner x) = B.traceCorner x :=
  matrixCorner_trace_expectation B.embedBase B.modelExpectation B.trace B.modelTrace
    (atomicExpectation_factor_mul B.atoms B.amalgam false)
    (atomicExpectation_mul_factor B.atoms B.amalgam false)
    (atomicExpectation_trace B.atoms B.amalgam false) x

end PeakingPairData

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

theorem hnnTrace_isState : IsState B.hnnTrace := B.traceCorner_isState
theorem hnnTrace_base (a : A) : B.hnnTrace (B.hnnBase a) = B.trace a := B.traceCorner_base a
theorem hnnTrace_faithful (a : B.HNNAlgebra) (ha : B.hnnTrace (star a*a) = 0) : a = 0 :=
  B.traceCorner_faithful a ha
theorem hnnTrace_expectation (a : B.HNNAlgebra) : B.trace (B.hnnExpectation a) = B.hnnTrace a :=
  B.traceCorner_expectation a

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
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

theorem hnn_no_unintended_join (hs : B.Separated) (hA : IsSimpleCStar A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hne : ¬ UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (hex : ∀ i, ¬ (UnitarilyEquivalent (pureGNS f hf)
        (pureGNS (B.state i) (B.peaks i).isPureState) ∧
      UnitarilyEquivalent (pureGNS g hg)
        (pureGNS (B.state (!i)) (B.peaks (!i)).isPureState)))
    (F G : B.HNNAlgebra →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState B.hnnBase F = f) (hrG : restrictState B.hnnBase G = g) :
    ¬ PureStateEquivalent F hF G hG := by
  apply corner_extensions_inequivalent_of_matrix_no_common B.embedBase f g ?_ F G hF hG hrF hrG
  intro H _ _ _ π hπ ξ η _ _ hcξ hcη
  apply B.matrix_no_unintended_join hs (NaimarkZFC.matrixState f false)
    (NaimarkZFC.matrixState g false) (matrixState_isPureState f hf false)
    (matrixState_isPureState g hg false) (B.supported_small_projections hA f hf false)
    (B.supported_small_projections hA g hg false) ?_ ?_ π hπ ξ η hcξ hcη
  · exact fun h => hne (matrix_pure_equivalence_reflects f g hf hg false false h)
  · intro i h
    exact hex i ⟨matrix_pure_equivalence_reflects f (B.state i) hf (B.peaks i).isPureState
      false i h.1, matrix_pure_equivalence_reflects g (B.state (!i)) hg
      (B.peaks (!i)).isPureState false (!i) h.2⟩

end PeakingPairData

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

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem pureStateEquivalent_restrict_equiv (e : A ≃⋆ₐ[ℂ] B)
    (f g : B →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (he : PureStateEquivalent f hf g hg) :
    PureStateEquivalent (restrictState e.toStarAlgHom f) (isPureState_restrict_equiv e f hf)
      (restrictState e.toStarAlgHom g) (isPureState_restrict_equiv e g hg) := by
  exact pure_lifts_equivalent e.symm.toStarAlgHom f g hf hg he
    (StateExtensionUnique.of_surjective _ e.symm.surjective g) _ _
    (isPureState_restrict_equiv e f hf) (isPureState_restrict_equiv e g hg)
    (by ext b; exact congrArg f (e.apply_symm_apply b))
    (by ext b; exact congrArg g (e.apply_symm_apply b))

end

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem hnn_restriction {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (hw : ∀ i, star (w i) = w (!i))
    (hr : ∀ i a, w i*ψ a*w (!i) = w i*ψ (B.turnCenter i a)*w (!i) +
      ψ (B.turnRemainder i a))
    (g : C →ₚ[ℂ] ℂ) (hg : ∀ c : C, g (star c*c) = 0 → c = 0)
    (hbase : ∀ a, g (ψ a) = B.trace a)
    (hred : ∀ (u : HNNWord A) a, u.Reduced B.turnCentered →
      g (ψ a*u.eval ψ w) = 0) :
    ∃ F : B.HNNAlgebra →⋆ₐ[ℂ] C, Function.Injective F ∧
      (∀ a, F (B.hnnBase a) = ψ a) ∧ (∀ i, F (B.hnnLetter i) = w i) ∧
      (∀ b, g (F b) = B.hnnTrace b) ∧ F.range = hnnGenerated ψ w := by
  apply exists_hnnRestriction B.hnnBase ψ B.hnnLetter w B.hnnLetter_star hw
    B.turnCentered B.turnCenter B.turnRemainder B.turnCenter_centered B.hnnLetter_turn hr
    (positiveOfSquares B.hnnTrace B.hnnTrace_isState.2) g
  · intro a
    exact (B.hnnTrace_base a).trans (hbase a).symm
  · intro u a hu
    change B.hnnTrace _ = g _
    rw [← B.hnnTrace_expectation,B.hnnExpectation_word u a hu,hred u a hu,map_zero]
  · exact B.hnnTrace_faithful
  · exact hg
  · exact B.hnn_generated

theorem hnn_restriction_expectation {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]
    (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (ι : A →⋆ₐ[ℂ] D)
    (F : B.HNNAlgebra →⋆ₐ[ℂ] C) (hbase : ∀ a, F (B.hnnBase a) = ψ a)
    (hletter : ∀ i, F (B.hnnLetter i) = w i)
    (G : C →L[ℂ] D) (hG : ∀ a, G (ψ a) = ι a)
    (hGr : ∀ (u : HNNWord A) a, u.Reduced B.turnCentered →
      G (ψ a*u.eval ψ w) = 0) (b : B.HNNAlgebra) :
    G (F b) = ι (B.hnnExpectation b) :=
  hnn_expectation_intertwines B.hnnBase ψ ι B.hnnLetter w F hbase hletter
    B.hnnLetter_star B.turnCentered B.turnCenter B.turnRemainder B.turnCenter_centered
    B.hnnLetter_turn B.hnnExpectation G B.hnnExpectation_base hG B.hnnExpectation_word hGr
    B.hnn_generated b

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem hnn_inclusion (ι : A →⋆ₐ[ℂ] C)
    (htrace : ∀ a, D.trace (ι a) = B.trace a)
    (hdiag : ∀ i a, ι (B.diagonal i a) = D.diagonal i a)
    (hexpect : ∀ i a, (D.input false).expectation i (ι a) =
      (B.input false).expectation i a) :
    ∃ F : B.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra, Function.Injective F ∧
      (∀ a, F (B.hnnBase a) = D.hnnBase (ι a)) ∧
      (∀ i, F (B.hnnLetter i) = D.hnnLetter i) ∧
      (∀ b, D.hnnTrace (F b) = B.hnnTrace b) ∧
      F.range = hnnGenerated (D.hnnBase.comp ι) D.hnnLetter ∧
      (∀ b, D.hnnExpectation (F b) = ι (B.hnnExpectation b)) := by
  have hc (i : Bool) (a : A) : ι (B.turnCenter i a) = D.turnCenter i (ι a) := by
    simp only [turnCenter,map_sub,hdiag,hexpect]
  have hr (i : Bool) (a : A) : ι (B.turnRemainder i a) = D.turnRemainder i (ι a) := by
    simp only [turnRemainder,hdiag,hexpect]
  have hturn i a : D.hnnLetter i*(D.hnnBase.comp ι) a*D.hnnLetter (!i) =
      D.hnnLetter i*(D.hnnBase.comp ι) (B.turnCenter i a)*D.hnnLetter (!i) +
      (D.hnnBase.comp ι) (B.turnRemainder i a) := by
    simp only [StarAlgHom.comp_apply,hc,hr]
    exact D.hnnLetter_turn i (ι a)
  have hK i a (ha : B.turnCentered i a) : D.turnCentered i (ι a) := by
    change (D.input false).expectation (!i) (ι a) = 0
    rw [hexpect]
    exact ha
  have hzero (u : HNNWord A) (a : A) (hu : u.Reduced B.turnCentered) :
      D.hnnExpectation ((D.hnnBase.comp ι) a*u.eval (D.hnnBase.comp ι) D.hnnLetter) = 0 := by
    have hv := HNNWord.mapCoefficients_reduced ι B.turnCentered D.turnCentered hK u hu
    have he : (u.mapCoefficients ι).eval D.hnnBase D.hnnLetter =
      u.eval (D.hnnBase.comp ι) D.hnnLetter :=
      u.eval_mapCoefficients ι D.hnnBase D.hnnLetter
    simpa only [he,StarAlgHom.comp_apply] using D.hnnExpectation_word (u.mapCoefficients ι) (ι a) hv
  obtain ⟨F,hF,hFa,hFv,hFt,hFr⟩ := B.hnn_restriction (D.hnnBase.comp ι) D.hnnLetter
    D.hnnLetter_star hturn (positiveOfSquares D.hnnTrace D.hnnTrace_isState.2)
    D.hnnTrace_faithful
    (fun a => (D.hnnTrace_base (ι a)).trans (htrace a))
    (fun u a hu => by
      change D.hnnTrace _ = 0
      rw [← D.hnnTrace_expectation,hzero u a hu,map_zero])
  refine ⟨F,hF,hFa,hFv,hFt,hFr,?_⟩
  exact fun b => B.hnn_restriction_expectation (D.hnnBase.comp ι) D.hnnLetter ι F hFa hFv
    D.hnnExpectation (fun a => D.hnnExpectation_base (ι a)) hzero b

end PeakingPairData

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

variable (ι : A →⋆ₐ[ℂ] C) (hp : ∀ i n, ι (B.peak i n) = D.peak i n)

include hp in

theorem hnn_inclusion_of_peaks (ht : ∀ a, D.trace (ι a) = B.trace a) :
    ∃ F : B.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra, Function.Injective F ∧
      (∀ a, F (B.hnnBase a) = D.hnnBase (ι a)) ∧
      (∀ i, F (B.hnnLetter i) = D.hnnLetter i) ∧
      (∀ b, D.hnnTrace (F b) = B.hnnTrace b) ∧
      F.range = hnnGenerated (D.hnnBase.comp ι) D.hnnLetter ∧
      (∀ b, D.hnnExpectation (F b) = ι (B.hnnExpectation b)) :=
  B.hnn_inclusion D ι ht (B.diagonal_natural D ι hp) (B.expectation_natural D ι hp ht)

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
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem hnnExpectation_state (f : A →L[ℂ] ℂ) (hf : IsState f) :
    IsState (f.comp B.hnnExpectation) := B.expectCorner_state f hf

end PeakingPairData

open Topology
open scoped ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

def pairHNNExpect : ∀ i, pairHNN B Q i →ₗ[ℂ] A
  | false => B.hnnExpectation.toLinearMap
  | true => Q.hnnExpectation.toLinearMap

end PeakingPairData

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

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty
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

variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

theorem hnn_reduced_vanish_of_dense (φ : A →⋆ₐ[ℂ] C) (v : Bool → C)
    (S : Set A) (hS : Dense S) (K : Bool → A → Prop)
    (center : Bool → A →L[ℂ] A)
    (hc : ∀ i a, K i (center i a))
    (hfix : ∀ i a, K i a → center i a = a)
    (hmem : ∀ i a, a ∈ S → center i a ∈ S)
    (f : C →L[ℂ] ℂ)
    (hz : ∀ (u : HNNWord A) a, u.Reduced K → u.AllCoefficients S → a ∈ S →
      f (φ a*u.eval φ v) = 0)
    (w : HNNWord A) (a : A) (hw : w.Reduced K) : f (φ a*w.eval φ v) = 0 := by
  obtain ⟨u,_,hu₂,hu₃,hu₄⟩ := w.reduced_approximation φ v S hS K center hc hfix hmem hw
  obtain ⟨b,hb,ht⟩ := mem_closure_iff_seq_limit.mp (hS a)
  have ht' := f.continuous.tendsto _ |>.comp (((map_continuous φ).tendsto a |>.comp ht).mul hu₄)
  apply tendsto_nhds_unique ht'
  simpa only [Function.comp_def,hz _ _ (hu₂ _) (hu₃ _) (hb _)] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0))

end

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem turnCenter_fix (i : Bool) (a : A) (ha : B.turnCentered i a) :
    B.turnCenter i a = a := by
  change (B.input false).expectation (!i) a = 0 at ha
  simp only [turnCenter,ha,map_zero,sub_zero]

theorem hnn_limit_comparison {C : Type*} [CStarAlgebra C]
    [PartialOrder C] [StarOrderedRing C]
    (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C) (hw : ∀ i, star (w i) = w (!i))
    (hr : ∀ i a, w i*ψ a*w (!i) = w i*ψ (B.turnCenter i a)*w (!i) +
      ψ (B.turnRemainder i a))
    (g : C →L[ℂ] ℂ) (hgs : IsState g)
    (hg : ∀ c : C, g (star c*c) = 0 → c = 0)
    (hbase : ∀ a, g (ψ a) = B.trace a)
    (S : Set A) (hS : Dense S)
    (hmem : ∀ i a, a ∈ S → B.turnCenter i a ∈ S)
    (hz : ∀ (u : HNNWord A) a, u.Reduced B.turnCentered →
      u.AllCoefficients S → a ∈ S → g (ψ a*u.eval ψ w) = 0)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C)) :
    ∃ e : B.HNNAlgebra ≃⋆ₐ[ℂ] C,
      (∀ a, e (B.hnnBase a) = ψ a) ∧ (∀ i, e (B.hnnLetter i) = w i) ∧
      (∀ b, g (e b) = B.hnnTrace b) := by
  have hred (u : HNNWord A) (a : A) (hu : u.Reduced B.turnCentered) :
      g (ψ a*u.eval ψ w) = 0 :=
    hnn_reduced_vanish_of_dense ψ w S hS B.turnCentered B.turnCenterCLM
      B.turnCenter_centered B.turnCenter_fix hmem g hz u a hu
  obtain ⟨F,hF,hFb,hFw,hFg,hFr⟩ := B.hnn_restriction ψ w hw hr
    (positiveOfSquares g hgs.2) hg hbase hred
  have hs : Function.Surjective F := by
    intro c
    have hc : c ∈ hnnGenerated ψ w := hd c
    rw [← hFr] at hc
    exact hc
  exact ⟨StarAlgEquiv.ofBijective F ⟨hF,hs⟩,hFb,hFw,hFg⟩

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
end

open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace
namespace KOS

@[simp] lemma projectionCutoff_zero : projectionCutoff 0 = 0 := by norm_num [projectionCutoff]

end KOS

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

variable (T : StarSubalgebra ℂ A) [IsClosed (T : Set A)] (hST : S ≤ T)
  (ht : ∀ i n, G.peak i n ∈ T)

attribute [local instance] OAI.NaimarkZFC.PeakingPairData.ambientSubalgebraOrder
attribute [local instance] OAI.NaimarkZFC.PeakingPairData.ambientSubalgebraStarOrder
include ht in
lemma onSubalgebra_unique_inclusion (i : Bool) :
    StateExtensionUnique (StarSubalgebra.inclusion hST)
      ((G.onSubalgebra S hp).state i) := by
  exact (G.onSubalgebra T ht).pullback_unique (StarSubalgebra.inclusion hST)
    (StarSubalgebra.inclusion_injective hST) ((G.onSubalgebra S hp).peak)
    (fun _ _ => rfl) i

include hST in
lemma onSubalgebra_inequivalent_of_larger
    (hne : ¬ PureStateEquivalent ((G.onSubalgebra T ht).state false)
      ((G.onSubalgebra T ht).peaks false).isPureState
      ((G.onSubalgebra T ht).state true) ((G.onSubalgebra T ht).peaks true).isPureState) :
    ¬ PureStateEquivalent ((G.onSubalgebra S hp).state false)
      ((G.onSubalgebra S hp).peaks false).isPureState
      ((G.onSubalgebra S hp).state true) ((G.onSubalgebra S hp).peaks true).isPureState := by
  intro he
  exact hne (pure_lifts_equivalent (StarSubalgebra.inclusion hST) _ _
    ((G.onSubalgebra S hp).peaks false).isPureState
    ((G.onSubalgebra S hp).peaks true).isPureState he
    (G.onSubalgebra_unique_inclusion S hp T hST ht true) _ _
    ((G.onSubalgebra T ht).peaks false).isPureState
    ((G.onSubalgebra T ht).peaks true).isPureState rfl rfl)

end
section
variable {A B C : Type} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [CStarAlgebra C]
  [PartialOrder C] [StarOrderedRing C]

theorem hnn_ambient_presentation (B₀ : PeakingPairData B) (D : PeakingPairData C)
    (φ : B →⋆ₐ[ℂ] C)
    (hp : ∀ i n, φ (B₀.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B₀.trace a)
    (Ψ : D.HNNAlgebra →⋆ₐ[ℂ] A) (hΨ : Function.Injective Ψ)
    (ψ : B →⋆ₐ[ℂ] A) (w : Bool → A)
    (hbase : ∀ b, Ψ (D.hnnBase (φ b)) = ψ b)
    (hw : ∀ i, Ψ (D.hnnLetter i) = w i) :
    ∃ e : B₀.HNNAlgebra ≃⋆ₐ[ℂ] hnnGenerated ψ w,
      (∀ b, (e (B₀.hnnBase b) : A) = ψ b) ∧
      (∀ i, (e (B₀.hnnLetter i) : A) = w i) ∧
      (∀ g : A →L[ℂ] ℂ, (∀ b, g (Ψ b) = D.hnnTrace b) →
        ∀ b, g (e b) = B₀.hnnTrace b) := by
  obtain ⟨F,hFi,hFb,hFw,hFt,hFr,_⟩ := B₀.hnn_inclusion_of_peaks D φ hp ht
  have hcomp : Ψ.comp (D.hnnBase.comp φ) = ψ := by ext b; exact hbase b
  have hletter : (fun i => Ψ (D.hnnLetter i)) = w := funext hw
  have hr : (Ψ.comp F).range = hnnGenerated ψ w := by
    rw [StarAlgHom.range_comp_eq_map,hFr,map_hnnGenerated _ _ Ψ hΨ,hcomp,hletter]
  obtain ⟨e,he⟩ := StarAlgHom.equivClosedRange (Ψ.comp F) (hΨ.comp hFi) _ hr
  refine ⟨e,?_,?_,?_⟩
  · intro b
    rw [he]
    change Ψ (F (B₀.hnnBase b)) = _
    rw [hFb,hbase]
  · intro i
    rw [he]
    change Ψ (F (B₀.hnnLetter i)) = _
    rw [hFw,hw]
  · intro g hg b
    rw [he]
    exact (hg (F b)).trans (hFt b)

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A C X : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [partialOrderC : PartialOrder C] [starOrderedRingC : StarOrderedRing C]
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]

omit partialOrderC starOrderedRingC in
lemma hnn_hom_ext [PartialOrder C] [StarOrderedRing C] (B : PeakingPairData A) (f g : B.HNNAlgebra →⋆ₐ[ℂ] C)
    (hb : ∀ a, f (B.hnnBase a) = g (B.hnnBase a))
    (hw : ∀ i, f (B.hnnLetter i) = g (B.hnnLetter i)) : f = g := by
  have hfg : (f : B.HNNAlgebra → C) = g := by
    apply Continuous.ext_on B.hnn_generated
      (show Continuous (f : B.HNNAlgebra → C) from (starAlgHomCLM f).continuous)
      (show Continuous (g : B.HNNAlgebra → C) from (starAlgHomCLM g).continuous)
    change StarAlgebra.adjoin ℂ _ ≤ StarAlgHom.equalizer f g
    apply StarAlgHom.adjoin_le_equalizer
    rintro x (⟨a,rfl⟩ | ⟨i,rfl⟩)
    · exact hb a
    · exact hw i
  exact DFunLike.ext _ _ (congrFun hfg)

end

end PeakingPairData

open Topology
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A C X : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [CStarAlgebra X]

lemma hnnGenerated_eq_top (B : PeakingPairData A) :
    hnnGenerated B.hnnBase B.hnnLetter = ⊤ := by
  apply top_unique
  intro x _
  exact B.hnn_generated x

lemma hnn_image_generated (B : PeakingPairData A) (φ : B.HNNAlgebra →⋆ₐ[ℂ] C)
    (hφ : Function.Injective φ) :
    φ.range = hnnGenerated (φ.comp B.hnnBase) (fun i => φ (B.hnnLetter i)) := by
  have H := map_hnnGenerated B.hnnBase B.hnnLetter φ hφ
  have htop : (⊤ : StarSubalgebra ℂ B.HNNAlgebra).map φ = φ.range := by
    ext c
    constructor
    · rintro ⟨b,_,rfl⟩; exact ⟨b,rfl⟩
    · rintro ⟨b,rfl⟩; exact ⟨b,trivial,rfl⟩
  rw [B.hnnGenerated_eq_top,htop] at H
  exact H

lemma hnn_equiv_image_generated (B : PeakingPairData A)
    (e : B.HNNAlgebra ≃⋆ₐ[ℂ] X) (ψ : X →⋆ₐ[ℂ] C) (hψ : Function.Injective ψ) :
    ψ.range = hnnGenerated ((ψ.comp e.toStarAlgHom).comp B.hnnBase)
      (fun i => ψ (e (B.hnnLetter i))) := by
  have H := B.hnn_image_generated (ψ.comp e.toStarAlgHom) (hψ.comp e.injective)
  have hr : (ψ.comp e.toStarAlgHom).range = ψ.range := by
    ext c
    constructor
    · rintro ⟨b,rfl⟩; exact ⟨e b,rfl⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨b,rfl⟩ := e.surjective x
      exact ⟨b,rfl⟩
  rw [hr] at H
  exact H
end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {S R T U A : Type}
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit partialOrderT starOrderedRingT in
lemma HNNAmbientPresentation.generated [PartialOrder T] [StarOrderedRing T] (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (ht : Function.Injective t) (h : G.HNNAmbientPresentation b t z) :
    t.range = hnnGenerated b z := by
  obtain ⟨B,_,_,e,heb,hew,_⟩ := h
  have H := B.hnn_equiv_image_generated e t ht
  have hb : (t.comp e.toStarAlgHom).comp B.hnnBase = b := by ext a; exact heb a
  have hw : (fun i => t (e (B.hnnLetter i))) = z := funext hew
  rw [hb,hw] at H
  exact H

end

end PeakingPairData

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Omission
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_noMax _root_.OAI.NaimarkZFC.constructionIndex_orderBot
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

lemma AmbientPresentation.generated (G : PeakingPairData A)
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] (hp : ∀ i n, G.peak i n ∈ S)
    (z : A) (T : StarSubalgebra ℂ A) [IsClosed (T : Set A)]
    (h : G.AmbientPresentation S hp z T) :
    T = hnnGenerated S.subtype (starPair z) := by
  have H := HNNAmbientPresentation.generated G S.subtype T.subtype (starPair z)
    Subtype.val_injective h
  have hr : T.subtype.range = T := by
    ext a
    constructor
    · rintro ⟨b,rfl⟩; exact b.property
    · intro ha; exact ⟨⟨a,ha⟩,rfl⟩
  exact hr.symm.trans H

end

section
attribute [local instance] hnnGenerated_isClosed ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A S X Y : Type}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]
  [CStarAlgebra Y] [partialOrderY : PartialOrder Y] [starOrderedRingY : StarOrderedRing Y]

omit partialOrderY starOrderedRingY in
lemma HNNAmbientPresentation.inherited [PartialOrder Y] [StarOrderedRing Y] (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (x : X →⋆ₐ[ℂ] A) (y : Y →⋆ₐ[ℂ] A)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (f : S →⋆ₐ[ℂ] X) (hf : ∀ a, x (f a) = b a) (z : Bool → A)
    (h : G.HNNAmbientPresentation x y z)
    (B : PeakingPairData S) (hp : ∀ i n, b (B.peak i n) = G.peak i n)
    (ht : ∀ a, B.trace a = G.trace (b a)) :
    G.HNNAmbientPresentation b (hnnGenerated b z).subtype z := by
  obtain ⟨D,hpD,htD,e,heb,hew,het⟩ := h
  let Ψ : D.HNNAlgebra →⋆ₐ[ℂ] A := y.comp e.toStarAlgHom
  have hΨ : Function.Injective Ψ := hy.comp e.injective
  have hpeak (i : Bool) (n : ℕ) : f (B.peak i n) = D.peak i n := by
    apply hx
    rw [hf,hp,hpD]
  have htrace (a : S) : D.trace (f a) = B.trace a := by
    rw [htD,hf,ht]
  have hb (a : S) : Ψ (D.hnnBase (f a)) = b a := (heb (f a)).trans (hf a)
  obtain ⟨e',he'b,he'w,he't⟩ := B.hnn_ambient_presentation D f hpeak htrace
    Ψ hΨ b z hb hew
  exact ⟨B,hp,ht,e',he'b,he'w,he't (positiveCLM G.trace) het⟩

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] hnnGenerated_isClosed
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem ambient_presentation_inherited (G : PeakingPairData A)
    (X Y S : StarSubalgebra ℂ A)
    [IsClosed (X : Set A)] [IsClosed (Y : Set A)] [IsClosed (S : Set A)]
    (pX : ∀ i n, G.peak i n ∈ X) (pS : ∀ i n, G.peak i n ∈ S)
    (z : A) (hSX : S ≤ X) (h : G.AmbientPresentation X pX z Y) :
    G.AmbientPresentation S pS z (hnnGenerated S.subtype (starPair z)) :=
  HNNAmbientPresentation.inherited G S.subtype X.subtype Y.subtype
    Subtype.val_injective Subtype.val_injective (StarSubalgebra.inclusion hSX)
    (fun _ => rfl) (starPair z) h (G.onSubalgebra S pS)
    (fun _ _ => rfl) (fun _ => rfl)

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [partialOrderC : PartialOrder C] [starOrderedRingC : StarOrderedRing C]

lemma turnCenter_natural (B : PeakingPairData A) (D : PeakingPairData C)
    (φ : A →⋆ₐ[ℂ] C) (hp : ∀ i n, φ (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B.trace a) (i : Bool) (a : A) :
    φ (B.turnCenter i a) = D.turnCenter i (φ a) := by
  simp only [turnCenter,map_sub,B.diagonal_natural D φ hp,
    B.expectation_natural D φ hp ht]

lemma turnRemainder_natural (B : PeakingPairData A) (D : PeakingPairData C)
    (φ : A →⋆ₐ[ℂ] C) (hp : ∀ i n, φ (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B.trace a) (i : Bool) (a : A) :
    φ (B.turnRemainder i a) = D.turnRemainder i (φ a) := by
  simp only [turnRemainder,B.diagonal_natural D φ hp,
    B.expectation_natural D φ hp ht]

lemma turnCentered_natural_iff (B : PeakingPairData A) (D : PeakingPairData C)
    (φ : A →⋆ₐ[ℂ] C) (hp : ∀ i n, φ (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (φ a) = B.trace a) (i : Bool) (a : A) :
    D.turnCentered i (φ a) ↔ B.turnCentered i a := by
  change (D.input false).expectation (!i) (φ a) = 0 ↔ _
  rw [B.expectation_natural D φ hp ht]
  rfl

variable {I : Type*} (B : PeakingPairData A)
  (D : I → Type) [∀ i, CStarAlgebra (D i)]
  [∀ i, PartialOrder (D i)] [∀ i, StarOrderedRing (D i)]
  (P : ∀ i, PeakingPairData (D i)) (ι : ∀ i, D i →⋆ₐ[ℂ] A)
  (hp : ∀ i s n, ι i ((P i).peak s n) = B.peak s n)
  (ht : ∀ i a, B.trace (ι i a) = (P i).trace a)
  (ψ : A →⋆ₐ[ℂ] C) (w : Bool → C)
  (F : ∀ i, (P i).HNNAlgebra →⋆ₐ[ℂ] C)
  (hFb : ∀ i a, F i ((P i).hnnBase a) = ψ (ι i a))
  (hFw : ∀ i s, F i ((P i).hnnLetter s) = w s)

include hp ht hFb hFw in
omit partialOrderC starOrderedRingC in
lemma inherited_turn [PartialOrder C] [StarOrderedRing C] (i : I) (s : Bool) (a : D i) :
    w s*ψ (ι i a)*w (!s) =
      w s*ψ (B.turnCenter s (ι i a))*w (!s) + ψ (B.turnRemainder s (ι i a)) := by
  have H := congrArg (F i) ((P i).hnnLetter_turn s a)
  simpa only [map_mul,map_add,hFb,hFw,
    (P i).turnCenter_natural B (ι i) (hp i) (ht i),
    (P i).turnRemainder_natural B (ι i) (hp i) (ht i)] using H

include hp ht in
lemma union_turnCenter_stable (s : Bool) (a : A)
    (ha : a ∈ ⋃ i, Set.range (ι i)) : B.turnCenter s a ∈ ⋃ i, Set.range (ι i) := by
  obtain ⟨i,b,rfl⟩ := Set.mem_iUnion.mp ha
  exact Set.mem_iUnion.mpr ⟨i,(P i).turnCenter s b,
    (P i).turnCenter_natural B (ι i) (hp i) (ht i) s b⟩

include hp ht hFb hFw in
omit partialOrderC starOrderedRingC in
lemma limit_reduced_moment [PartialOrder C] [StarOrderedRing C]
    (hdir : Directed (· ⊆ ·) (fun i => Set.range (ι i)))
    (g : C →L[ℂ] ℂ) (hFg : ∀ i b, g (F i b) = (P i).hnnTrace b)
    (u : HNNWord A) (a : A) (hu : u.Reduced B.turnCentered)
    (huc : u.AllCoefficients (⋃ i, Set.range (ι i)))
    (ha : a ∈ ⋃ i, Set.range (ι i)) : g (ψ a*u.eval ψ w) = 0 := by
  obtain ⟨i,hui,⟨b,rfl⟩⟩ := u.allCoefficients_one_stage
    (fun i => Set.range (ι i)) hdir huc a ha
  obtain ⟨v,rfl,hv⟩ := u.lift_reduced (ι i) (P i).turnCentered B.turnCentered
    (fun s c => ((P i).turnCentered_natural_iff B (ι i) (hp i) (ht i) s c).mp) hui hu
  have hvEval := v.eval_hom (P i).hnnBase (ψ.comp (ι i))
    (P i).hnnLetter w (F i) (hFb i) (hFw i)
  rw [HNNWord.eval_mapCoefficients]
  change g (ψ (ι i b)*v.eval (ψ.comp (ι i)) w) = 0
  rw [← hFb i b,← hvEval,← map_mul,hFg]
  rw [← (P i).hnnTrace_expectation,(P i).hnnExpectation_word v b hv,map_zero]

include hp ht hFb hFw in

theorem hnn_directed_limit_presentation [Nonempty I]
    (hdir : Directed (· ⊆ ·) (fun i => Set.range (ι i)))
    (hdense : Dense (⋃ i, Set.range (ι i)))
    (g : C →L[ℂ] ℂ) (hgs : IsState g)
    (hg : ∀ c : C, g (star c*c) = 0 → c = 0)
    (hFg : ∀ i b, g (F i b) = (P i).hnnTrace b)
    (hgen : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C)) :
    ∃ e : B.HNNAlgebra ≃⋆ₐ[ℂ] C,
      (∀ a, e (B.hnnBase a) = ψ a) ∧ (∀ s, e (B.hnnLetter s) = w s) ∧
      (∀ b, g (e b) = B.hnnTrace b) := by
  have hstar (s : Bool) : star (w s) = w (!s) := by
    obtain ⟨i⟩ := ‹Nonempty I›
    rw [← hFw i s,← map_star,(P i).hnnLetter_star,hFw]
  have hturn (s : Bool) (a : A) : w s*ψ a*w (!s) =
      w s*ψ (B.turnCenter s a)*w (!s) + ψ (B.turnRemainder s a) := by
    apply congrFun (Continuous.ext_on hdense
      (((continuous_const.mul (map_continuous ψ)).mul continuous_const))
      (((continuous_const.mul ((map_continuous ψ).comp (B.turnCenterCLM s).continuous)).mul
        continuous_const).add ((map_continuous ψ).comp (B.turnRemainderCLM s).continuous)) ?_) a
    rintro x hx
    obtain ⟨i,b,rfl⟩ := Set.mem_iUnion.mp hx
    exact B.inherited_turn D P ι hp ht ψ w F hFb hFw i s b
  have hbase (a : A) : g (ψ a) = B.trace a := by
    apply congrFun (Continuous.ext_on hdense (g.continuous.comp (map_continuous ψ)) (map_continuous B.trace) ?_) a
    rintro x hx
    obtain ⟨i,b,rfl⟩ := Set.mem_iUnion.mp hx
    change g (ψ (ι i b)) = B.trace (ι i b)
    rw [← hFb i b,hFg,(P i).hnnTrace_base,ht]
  exact B.hnn_limit_comparison ψ w hstar hturn g hgs hg hbase _ hdense
    (B.union_turnCenter_stable D P ι hp ht)
    (B.limit_reduced_moment D P ι hp ht ψ w F hFb hFw hdir g hFg) hgen

end PeakingPairData

open Topology
namespace PeakingPairData
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A V C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra V] [PartialOrder V] [StarOrderedRing V]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

lemma HNNAmbientPresentation.directed_limit {I : Type*} [Nonempty I]
    (G : PeakingPairData A) (S T : I → Type)
    [∀ i, CStarAlgebra (S i)] [∀ i, PartialOrder (S i)] [∀ i, StarOrderedRing (S i)]
    [∀ i, CStarAlgebra (T i)]
    (v : V →⋆ₐ[ℂ] A) (s : ∀ i, S i →⋆ₐ[ℂ] A) (t : ∀ i, T i →⋆ₐ[ℂ] A)
    (c : C →⋆ₐ[ℂ] A) (hv : Function.Injective v) (hc : Function.Injective c)
    (ι : ∀ i, S i →⋆ₐ[ℂ] V) (hι : ∀ i a, v (ι i a) = s i a)
    (φ : ∀ i, T i →⋆ₐ[ℂ] C) (hφ : ∀ i a, c (φ i a) = t i a)
    (ψ : V →⋆ₐ[ℂ] C) (hψ : ∀ a, c (ψ a) = v a)
    (w : Bool → C) (z : Bool → A) (hw : ∀ i, c (w i) = z i)
    (h : ∀ i, G.HNNAmbientPresentation (s i) (t i) z)
    (B : PeakingPairData V) (hp : ∀ i n, v (B.peak i n) = G.peak i n)
    (ht : ∀ a, B.trace a = G.trace (v a))
    (hdir : Directed (· ⊆ ·) (fun i => Set.range (ι i)))
    (hdense : Dense (⋃ i, Set.range (ι i)))
    (hgen : Dense (StarAlgebra.adjoin ℂ (Set.range ψ ∪ Set.range w) : Set C)) :
    G.HNNAmbientPresentation v c z := by
  choose P hpp hpt e heb hew het using h
  let F (i : I) : (P i).HNNAlgebra →⋆ₐ[ℂ] C := (φ i).comp (e i).toStarAlgHom
  have hFb (i : I) (a : S i) : F i ((P i).hnnBase a) = ψ (ι i a) := by
    apply hc
    exact (hφ i _).trans ((heb i a).trans ((hι i a).symm.trans (hψ _).symm))
  have hFw (i : I) (b : Bool) : F i ((P i).hnnLetter b) = w b := by
    apply hc
    exact (hφ i _).trans ((hew i b).trans (hw b).symm)
  have hpeak (i : I) (b : Bool) (n : ℕ) : ι i ((P i).peak b n) = B.peak b n := by
    apply hv
    exact (hι i _).trans ((hpp i b n).trans (hp b n).symm)
  have htrace (i : I) (a : S i) : B.trace (ι i a) = (P i).trace a := by
    rw [ht,hι,hpt]
  let g := restrictState c (positiveCLM G.trace)
  have hgs : IsState g := isState_restrict c _ (positiveCLM_isState G.trace G.normalized)
  have hgf (x : C) (he : g (star x*x) = 0) : x = 0 := by
    apply hc
    rw [map_zero]
    apply G.faithful
    change G.trace (c (star x*x)) = 0 at he
    simpa only [map_mul,map_star] using he
  have hFg (i : I) (b : (P i).HNNAlgebra) : g (F i b) = (P i).hnnTrace b := by
    change G.trace (c (φ i (e i b))) = _
    rw [hφ,het]
  obtain ⟨f,hfb,hfw,hft⟩ := B.hnn_directed_limit_presentation S P ι hpeak htrace ψ w F
    hFb hFw hdir hdense g hgs hgf hFg hgen
  refine ⟨B,hp,ht,f,?_,?_,hft⟩
  · intro a
    rw [hfb,hψ]
  · intro i
    rw [hfw,hw]

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] hnnGenerated_isClosed
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma AmbientPresentation.le (G : PeakingPairData A)
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] (hp : ∀ i n, G.peak i n ∈ S)
    (z : A) (T : StarSubalgebra ℂ A) [IsClosed (T : Set A)]
    (h : G.AmbientPresentation S hp z T)
    (U : StarSubalgebra ℂ A) [IsClosed (U : Set A)] (hSU : S ≤ U) (hz : z ∈ U) : T ≤ U := by
  rw [h.generated]
  change (StarAlgebra.adjoin ℂ _).topologicalClosure ≤ U
  apply StarSubalgebra.topologicalClosure_minimal _ (inferInstance : IsClosed (U : Set A))
  apply StarAlgebra.adjoin_le
  rintro x (⟨a,rfl⟩ | ⟨i,rfl⟩)
  · exact hSU a.property
  · cases i <;> simp only [starPair]
    · exact hz
    · exact star_mem hz

theorem ambient_presentation_directed_limit {I : Type*} [Nonempty I]
    (G : PeakingPairData A)
    (S T : I → StarSubalgebra ℂ A)
    [∀ i, IsClosed (S i : Set A)] [∀ i, IsClosed (T i : Set A)]
    (V : StarSubalgebra ℂ A) [IsClosed (V : Set A)]
    (pS : ∀ i s n, G.peak s n ∈ S i) (pV : ∀ s n, G.peak s n ∈ V)
    (hSV : ∀ i, S i ≤ V) (z : A)
    (h : ∀ i, G.AmbientPresentation (S i) (pS i) z (T i))
    (hdir : Directed (· ⊆ ·) (fun i => Set.range (StarSubalgebra.inclusion (hSV i))))
    (hdense : Dense (⋃ i, Set.range (StarSubalgebra.inclusion (hSV i)))) :
    G.AmbientPresentation V pV z (hnnGenerated V.subtype (starPair z)) := by
  classical
  let C := hnnGenerated V.subtype (starPair z)
  let B := G.onSubalgebra V pV
  let incl (i : I) : S i →⋆ₐ[ℂ] V := StarSubalgebra.inclusion (hSV i)
  let ψ : V →⋆ₐ[ℂ] C := hnnGeneratedBase V.subtype (starPair z)
  let w : Bool → C := hnnGeneratedLetter V.subtype (starPair z)
  have hVC : V ≤ C := by
    intro a ha
    exact (hnnGeneratedBase V.subtype (starPair z) ⟨a,ha⟩).property
  have hzC : z ∈ C := (hnnGeneratedLetter V.subtype (starPair z) false).property
  have hTC (i : I) : T i ≤ C := AmbientPresentation.le G (S i) (pS i) z (T i) (h i) C ((hSV i).trans hVC) hzC
  exact HNNAmbientPresentation.directed_limit G (fun i => S i) (fun i => T i)
    V.subtype (fun i => (S i).subtype) (fun i => (T i).subtype) C.subtype
    Subtype.val_injective Subtype.val_injective incl (fun _ _ => rfl)
    (fun i => StarSubalgebra.inclusion (hTC i)) (fun _ _ => rfl)
    ψ (fun _ => rfl) w (starPair z) (fun _ => rfl) h B
    (fun _ _ => rfl) (fun _ => rfl) hdir hdense (hnnGenerated_dense V.subtype (starPair z))

end PeakingPairData

open Topology

open Topology
section
universe u
variable {A : Type} [CStarAlgebra A]

lemma omittedAlgebra_zero (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) :
    omittedAlgebra base v j S 0 = generatedFamily base v (Set.Iio j) :=
  congrArg (generatedFamily base v) (omittedIndices_zero j S)

end

open Topology

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

theorem ambient_presentation_ordinal_limit
    (P : PeakingPairData A) (S R : Ordinal.{u} → StarSubalgebra ℂ A)
    [∀ k, IsClosed (S k : Set A)] [∀ k, IsClosed (R k : Set A)]
    (pS : ∀ k i n, P.peak i n ∈ S k)
    (hmono : Monotone S) (z : A) (β : Ordinal.{u}) (hβ : 0 < β)
    (hcont : (S β : Set A) = closure (⋃ k : Set.Iio β, (S k.val : Set A)))
    (ih : ∀ k < β, P.AmbientPresentation (S k) (pS k) z (R k)) :
    P.AmbientPresentation (S β) (pS β) z (hnnGenerated (S β).subtype (starPair z)) := by
  let : Nonempty (Set.Iio β) := ⟨⟨0,hβ⟩⟩
  exact ambient_presentation_directed_limit P (fun k : Set.Iio β => S k.val)
    (fun k : Set.Iio β => R k.val) (S β) (fun k => pS k.val) (pS β)
    (fun k => hmono k.property.le) z (fun k => ih k.val k.property)
    (subalgebra_inclusion_ranges_directed S hmono β)
    (dense_subalgebra_inclusion_ranges (fun k : Set.Iio β => S k.val) (S β)
      (fun k => hmono k.property.le) hcont)

end PeakingPairData

open Topology
namespace PeakingPairData

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hj : j < δ)
    (hja : j ∈ active) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (htrace : ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a)
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)

def OmittedModel (P : PeakingPairData A) (base : Set A) (v : Ordinal.{u} → A)
    (j : Ordinal.{u}) (S : Set Ordinal.{u}) (β : Ordinal.{u}) : Prop :=
  P.HNNAmbientPresentation (omittedAlgebra base v j S β).subtype
    (omittedAlgebra base v (j+1) S β).subtype (starPair (v j))

include hpeak hja in
lemma omitted_model_limit (β : Ordinal.{u}) (hlim : Order.IsSuccLimit β)
    (ih : ∀ k < β, (Q j).OmittedModel base v j S k) :
    (Q j).OmittedModel base v j S β := by
  let O := omittedAlgebra base v j S
  let R := omittedAlgebra base v (j+1) S
  let pO (β : Ordinal.{u}) (i : Bool) (n : ℕ) : (Q j).peak i n ∈ O β :=
    omittedAlgebra_contains_initial base v j S β (hpeak j hja i n)
  change (Q j).AmbientPresentation (O β) (pO β) (v j) (R β)
  have H := ambient_presentation_ordinal_limit (Q j) O R pO
    (fun _ _ h => omittedAlgebra_mono base v j S h) (v j) β hlim.ne_bot.bot_lt
    (omittedAlgebra_continuous base v j S β hlim) ih
  exact AmbientPresentation.congr (Q j) _ _ _ _ (pO β) (pO β) (v j) rfl
    (omittedAlgebra_hnnGenerated base v j S β) H

end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A S T : Type}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]

lemma HNNAmbientPresentation.no_unintended_join (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (ht : Function.Injective t) (ψ : S →⋆ₐ[ℂ] T) (hψ : ∀ a, t (ψ a) = b a)
    (h : G.HNNAmbientPresentation b t z) (E : PeakingPairData S)
    (hpE : ∀ i n, b (E.peak i n) = G.peak i n)
    (hE : ¬ PureStateEquivalent (E.state false) (E.peaks false).isPureState
      (E.state true) (E.peaks true).isPureState) (hS : IsSimpleCStar S)
    (f g : S →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hne : ¬ PureStateEquivalent f hf g hg)
    (hex : ∀ i, ¬ (PureStateEquivalent f hf (E.state i) (E.peaks i).isPureState ∧
      PureStateEquivalent g hg (E.state (!i)) (E.peaks (!i)).isPureState))
    (F H : T →L[ℂ] ℂ) (hF : IsPureState F) (hH : IsPureState H)
    (hrF : restrictState ψ F = f) (hrH : restrictState ψ H = g) :
    ¬ PureStateEquivalent F hF H hH := by
  obtain ⟨B,hpB,_,e,heb,_,_⟩ := h
  have hs (i : Bool) := states_eq_of_ambient_peaks G B E b hpB hpE i
  have hnB : ¬ PureStateEquivalent (B.state false) (B.peaks false).isPureState
      (B.state true) (B.peaks true).isPureState := by
    simpa only [hs] using hE
  have hexB : ∀ i, ¬ (PureStateEquivalent f hf (B.state i) (B.peaks i).isPureState ∧
      PureStateEquivalent g hg (B.state (!i)) (B.peaks (!i)).isPureState) := by
    simpa only [hs] using hex
  have heψ : e.toStarAlgHom.comp B.hnnBase = ψ := by
    ext a
    exact ht ((heb a).trans (hψ a).symm)
  have hRF : restrictState B.hnnBase (restrictState e.toStarAlgHom F) = f := by
    rw [restrictState_comp,heψ,hrF]
  have hRH : restrictState B.hnnBase (restrictState e.toStarAlgHom H) = g := by
    rw [restrictState_comp,heψ,hrH]
  intro he
  exact B.hnn_no_unintended_join (B.separated_of_inequivalent hnB) hS
    f g hf hg hne hexB _ _ (isPureState_restrict_equiv e F hF)
    (isPureState_restrict_equiv e H hH) hRF hRH
    (pureStateEquivalent_restrict_equiv e F H hF hH he)

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma onSubalgebra_class_exclusions (P Q : PeakingPairData A)
    (S X : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (X : Set A)]
    (pS : ∀ i n, P.peak i n ∈ S) (qS : ∀ i n, Q.peak i n ∈ S)
    (pX : ∀ i n, P.peak i n ∈ X) (qX : ∀ i n, Q.peak i n ∈ X)
    (hSX : S ≤ X)
    (hjoin : PureStateEquivalent ((P.onSubalgebra X pX).state false)
      ((P.onSubalgebra X pX).peaks false).isPureState ((P.onSubalgebra X pX).state true)
      ((P.onSubalgebra X pX).peaks true).isPureState)
    (hne : ¬ PureStateEquivalent ((Q.onSubalgebra X qX).state false)
      ((Q.onSubalgebra X qX).peaks false).isPureState ((Q.onSubalgebra X qX).state true)
      ((Q.onSubalgebra X qX).peaks true).isPureState) :
    (¬ PureStateEquivalent ((Q.onSubalgebra S qS).state false)
      ((Q.onSubalgebra S qS).peaks false).isPureState ((Q.onSubalgebra S qS).state true)
      ((Q.onSubalgebra S qS).peaks true).isPureState) ∧
    ∀ i, ¬ (PureStateEquivalent ((P.onSubalgebra S pS).state false)
        ((P.onSubalgebra S pS).peaks false).isPureState ((Q.onSubalgebra S qS).state i)
        ((Q.onSubalgebra S qS).peaks i).isPureState ∧
      PureStateEquivalent ((P.onSubalgebra S pS).state true)
        ((P.onSubalgebra S pS).peaks true).isPureState ((Q.onSubalgebra S qS).state (!i))
        ((Q.onSubalgebra S qS).peaks (!i)).isPureState) := by
  refine ⟨Q.onSubalgebra_inequivalent_of_larger S qS X hSX qX hne,?_⟩
  intro i he
  have lift (a b : Bool) (hab : PureStateEquivalent ((P.onSubalgebra S pS).state a)
      ((P.onSubalgebra S pS).peaks a).isPureState ((Q.onSubalgebra S qS).state b)
      ((Q.onSubalgebra S qS).peaks b).isPureState) :
      PureStateEquivalent ((P.onSubalgebra X pX).state a)
        ((P.onSubalgebra X pX).peaks a).isPureState ((Q.onSubalgebra X qX).state b)
        ((Q.onSubalgebra X qX).peaks b).isPureState :=
    pure_lifts_equivalent (StarSubalgebra.inclusion hSX) _ _
      ((P.onSubalgebra S pS).peaks a).isPureState ((Q.onSubalgebra S qS).peaks b).isPureState
      hab (Q.onSubalgebra_unique_inclusion S qS X hSX qX b) _ _
      ((P.onSubalgebra X pX).peaks a).isPureState ((Q.onSubalgebra X qX).peaks b).isPureState
      rfl rfl
  have H := PureStateEquivalent.trans (PureStateEquivalent.symm (lift false i he.1))
    (PureStateEquivalent.trans hjoin (lift true (!i) he.2))
  cases i
  · exact hne H
  · exact hne (PureStateEquivalent.symm H)

theorem ambient_preserves_omitted_inequivalence (P Q : PeakingPairData A)
    (S T X : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (X : Set A)] (hST : S ≤ T) (hSX : S ≤ X)
    (pS : ∀ i n, P.peak i n ∈ S) (qS : ∀ i n, Q.peak i n ∈ S)
    (pT : ∀ i n, P.peak i n ∈ T)
    (pX : ∀ i n, P.peak i n ∈ X) (qX : ∀ i n, Q.peak i n ∈ X)
    (z : A) (hQ : Q.AmbientPresentation S qS z T) (hs : IsSimpleCStar S)
    (hjoin : PureStateEquivalent ((P.onSubalgebra X pX).state false)
      ((P.onSubalgebra X pX).peaks false).isPureState ((P.onSubalgebra X pX).state true)
      ((P.onSubalgebra X pX).peaks true).isPureState)
    (hneQ : ¬ PureStateEquivalent ((Q.onSubalgebra X qX).state false)
      ((Q.onSubalgebra X qX).peaks false).isPureState ((Q.onSubalgebra X qX).state true)
      ((Q.onSubalgebra X qX).peaks true).isPureState)
    (hneP : ¬ PureStateEquivalent ((P.onSubalgebra S pS).state false)
      ((P.onSubalgebra S pS).peaks false).isPureState ((P.onSubalgebra S pS).state true)
      ((P.onSubalgebra S pS).peaks true).isPureState) :
    ¬ PureStateEquivalent ((P.onSubalgebra T pT).state false)
      ((P.onSubalgebra T pT).peaks false).isPureState ((P.onSubalgebra T pT).state true)
      ((P.onSubalgebra T pT).peaks true).isPureState := by
  obtain ⟨hne,hex⟩ := onSubalgebra_class_exclusions P Q S X pS qS pX qX hSX hjoin hneQ
  exact HNNAmbientPresentation.no_unintended_join Q S.subtype T.subtype (starPair z)
    Subtype.val_injective (StarSubalgebra.inclusion hST) (fun _ => rfl) hQ
    (Q.onSubalgebra S qS) (fun _ _ => rfl) hne hs _ _
    ((P.onSubalgebra S pS).peaks false).isPureState ((P.onSubalgebra S pS).peaks true).isPureState
    hneP hex _ _ ((P.onSubalgebra T pT).peaks false).isPureState
    ((P.onSubalgebra T pT).peaks true).isPureState rfl rfl

end

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma omitted_active_bridge
    (base : Set A) (v : Ordinal.{u} → A) (Q : PeakingPairData A)
    (j k : Ordinal.{u}) (S : Set Ordinal.{u}) (hkS : k ∈ S) (hjk : j ≤ k)
    (qO : ∀ i n, Q.peak i n ∈ omittedAlgebra base v j S k)
    (qX : ∀ i n, Q.peak i n ∈ generatedFamily base v (Set.Iio k))
    (hQ : Q.AmbientPresentation (generatedFamily base v (Set.Iio k)) qX
      (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hneQ : ¬ PureStateEquivalent ((Q.onSubalgebra (generatedFamily base v (Set.Iio k)) qX).state false)
      ((Q.onSubalgebra (generatedFamily base v (Set.Iio k)) qX).peaks false).isPureState
      ((Q.onSubalgebra (generatedFamily base v (Set.Iio k)) qX).state true)
      ((Q.onSubalgebra (generatedFamily base v (Set.Iio k)) qX).peaks true).isPureState) :
    BridgeSuccessor (StarSubalgebra.inclusion
      (omittedAlgebra_mono base v j S (show k ≤ k+1 from le_self_add))) := by
  let O := omittedAlgebra base v j S
  let X := generatedFamily base v (Set.Iio k)
  have hOX : O k ≤ X := omittedAlgebra_le_chronological base v j S k hjk
  have Hp := ambient_presentation_inherited Q X _ (O k) qX qO (v k) hOX hQ
  have Hp' := AmbientPresentation.congr Q _ _ _ _ qO qO (v k) rfl
    (omittedAlgebra_succ base v j S k hkS).symm Hp
  exact AmbientPresentation.bridge Q (O k) (O (k+1)) qO (v k)
    (omittedAlgebra_mono base v j S le_self_add) Hp'
    (Q.onSubalgebra_inequivalent_of_larger (O k) qO X hOX qX hneQ)

theorem omitted_successor_bridge
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      ¬ PureStateEquivalent (((Q k).onSubalgebra (generatedFamily base v (Set.Iio k)) (hpeak k hk)).state false)
        (((Q k).onSubalgebra (generatedFamily base v (Set.Iio k)) (hpeak k hk)).peaks false).isPureState
        (((Q k).onSubalgebra (generatedFamily base v (Set.Iio k)) (hpeak k hk)).state true)
        (((Q k).onSubalgebra (generatedFamily base v (Set.Iio k)) (hpeak k hk)).peaks true).isPureState)
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (k : Ordinal.{u}) (hkδ : k < δ) :
    BridgeSuccessor (StarSubalgebra.inclusion
      (omittedAlgebra_mono base v j S (show k ≤ k+1 from le_self_add))) := by
  have inert (he : omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k) :=
    ambient_identity_bridge _ _ (omittedAlgebra_mono base v j S le_self_add) he.symm
  by_cases hkS : k ∈ S
  · by_cases hkj : k < j
    · exact inert (omittedAlgebra_succ_of_lt base v j S k hkj)
    · have hjk : j < k := lt_of_le_of_ne (le_of_not_gt hkj) (fun e => hjS (e ▸ hkS))
      by_cases hka : k ∈ active
      · exact omitted_active_bridge base v (Q k) j k S hkS hjk.le
          (hdep k hkδ hkS hka hjk) (hpeak k hka) (hchrono k hkδ hka) (hne k hkδ hka)
      · exact inert (omittedAlgebra_succ_of_one base v j S k (hinactive k hkδ hka))
  · exact inert (omittedAlgebra_succ_of_not_mem base v j S k hkS)

end

end PeakingPairData

open Topology
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A S T : Type}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]

lemma joined_of_conjugacy (E : PeakingPairData T) (u : unitary T)
    (hc : ∀ n, (u:T)*E.peak false n*star (u:T) = E.peak true n) :
    PureStateEquivalent (E.state false) (E.peaks false).isPureState
      (E.state true) (E.peaks true).isPureState :=
  (E.peaks false).join_named (E.peaks true) (StarAlgHom.id ℂ T) u hc
    (StateExtensionUnique.of_surjective _ Function.surjective_id _)
    _ _ (E.peaks false).isPureState (E.peaks true).isPureState rfl rfl

lemma HNNAmbientPresentation.joined (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (ht : Function.Injective t) (h : G.HNNAmbientPresentation b t z)
    (E : PeakingPairData T) (hpE : ∀ i n, t (E.peak i n) = G.peak i n) :
    PureStateEquivalent (E.state false) (E.peaks false).isPureState
      (E.state true) (E.peaks true).isPureState := by
  obtain ⟨B,hpB,_,e,heb,_,_⟩ := h
  let u : unitary T := ⟨e (B.hnnUnitary:B.HNNAlgebra),by
    constructor
    · rw [← map_star,← map_mul,B.hnnUnitary.property.1,map_one]
    · rw [← map_star,← map_mul,B.hnnUnitary.property.2,map_one]⟩
  apply E.joined_of_conjugacy u
  have he (i : Bool) (n : ℕ) : e (B.hnnBase (B.peak i n)) = E.peak i n :=
    ht ((heb _).trans ((hpB i n).trans (hpE i n).symm))
  intro n
  change e (B.hnnUnitary:B.HNNAlgebra) * E.peak false n *
    star (e (B.hnnUnitary:B.HNNAlgebra)) = E.peak true n
  rw [← he false n,← he true n,← map_star,← map_mul,← map_mul,B.hnnUnitary_conjugates]

lemma AmbientPresentation.joined (G : PeakingPairData A)
    (V W : StarSubalgebra ℂ A) [IsClosed (V : Set A)] [IsClosed (W : Set A)]
    (pV : ∀ i n, G.peak i n ∈ V) (pW : ∀ i n, G.peak i n ∈ W)
    (z : A) (h : G.AmbientPresentation V pV z W) :
    PureStateEquivalent ((G.onSubalgebra W pW).state false)
      ((G.onSubalgebra W pW).peaks false).isPureState ((G.onSubalgebra W pW).state true)
      ((G.onSubalgebra W pW).peaks true).isPureState :=
  HNNAmbientPresentation.joined G V.subtype W.subtype (starPair z) Subtype.val_injective h
    (G.onSubalgebra W pW) (fun _ _ => rfl)

lemma joined_onSubalgebra_larger (G : PeakingPairData A)
    (V W : StarSubalgebra ℂ A) [IsClosed (V : Set A)] [IsClosed (W : Set A)]
    (pV : ∀ i n, G.peak i n ∈ V) (pW : ∀ i n, G.peak i n ∈ W) (hVW : V ≤ W)
    (h : PureStateEquivalent ((G.onSubalgebra V pV).state false)
      ((G.onSubalgebra V pV).peaks false).isPureState ((G.onSubalgebra V pV).state true)
      ((G.onSubalgebra V pV).peaks true).isPureState) :
    PureStateEquivalent ((G.onSubalgebra W pW).state false)
      ((G.onSubalgebra W pW).peaks false).isPureState ((G.onSubalgebra W pW).state true)
      ((G.onSubalgebra W pW).peaks true).isPureState :=
  pure_lifts_equivalent (StarSubalgebra.inclusion hVW) _ _
    ((G.onSubalgebra V pV).peaks false).isPureState ((G.onSubalgebra V pV).peaks true).isPureState
    h (G.onSubalgebra_unique_inclusion V pV W hVW pW true) _ _
    ((G.onSubalgebra W pW).peaks false).isPureState ((G.onSubalgebra W pW).peaks true).isPureState rfl rfl

end

section
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma PairDistinctOn.congr (G : PeakingPairData A)
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    (pS : ∀ i n, G.peak i n ∈ S) (pT : ∀ i n, G.peak i n ∈ T)
    (he : S = T) (h : G.PairDistinctOn S pS) : G.PairDistinctOn T pT := by
  subst T
  exact h

end

end PeakingPairData

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem inherited_successor_bridge
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u})
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j ≤ k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (k : Ordinal.{u}) (hkδ : k < δ) :
    BridgeSuccessor (StarSubalgebra.inclusion
      (omittedAlgebra_mono base v j S (show k ≤ k+1 from le_self_add))) := by
  have inert (he : omittedAlgebra base v j S (k+1) = omittedAlgebra base v j S k) :=
    ambient_identity_bridge _ _ (omittedAlgebra_mono base v j S le_self_add) he.symm
  by_cases hkS : k ∈ S
  · by_cases hkj : k < j
    · exact inert (omittedAlgebra_succ_of_lt base v j S k hkj)
    · have hjk : j ≤ k := le_of_not_gt hkj
      by_cases hka : k ∈ active
      · exact omitted_active_bridge base v (Q k) j k S hkS hjk
          (hdep k hkδ hkS hka hjk) (hpeak k hka) (hchrono k hkδ hka) (hne k hkδ hka)
      · exact inert (omittedAlgebra_succ_of_one base v j S k (hinactive k hkδ hka))
  · exact inert (omittedAlgebra_succ_of_not_mem base v j S k hkS)

theorem inherited_simple
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u})
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j ≤ k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio j)))
    (β : Ordinal.{u}) (hβ : β ≤ δ) : IsSimpleCStar (omittedAlgebra base v j S β) := by
  apply ambient_bridge_ordinal_simple (omittedAlgebra base v j S)
    (fun _ _ h => omittedAlgebra_mono base v j S h) δ _ _ _ β hβ
  · exact (subalgebra_simple_congr _ _ (omittedAlgebra_zero base v j S)).mpr h0
  · exact inherited_successor_bridge base v Q active S δ j hpeak hchrono hinactive hne hdep
  · intro k _ hlim
    exact omittedAlgebra_continuous base v j S k hlim

end PeakingPairData

section
open Topology
universe u
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

omit partialOrderA starOrderedRingA in
lemma ambient_bridge_congr [PartialOrder A] [StarOrderedRing A] (S T S' T' : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (S' : Set A)] [IsClosed (T' : Set A)]
    (hST : S ≤ T) (hST' : S' ≤ T') (hS : S = S') (hT : T = T')
    (h : BridgeSuccessor (StarSubalgebra.inclusion hST)) :
    BridgeSuccessor (StarSubalgebra.inclusion hST') := by
  subst S'
  subst T'
  exact h

theorem chronological_simple
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active : Set Ordinal.{u}) (δ : Ordinal.{u})
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio 0)))
    (β : Ordinal.{u}) (hβ : β ≤ δ) : IsSimpleCStar (generatedFamily base v (Set.Iio β)) := by
  have hd : ∀ k < δ, k ∈ Set.Iio δ → k ∈ active → (0 : Ordinal.{u}) ≤ k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v 0 (Set.Iio δ) k := by
    intro k hk _ hka _ i n
    rw [omittedAlgebra_all_before base v δ k hk.le]
    exact hpeak k hka i n
  exact (subalgebra_simple_congr _ _ (omittedAlgebra_all_before base v δ β hβ)).mp
    (inherited_simple base v Q active (Set.Iio δ) δ 0 hpeak hchrono hinactive hne hd h0 β hβ)

end PeakingPairData
end

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem omitted_simple_of_chronological
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio j)))
    (β : Ordinal.{u}) (hβ : β ≤ δ) : IsSimpleCStar (omittedAlgebra base v j S β) := by
  apply ambient_bridge_ordinal_simple (omittedAlgebra base v j S)
    (fun _ _ h => omittedAlgebra_mono base v j S h) δ _ _ _ β hβ
  · exact (subalgebra_simple_congr _ _ (omittedAlgebra_zero base v j S)).mpr h0
  · exact omitted_successor_bridge base v Q active S δ j hjS hpeak hchrono hinactive hne hdep
  · intro k _ hlim
    exact omittedAlgebra_continuous base v j S k hlim

end PeakingPairData

section
universe u
variable {A : Type} [CStarAlgebra A]

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable [PartialOrder A] [StarOrderedRing A]

lemma chronological_joined (base : Set A) (v : Ordinal.{u} → A)
    (G : PeakingPairData A) (j k : Ordinal.{u}) (hjk : j < k)
    (p : ∀ i n, G.peak i n ∈ generatedFamily base v (Set.Iio j))
    (h : G.AmbientPresentation (generatedFamily base v (Set.Iio j)) p (v j)
      (generatedFamily base v (Set.Iio (j+1)))) :
    PureStateEquivalent
      ((G.onSubalgebra (generatedFamily base v (Set.Iio k))
        (fun i n => generatedFamily_Iio_mono base v hjk.le (p i n))).state false)
      ((G.onSubalgebra (generatedFamily base v (Set.Iio k))
        (fun i n => generatedFamily_Iio_mono base v hjk.le (p i n))).peaks false).isPureState
      ((G.onSubalgebra (generatedFamily base v (Set.Iio k))
        (fun i n => generatedFamily_Iio_mono base v hjk.le (p i n))).state true)
      ((G.onSubalgebra (generatedFamily base v (Set.Iio k))
        (fun i n => generatedFamily_Iio_mono base v hjk.le (p i n))).peaks true).isPureState := by
  let p' (i : Bool) (n : ℕ) := generatedFamily_Iio_mono base v
    (show j ≤ j+1 from le_self_add) (p i n)
  exact joined_onSubalgebra_larger G _ _ p' _
    (generatedFamily_Iio_mono base v (Order.add_one_le_iff.mpr hjk))
    (AmbientPresentation.joined G _ _ p p' (v j) h)

end PeakingPairData
end

open Topology
namespace PeakingPairData

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem ambient_pair_ordinal_inequivalent (G : PeakingPairData A)
    (C : Ordinal.{u} → StarSubalgebra ℂ A) [∀ i, IsClosed (C i : Set A)]
    (pC : ∀ k i n, G.peak i n ∈ C k) (hm : Monotone C) (L : Ordinal.{u})
    (h0 : G.PairDistinctOn (C 0) (pC 0))
    (hn : ∀ k < L, G.PairDistinctOn (C k) (pC k) → G.PairDistinctOn (C (k+1)) (pC (k+1)))
    (hc : ∀ k ≤ L, Order.IsSuccLimit k →
      (C k : Set A) = closure (⋃ i : {i : Ordinal.{u} // i < k}, (C i.val : Set A)))
    (k : Ordinal.{u}) (hk : k ≤ L) : G.PairDistinctOn (C k) (pC k) :=
  pure_inequivalent_ordinal_chain (fun k => C k)
    (fun {_ _} h => StarSubalgebra.inclusion (hm h)) (fun _ _ => rfl) L 0
    (fun k => (G.onSubalgebra (C k) (pC k)).state false)
    (fun k => (G.onSubalgebra (C k) (pC k)).state true)
    (fun k => ((G.onSubalgebra (C k) (pC k)).peaks false).isPureState)
    (fun k => ((G.onSubalgebra (C k) (pC k)).peaks true).isPureState)
    (fun _ => rfl) (fun _ => rfl) h0 (fun k hk _ => hn k hk)
    (fun k hk hl => dense_subalgebra_inclusion_ranges _ _ _ (hc k hk hl)) k hk bot_le

end

section
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed hnnGenerated_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma omitted_active_preserves_distinct
    (base : Set A) (v : Ordinal.{u} → A) (P Q : PeakingPairData A)
    (j k : Ordinal.{u}) (S : Set Ordinal.{u}) (hkS : k ∈ S) (hjk : j < k)
    (p : ∀ i n, P.peak i n ∈ generatedFamily base v (Set.Iio j))
    (qO : ∀ i n, Q.peak i n ∈ omittedAlgebra base v j S k)
    (qX : ∀ i n, Q.peak i n ∈ generatedFamily base v (Set.Iio k))
    (hP : P.AmbientPresentation (generatedFamily base v (Set.Iio j)) p
      (v j) (generatedFamily base v (Set.Iio (j+1))))
    (hQ : Q.AmbientPresentation (generatedFamily base v (Set.Iio k)) qX
      (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hs : IsSimpleCStar (omittedAlgebra base v j S k))
    (hneQ : Q.PairDistinctOn (generatedFamily base v (Set.Iio k)) qX)
    (hneP : P.PairDistinctOn (omittedAlgebra base v j S k)
      (fun i n => omittedAlgebra_contains_initial base v j S k (p i n))) :
    P.PairDistinctOn (omittedAlgebra base v j S (k+1))
      (fun i n => omittedAlgebra_contains_initial base v j S (k+1) (p i n)) := by
  let O := omittedAlgebra base v j S
  let X := generatedFamily base v (Set.Iio k)
  let pO (β : Ordinal.{u}) (i : Bool) (n : ℕ) :=
    omittedAlgebra_contains_initial base v j S β (p i n)
  let pX (i : Bool) (n : ℕ) := generatedFamily_Iio_mono base v hjk.le (p i n)
  have hOX : O k ≤ X := omittedAlgebra_le_chronological base v j S k hjk.le
  have Hp := ambient_presentation_inherited Q X _ (O k) qX qO (v k) hOX hQ
  have Hp' := AmbientPresentation.congr Q _ _ _ _ qO qO (v k) rfl
    (omittedAlgebra_succ base v j S k hkS).symm Hp
  exact ambient_preserves_omitted_inequivalence P Q (O k) (O (k+1)) X
    (omittedAlgebra_mono base v j S le_self_add) hOX (pO k) qO (pO (k+1)) pX qX
    (v k) Hp' hs (chronological_joined base v P j k hjk p hP) hneQ hneP

variable
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hj : j < δ)
    (hja : j ∈ active) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio j)))

include hj hja hjS hpeak hchrono hinactive hne hdep h0 in
lemma omitted_distinct_successor (k : Ordinal.{u}) (hkδ : k < δ)
    (hi : (Q j).PairDistinctOn (omittedAlgebra base v j S k)
      (fun i n => omittedAlgebra_contains_initial base v j S k (hpeak j hja i n))) :
    (Q j).PairDistinctOn (omittedAlgebra base v j S (k+1))
      (fun i n => omittedAlgebra_contains_initial base v j S (k+1) (hpeak j hja i n)) := by
  let O := omittedAlgebra base v j S
  let pO (β : Ordinal.{u}) (i : Bool) (n : ℕ) :=
    omittedAlgebra_contains_initial base v j S β (hpeak j hja i n)
  have inert (he : O (k+1) = O k) : (Q j).PairDistinctOn (O (k+1)) (pO (k+1)) :=
    PairDistinctOn.congr (Q j) _ _ (pO k) (pO (k+1)) he.symm hi
  by_cases hkS : k ∈ S
  · by_cases hkj : k < j
    · exact inert (omittedAlgebra_succ_of_lt base v j S k hkj)
    · have hjk : j < k := lt_of_le_of_ne (le_of_not_gt hkj) (fun e => hjS (e ▸ hkS))
      by_cases hka : k ∈ active
      · exact omitted_active_preserves_distinct base v (Q j) (Q k) j k S hkS hjk
          (hpeak j hja) (hdep k hkδ hkS hka hjk) (hpeak k hka)
          (hchrono j hj hja) (hchrono k hkδ hka)
          (omitted_simple_of_chronological base v Q active S δ j hjS hpeak hchrono
            hinactive hne hdep h0 k hkδ.le) (hne k hkδ hka) hi
      · exact inert (omittedAlgebra_succ_of_one base v j S k (hinactive k hkδ hka))
  · exact inert (omittedAlgebra_succ_of_not_mem base v j S k hkS)

end

end PeakingPairData

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (δ j : Ordinal.{u}) (hj : j < δ)
    (hja : j ∈ active) (hjS : j ∉ S)
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (hdep : ∀ k < δ, k ∈ S → k ∈ active → j < k → ∀ i n,
      (Q k).peak i n ∈ omittedAlgebra base v j S k)
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio j)))

include hj hja hjS hpeak hchrono hinactive hne hdep h0 in

theorem omitted_distinct_of_chronological (β : Ordinal.{u}) (hβ : β ≤ δ) :
    (Q j).PairDistinctOn (omittedAlgebra base v j S β)
      (fun i n => omittedAlgebra_contains_initial base v j S β (hpeak j hja i n)) := by
  apply ambient_pair_ordinal_inequivalent (Q j) (omittedAlgebra base v j S)
    (fun β i n => omittedAlgebra_contains_initial base v j S β (hpeak j hja i n))
    (fun _ _ h => omittedAlgebra_mono base v j S h) δ _ _ _ β hβ
  · exact PairDistinctOn.congr (Q j) _ _ (hpeak j hja) _
      (omittedAlgebra_zero base v j S).symm (hne j hj hja)
  · exact omitted_distinct_successor base v Q active S δ j hj hja hjS hpeak hchrono
      hinactive hne hdep h0
  · intro k _ hlim
    exact omittedAlgebra_continuous base v j S k hlim

end PeakingPairData

open Topology
namespace PeakingPairData
universe u
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable
    (base : Set A) (v : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active S : Set Ordinal.{u}) (I : Ordinal.{u} → Set Ordinal.{u}) (δ : Ordinal.{u})
    (hS : S ⊆ Set.Iio δ) (hclosed : DependencyClosed I S)
    (hI : ∀ k < δ, k ∈ active → I k ⊆ Set.Iio k)
    (hdata : ∀ k < δ, k ∈ active → ∀ i n, (Q k).peak i n ∈ generatedFamily base v (I k))
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base v (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base v (Set.Iio k)) (hpeak k hk)
        (v k) (generatedFamily base v (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → v k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base v (Set.Iio k)) (hpeak k hk))
    (h0 : IsSimpleCStar (generatedFamily base v (Set.Iio 0)))

include hS hclosed hI hdata hpeak hchrono hinactive hne h0 in

theorem dependency_closed_retained_simple :
    IsSimpleCStar (retainedOrdinalAlgebra base v S 0) := by
  apply (subalgebra_simple_congr _ _
    (omittedAlgebra_endpoint_eq_retained base v S δ 0 hS)).mp
  apply inherited_simple base v Q active S δ 0 hpeak hchrono hinactive hne _ h0 δ le_rfl
  intro k hkδ hkS hka _
  exact dependency_peaks_omitted base v Q I S hclosed k 0 hkS (hI k hkδ hka) (hdata k hkδ hka)

end PeakingPairData

open Topology

open Cardinal Topology TopologicalSpace

open Cardinal Topology TopologicalSpace

end NaimarkZFC

end

end OAI
end


