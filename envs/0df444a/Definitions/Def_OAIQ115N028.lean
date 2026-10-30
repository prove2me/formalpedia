-- Prove2me | Definitions.Def_OAIQ115N028
-- name    : OAIQ115N028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:36:59.258705+00:00
-- url     : https://prove2.me/theorems/acfb17b7-17b6-4a87-ac18-4507bbf8fb1b
-- title:
--   Definitions bundle OAIQ115N028 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 144 declarations of OpenAI's Lean: 45 definitions, 4 instances and 95 theorems. The definitions and types are `OAI.NaimarkZFC.ChronologicalHistory.insertActive`, `OAI.NaimarkZFC.ChronologicalHistory.push`, `OAI.NaimarkZFC.ChronologicalStage.FullRule_unconditional`, `OAI.NaimarkZFC.ChronologicalStage.Treated`, `OAI.NaimarkZFC.ChronologicalStage.directLimit`, `OAI.NaimarkZFC.ChronologicalStage.directLimitCocone`, `OAI.NaimarkZFC.ChronologicalStage.directLimitHom`, `OAI.NaimarkZFC.ChronologicalStage.earlierPrefixes`, `OAI.NaimarkZFC.ChronologicalStage.forget`, `OAI.NaimarkZFC.ChronologicalStage.fullTower_unconditional`, `OAI.NaimarkZFC.ChronologicalStage.gluePrefixes`, `OAI.NaimarkZFC.ChronologicalStage.hnnEmbedding`, `OAI.NaimarkZFC.ChronologicalStage.hnnHistory`, `OAI.NaimarkZFC.ChronologicalStage.hnnHom`, `OAI.NaimarkZFC.ChronologicalStage.hnnNewPair`, `OAI.NaimarkZFC.ChronologicalStage.hnnPriorHistory`, `OAI.NaimarkZFC.ChronologicalStage.hnnSuccessor`, `OAI.NaimarkZFC.ChronologicalStage.inactiveHom`, `OAI.NaimarkZFC.ChronologicalStage.initial`, `OAI.NaimarkZFC.ChronologicalStage.initialHistory`, `OAI.NaimarkZFC.ChronologicalStage.joiningChoice_unconditional`, `OAI.NaimarkZFC.ChronologicalStage.limitActive`, `OAI.NaimarkZFC.ChronologicalStage.limitDependency`, `OAI.NaimarkZFC.ChronologicalStage.limitEmbedding`, `OAI.NaimarkZFC.ChronologicalStage.limitGenerator`, `OAI.NaimarkZFC.ChronologicalStage.limitHeight`, `OAI.NaimarkZFC.ChronologicalStage.limitHistory`, `OAI.NaimarkZFC.ChronologicalStage.limitIndex`, `OAI.NaimarkZFC.ChronologicalStage.limitPair`, `OAI.NaimarkZFC.ChronologicalStage.limitStage`, `OAI.NaimarkZFC.ChronologicalStage.prefixSystem`, `OAI.NaimarkZFC.ChronologicalStage.pureList`, `OAI.NaimarkZFC.ChronologicalStage.recursionData`, `OAI.NaimarkZFC.ChronologicalStage.recursivePrefixes`, `OAI.NaimarkZFC.ChronologicalStage.recursiveTower`, `OAI.NaimarkZFC.ChronologicalStage.scheduledRule_unconditional`, `OAI.NaimarkZFC.ChronologicalStage.scheduledTarget`, `OAI.NaimarkZFC.KOS.projectionTruncate`, `OAI.NaimarkZFC.PeakingPairData.reorderEquiv`, `OAI.NaimarkZFC.TracialStage.Hom.pureLift` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Homogeneity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Homogeneity.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean), [`Naimark_Operators`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Operators.lean), [`Naimark_Recursion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Recursion.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean), [`Naimark_Tracial`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Tracial.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N025`, `OAIQ115N026` and `OAIQ115N027` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.NaimarkZFC.main`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N025
import Definitions.Def_OAIQ115N026
import Definitions.Def_OAIQ115N027

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.PeakingPairData.pairHNN_cstar _root_.OAI.NaimarkZFC.carOrder _root_.OAI.NaimarkZFC.hnnGeneratedCStar
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

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

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

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra

open Topology

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
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem hnn_equiv_of_peaks (e : A ≃⋆ₐ[ℂ] C)
    (hp : ∀ i n, e (B.peak i n) = D.peak i n)
    (ht : ∀ a, D.trace (e a) = B.trace a) :
    ∃ E : B.HNNAlgebra ≃⋆ₐ[ℂ] D.HNNAlgebra,
      (∀ a, E (B.hnnBase a) = D.hnnBase (e a)) ∧
      (∀ i, E (B.hnnLetter i) = D.hnnLetter i) ∧
      (∀ b, D.hnnTrace (E b) = B.hnnTrace b) ∧
      (∀ b, D.hnnExpectation (E b) = e (B.hnnExpectation b)) := by
  obtain ⟨F,hF,hb,hv,htr,hr,he⟩ := B.hnn_inclusion_of_peaks D e.toStarAlgHom hp ht
  have hbr : Set.range (D.hnnBase.comp e.toStarAlgHom) = Set.range D.hnnBase := by
    apply Set.Subset.antisymm
    · rintro _ ⟨a,rfl⟩
      exact ⟨e a,rfl⟩
    · rintro _ ⟨c,rfl⟩
      obtain ⟨a,rfl⟩ := e.surjective c
      exact ⟨a,rfl⟩
  have hs : Function.Surjective F := by
    intro x
    have hx : x ∈ hnnGenerated (D.hnnBase.comp e.toStarAlgHom) D.hnnLetter := by
      change x ∈ closure (StarAlgebra.adjoin ℂ
        (Set.range (D.hnnBase.comp e.toStarAlgHom) ∪ Set.range D.hnnLetter) : Set D.HNNAlgebra)
      rw [hbr]
      exact D.hnn_generated x
    rw [← hr] at hx
    exact hx
  exact ⟨StarAlgEquiv.ofBijective F ⟨hF,hs⟩,hb,hv,htr,he⟩

end PeakingPairData

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Extension
attribute [-instance] _root_.OAI.NaimarkZFC.carOrder
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

namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)
  (ι : A →⋆ₐ[ℂ] C) (hp : ∀ i n, ι (B.peak i n) = D.peak i n)
  (F : C →L[ℂ] A) (hfix : ∀ a, F (ι a) = a)
  (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp F))
  (hleft : ∀ a x, F (ι a*x) = a*F x) (hright : ∀ x a, F (x*ι a) = F x*a)
  (ht : ∀ x, B.trace (F x) = D.trace x)
  (V : Bool → Type*) [∀ i, Ring (V i)] [∀ i, Algebra ℂ (V i)]
  (E : ∀ i, V i →ₗ[ℂ] A) (φ : ∀ i, V i →ₐ[ℂ] D.HNNAlgebra)

include hp hfix hstate hleft hright ht in

theorem hnn_family_free (s : Bool → Bool) (hs : Function.Injective s)
    (hk : ∀ i x, E i x = 0 →
      HNNCenteredBlock ι D.hnnBase D.hnnLetter B.turnCentered F (s i) (φ i x))
    (w : List (Bool × D.HNNAlgebra)) (hw : IsCenteredWord (factorCenters V E φ) w)
    (hne : w ≠ []) : D.hnnTrace (wordValue w) = 0 := by
  have h := B.hnn_free_blocks D ι hp F hfix hstate hleft hright ht
    (w.map (fun p => (s p.1,p.2))) (by simpa using hne) ?_ ?_
  · rw [wordValue_reindex] at h
    rw [← D.hnnTrace_expectation,← ht,h,map_zero]
  · intro p hpw
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hpw
    obtain ⟨x,hx,hxq⟩ := hw.centered q hq
    change E q.1 x = 0 at hx
    exact hxq ▸ hk q.1 x hx
  · apply (List.isChain_map _).mpr
    exact hw.alternating.imp (fun _ _ h he => h (hs he))

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

theorem pairHNNExpect_fix (i : Bool) (a : A) :
    pairHNNExpect B Q i (pairHNNBase B Q i a) = a := by
  cases i
  · exact B.hnnExpectation_base a
  · exact Q.hnnExpectation_base a

theorem pairHNNExpect_left (i : Bool) (a : A) (x : pairHNN B Q i) :
    pairHNNExpect B Q i (pairHNNBase B Q i a*x) = a*pairHNNExpect B Q i x := by
  cases i
  · exact B.hnnExpectation_left a x
  · exact Q.hnnExpectation_left a x

variable (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
  (jQ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra) (jB : B.HNNAlgebra →⋆ₐ[ℂ] E.HNNAlgebra)

theorem leftHNNFamily_free
    (hp : ∀ i n, B.hnnBase (Q.peak i n) = D.peak i n)
    (ht : ∀ x, Q.trace (B.hnnExpectation x) = D.trace x)
    (ha : ∀ a, jQ (Q.hnnBase a) = D.hnnBase (B.hnnBase a))
    (hv : ∀ i, jQ (Q.hnnLetter i) = D.hnnLetter i)
    (w) (hw : IsCenteredWord (factorCenters (pairHNN B Q) (pairHNNExpect B Q)
      (fun i => (leftHNNFamily B Q D jQ i).toAlgHom)) w) (hne : w ≠ []) :
    D.hnnTrace (wordValue w) = 0 := by
  apply Q.hnn_family_free D B.hnnBase hp B.hnnExpectation B.hnnExpectation_base
    B.hnnExpectation_state B.hnnExpectation_left B.hnnExpectation_right ht
    (pairHNN B Q) (pairHNNExpect B Q) (fun i => (leftHNNFamily B Q D jQ i).toAlgHom)
    id Function.injective_id ?_ w hw hne
  intro i x hx
  cases i
  · exact ⟨x,hx,rfl⟩
  · exact Q.hnn_mapped_kernel D B.hnnBase jQ ha hv hx

theorem rightHNNFamily_free
    (hp : ∀ i n, Q.hnnBase (B.peak i n) = E.peak i n)
    (ht : ∀ x, B.trace (Q.hnnExpectation x) = E.trace x)
    (ha : ∀ a, jB (B.hnnBase a) = E.hnnBase (Q.hnnBase a))
    (hv : ∀ i, jB (B.hnnLetter i) = E.hnnLetter i)
    (w) (hw : IsCenteredWord (factorCenters (pairHNN B Q) (pairHNNExpect B Q)
      (fun i => (rightHNNFamily B Q E jB i).toAlgHom)) w) (hne : w ≠ []) :
    E.hnnTrace (wordValue w) = 0 := by
  apply B.hnn_family_free E Q.hnnBase hp Q.hnnExpectation Q.hnnExpectation_base
    Q.hnnExpectation_state Q.hnnExpectation_left Q.hnnExpectation_right ht
    (pairHNN B Q) (pairHNNExpect B Q) (fun i => (rightHNNFamily B Q E jB i).toAlgHom)
    Bool.not Bool.not_injective ?_ w hw hne
  intro i x hx
  cases i
  · exact B.hnn_mapped_kernel E Q.hnnBase jB ha hv hx
  · exact ⟨x,hx,rfl⟩

variable (ht : ∀ a, B.trace a = Q.trace a)
  (hpD : ∀ i n, B.hnnBase (Q.peak i n) = D.peak i n)
  (hpE : ∀ i n, Q.hnnBase (B.peak i n) = E.peak i n)
  (htD : ∀ x, Q.trace (B.hnnExpectation x) = D.trace x)
  (htE : ∀ x, B.trace (Q.hnnExpectation x) = E.trace x)
  (haQ : ∀ a, jQ (Q.hnnBase a) = D.hnnBase (B.hnnBase a))
  (hvQ : ∀ i, jQ (Q.hnnLetter i) = D.hnnLetter i)
  (haB : ∀ a, jB (B.hnnBase a) = E.hnnBase (Q.hnnBase a))
  (hvB : ∀ i, jB (B.hnnLetter i) = E.hnnLetter i)

include ht htD htE in
theorem reorder_base_moments (a : A) :
    D.hnnTrace (D.hnnBase (B.hnnBase a)) = E.hnnTrace (E.hnnBase (Q.hnnBase a)) := by
  rw [D.hnnTrace_base,E.hnnTrace_base,← htD,← htE,B.hnnExpectation_base,Q.hnnExpectation_base,ht]

def reorderEquiv : D.HNNAlgebra ≃⋆ₐ[ℂ] E.HNNAlgebra :=
  jointFreeEquiv (pairHNN B Q) (leftHNNFamily B Q D jQ) (rightHNNFamily B Q E jB)
    (fun i => (pairHNNBase B Q i).toAlgHom) (pairHNNExpect B Q)
    (D.hnnBase.comp B.hnnBase).toAlgHom (E.hnnBase.comp Q.hnnBase).toAlgHom
    (leftHNNFamily_base B Q D jQ haQ) (rightHNNFamily_base B Q E jB haB)
    (pairHNNExpect_fix B Q) (pairHNNExpect_left B Q)
    (positiveOfSquares D.hnnTrace D.hnnTrace_isState.2) (positiveOfSquares E.hnnTrace E.hnnTrace_isState.2)
    (reorder_base_moments B Q D E ht htD htE)
    (leftHNNFamily_free B Q D jQ hpD htD haQ hvQ)
    (rightHNNFamily_free B Q E jB hpE htE haB hvB)
    (leftHNNFamily_dense B Q D jQ hvQ) (rightHNNFamily_dense B Q E jB hvB)
    D.hnnTrace_faithful E.hnnTrace_faithful

theorem reorderEquiv_factor (i : Bool) (a : pairHNN B Q i) :
    reorderEquiv B Q D E jQ jB ht hpD hpE htD htE haQ hvQ haB hvB
      (leftHNNFamily B Q D jQ i a) = rightHNNFamily B Q E jB i a :=
  jointFreeEquiv_factor (pairHNN B Q) (leftHNNFamily B Q D jQ) (rightHNNFamily B Q E jB)
    (fun i => (pairHNNBase B Q i).toAlgHom) (pairHNNExpect B Q)
    (D.hnnBase.comp B.hnnBase).toAlgHom (E.hnnBase.comp Q.hnnBase).toAlgHom
    (leftHNNFamily_base B Q D jQ haQ) (rightHNNFamily_base B Q E jB haB)
    (pairHNNExpect_fix B Q) (pairHNNExpect_left B Q)
    (positiveOfSquares D.hnnTrace D.hnnTrace_isState.2) (positiveOfSquares E.hnnTrace E.hnnTrace_isState.2)
    (reorder_base_moments B Q D E ht htD htE)
    (leftHNNFamily_free B Q D jQ hpD htD haQ hvQ)
    (rightHNNFamily_free B Q E jB hpE htE haB hvB)
    (leftHNNFamily_dense B Q D jQ hvQ) (rightHNNFamily_dense B Q E jB hvB)
    D.hnnTrace_faithful E.hnnTrace_faithful i a

theorem reorderEquiv_trace (x : D.HNNAlgebra) :
    E.hnnTrace (reorderEquiv B Q D E jQ jB ht hpD hpE htD htE haQ hvQ haB hvB x) = D.hnnTrace x :=
  jointFreeEquiv_preserves (pairHNN B Q) (leftHNNFamily B Q D jQ) (rightHNNFamily B Q E jB)
    (fun i => (pairHNNBase B Q i).toAlgHom) (pairHNNExpect B Q)
    (D.hnnBase.comp B.hnnBase).toAlgHom (E.hnnBase.comp Q.hnnBase).toAlgHom
    (leftHNNFamily_base B Q D jQ haQ) (rightHNNFamily_base B Q E jB haB)
    (pairHNNExpect_fix B Q) (pairHNNExpect_left B Q)
    (positiveOfSquares D.hnnTrace D.hnnTrace_isState.2) (positiveOfSquares E.hnnTrace E.hnnTrace_isState.2)
    (reorder_base_moments B Q D E ht htD htE)
    (leftHNNFamily_free B Q D jQ hpD htD haQ hvQ)
    (rightHNNFamily_free B Q E jB hpE htE haB hvB)
    (leftHNNFamily_dense B Q D jQ hvQ) (rightHNNFamily_dense B Q E jB hvB)
    D.hnnTrace_faithful E.hnnTrace_faithful x

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

theorem hnn_reorder_of_peaks (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
    (ht : ∀ a, B.trace a = Q.trace a)
    (hpD : ∀ i n, B.hnnBase (Q.peak i n) = D.peak i n)
    (hpE : ∀ i n, Q.hnnBase (B.peak i n) = E.peak i n)
    (htD : ∀ x, Q.trace (B.hnnExpectation x) = D.trace x)
    (htE : ∀ x, B.trace (Q.hnnExpectation x) = E.trace x) :
    ∃ e : D.HNNAlgebra ≃⋆ₐ[ℂ] E.HNNAlgebra,
      (∀ a, e (D.hnnBase (B.hnnBase a)) = E.hnnBase (Q.hnnBase a)) ∧
      (∀ i, e (D.hnnBase (B.hnnLetter i)) = E.hnnLetter i) ∧
      (∀ i, e (D.hnnLetter i) = E.hnnBase (Q.hnnLetter i)) ∧
      (∀ x, E.hnnTrace (e x) = D.hnnTrace x) := by
  have haD (a : A) : D.trace (B.hnnBase a) = Q.trace a := by rw [← htD,B.hnnExpectation_base]
  have haE (a : A) : E.trace (Q.hnnBase a) = B.trace a := by rw [← htE,Q.hnnExpectation_base]
  obtain ⟨jQ,_,hjQa,hjQv,_,_,_⟩ := Q.hnn_inclusion_of_peaks D B.hnnBase hpD haD
  obtain ⟨jB,_,hjBa,hjBv,_,_,_⟩ := B.hnn_inclusion_of_peaks E Q.hnnBase hpE haE
  let e := reorderEquiv B Q D E jQ jB ht hpD hpE htD htE hjQa hjQv hjBa hjBv
  have he := reorderEquiv_factor B Q D E jQ jB ht hpD hpE htD htE hjQa hjQv hjBa hjBv
  refine ⟨e,?_,?_,?_,?_⟩
  · intro a; exact (he false (B.hnnBase a)).trans (hjBa a)
  · intro i; exact (he false (B.hnnLetter i)).trans (hjBv i)
  · intro i; exact (congrArg e (hjQv i)).symm.trans (he true (Q.hnnLetter i))
  · exact reorderEquiv_trace B Q D E jQ jB ht hpD hpE htD htE hjQa hjQv hjBa hjBv

end

end PeakingPairData

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
-- module Solutions.OAIQ115_Naimark.Naimark_CAR
attribute [-instance] _root_.OAI.NaimarkZFC.TracialStage.bond_directed _root_.OAI.NaimarkZFC.constructionIndex_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra
section

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (ψ : CAR →⋆ₐ[ℂ] B) (φ : B →⋆ₐ[ℂ] A) (hφ : Function.Injective φ)
  (f g : A →L[ℂ] ℂ) (hp : Peaks (fun n => φ (ψ (carPeak n))) f)
  (hg : IsPureState (restrictState φ g)) (hgs : IsState g)
  (hu : PureUEP φ) (γ : B ≃⋆ₐ[ℂ] B)
  (he : restrictState γ.toStarAlgHom (restrictState φ g) = restrictState φ f)

def homogeneousCARPeakPair (τ : A →ₚ[ℂ] ℂ) (htr : IsTracialPositive τ)
    (hn : τ 1 = 1) (hfaith : ∀ a, τ (star a*a) = 0 → a = 0) :
    PeakingPairData A where
  trace := τ
  tracial := htr
  normalized := hn
  faithful := hfaith
  peak i n := if i then φ (γ (ψ (carPeak n))) else φ (ψ (carPeak n))
  state i := if i then g else f
  peaks i := by
    cases i
    · exact hp
    · exact homogeneousCARPeak_peaks ψ φ hφ f g hp hg hgs hu γ he
  peak_zero i := by cases i <;> simp only [Bool.false_eq_true, ↓reduceIte, carPeak_zero, map_one]
  atom_positive i n := by
    have htrace (i : Bool) (n : ℕ) :
        τ (if i then φ (γ (ψ (carPeak n))) else φ (ψ (carPeak n))) = (2:ℂ)⁻¹^n := by
      cases i
      · exact carPeak_ambientTrace (φ.comp ψ) τ.toLinearMap hn htr n
      · exact carPeak_ambientTrace (φ.comp (γ.toStarAlgHom.comp ψ)) τ.toLinearMap hn htr n
    change 0 < (τ ((if i then φ (γ (ψ (carPeak n))) else φ (ψ (carPeak n))) -
      (if i then φ (γ (ψ (carPeak (n+1)))) else φ (ψ (carPeak (n+1)))))).re
    rw [map_sub,htrace,htrace,Complex.sub_re]
    rw [complexInvTwoPow_re,complexInvTwoPow_re,pow_succ]
    have h : (0:ℝ) < (1/2:ℝ)^n := pow_pos (by norm_num) n
    linarith
  trace_null i := by
    have htrace (n : ℕ) :
        τ (if i then φ (γ (ψ (carPeak n))) else φ (ψ (carPeak n))) = (2:ℂ)⁻¹^n := by
      cases i
      · exact carPeak_ambientTrace (φ.comp ψ) τ.toLinearMap hn htr n
      · exact carPeak_ambientTrace (φ.comp (γ.toStarAlgHom.comp ψ)) τ.toLinearMap hn htr n
    simp_rw [htrace]
    have hh : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [complexInvTwoPow_re] using hh
  matched i n := by
    cases i
    · rfl
    · change τ (φ (γ (ψ (carPeak n)))) = τ (φ (ψ (carPeak n)))
      exact (carPeak_ambientTrace (φ.comp (γ.toStarAlgHom.comp ψ)) τ.toLinearMap hn htr n).trans
        (carPeak_ambientTrace (φ.comp ψ) τ.toLinearMap hn htr n).symm

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Stages
attribute [-instance] _root_.OAI.NaimarkZFC.TracialStage.bond_directed _root_.OAI.NaimarkZFC.TracialStage.bond_isometric _root_.OAI.NaimarkZFC.constructionIndex_nonempty
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
namespace TracialStage
attribute [local instance 2000] PeakingPairData.hnnCStar PeakingPairData.hnnOrder
  PeakingPairData.hnnStarOrder
variable (X : TracialStage)

variable (Q : PeakingPairData X) (hs : Q.Separated)
  (htrace : ∀ a : X, Q.trace a = X.trace a)

def hnn : TracialStage where
  carrier := Q.HNNAlgebra
  cstar := inferInstance
  order := inferInstance
  starOrder := inferInstance
  simple := Q.hnn_simple hs X.simple
  trace := Q.hnnTrace
  traceState := Q.hnnTrace_isState
  tracial := Q.hnnTrace_tracial
  base := Q.hnnBase.comp X.base
  base_injective := Q.hnnBase_injective.comp X.base_injective
  baseUEP := X.baseUEP.comp (fun f hf => Q.hnn_unique hs X.simple f hf)

def hnnHom : Hom X (hnn X Q hs) where
  map := Q.hnnBase
  injective := Q.hnnBase_injective
  trace_map a := (Q.hnnTrace_base a).trans (htrace a)
  base_map _ := rfl
  uep f hf := Q.hnn_unique hs X.simple f hf

include htrace in
lemma hnn_reference (hf : Q.state false = X.reference) :
    restrictState Q.hnnBase (hnn X Q hs).reference = Q.state false := by
  rw [hf]
  exact (hnnHom X Q hs htrace).reference_map

include htrace in

theorem hnn_reference_join (f : X →L[ℂ] ℂ) (hf : IsPureState f)
    (h0 : Q.state false = X.reference) (h1 : Q.state true = f) :
    ∃ F : hnn X Q hs →L[ℂ] ℂ, ∃ hF : IsPureState F,
      restrictState Q.hnnBase F = f ∧
      PureStateEquivalent (hnn X Q hs).reference (hnn X Q hs).reference_spec.1 F hF := by
  obtain ⟨F,hF,hr,_⟩ := (Q.hnn_unique hs X.simple f hf).exists_unique_pure
    Q.hnnBase_injective hf
  refine ⟨F,hF,hr,?_⟩
  exact Q.hnn_join hs X.simple _ _ (hnn X Q hs).reference_spec.1 hF
    (hnn_reference X Q hs htrace h0) (hr.trans h1.symm)

end TracialStage

open scoped InnerProductSpace
namespace KOS

@[simp] lemma projectionCutoff_one : projectionCutoff 1 = 1 := by norm_num [projectionCutoff]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def projectionTruncate (a : A) : A := cfc projectionCutoff a

lemma projectionTruncate_nonneg (a : A) : 0 ≤ projectionTruncate a :=
  cfc_nonneg (fun t _ => projectionCutoff_nonneg t)

lemma projectionTruncate_le_one (a : A) : projectionTruncate a ≤ 1 :=
  cfc_le_one _ _ (fun t _ => projectionCutoff_le_one t)

omit [PartialOrder A] [StarOrderedRing A] in
lemma projectionTruncate_relation (a : A) (ha : IsSelfAdjoint a) :
    projectionTruncate a * (a^2 + (a-1)^2) = a^2 := by
  have hp : cfc (fun t : ℝ => t^2 + (t-1)^2) a = a^2 + (a-1)^2 := by
    rw [cfc_add a (fun t : ℝ => t^2) (fun t => (t-1)^2), cfc_pow_id (R := ℝ) a 2 ha, cfc_pow _ _ a,
      cfc_sub _ _ a, cfc_id' ℝ a ha, cfc_const_one ℝ a]
  rw [projectionTruncate, ← hp, ← cfc_mul _ _ a continuous_projectionCutoff.continuousOn (by fun_prop)]
  have he : (fun t => projectionCutoff t * (t^2 + (t-1)^2)) = fun t : ℝ => t^2 := by
    funext t
    exact div_mul_cancel₀ _ (projectionCutoff_den_pos t).ne'
  rw [he,cfc_pow_id (R := ℝ) a 2 ha]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma projectionTruncate_apply (a : A) (ha : IsSelfAdjoint a)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
    (hv : π a (π a v) = π a v) :
    π (projectionTruncate a) v = π a v := by
  have hd : π (a^2+(a-1)^2) v = v := by
    simp only [pow_two,map_add,map_mul,map_sub,map_one,add_apply,mul_apply_eq_comp,
      sub_apply,one_apply_eq_self,hv]
    abel
  calc
    π (projectionTruncate a) v = π (projectionTruncate a) (π (a^2+(a-1)^2) v) := by rw [hd]
    _ = π (projectionTruncate a * (a^2+(a-1)^2)) v := by rw [map_mul,mul_apply_eq_comp]
    _ = π (a^2) v := by rw [projectionTruncate_relation a ha]
    _ = π a v := by simpa only [pow_two,map_mul,mul_apply_eq_comp] using hv

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_projection_positive_lift
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (hPM : ∀ v ∈ M, P v ∈ M) :
    ∃ a : A, 0 ≤ a ∧ a ≤ 1 ∧ ∀ v ∈ M, π a v = P v := by
  obtain ⟨b,hb,_,hbM⟩ := irreducible_selfAdjoint_transitivity π hπ M P hP.isSelfAdjoint
  have hPP (v : H) : P (P v) = P v := by
    exact congrArg (fun T : H →L[ℂ] H => T v) hP.isIdempotentElem.eq
  refine ⟨projectionTruncate b,projectionTruncate_nonneg b,projectionTruncate_le_one b,?_⟩
  intro v hv
  have hbb : π b (π b v) = π b v := by
    rw [hbM v hv,hbM (P v) (hPM v hv),hPP]
  exact (projectionTruncate_apply b hb (irreducibleUnitalRepresentation π hπ) v hbb).trans (hbM v hv)

theorem approximate_gram_positive_lift
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    {ι : Type*} [Fintype ι] (x : ι → H) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ι → H,
      (∀ i j, ⟪x i,y j⟫_ℂ = 0) →
      (∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ) →
      ∃ a : A, 0 ≤ a ∧ a ≤ 1 ∧
        (∀ i, ‖π a (x i-y i)-(x i-y i)‖ < ε) ∧
        (∀ i, ‖π a (x i+y i)‖ < ε) := by
  obtain ⟨δ,hδ,hgeom⟩ := approximate_gram_projection x ε hε
  refine ⟨δ,hδ,fun y ho hg => ?_⟩
  obtain ⟨P,hP,hPM,hd,hs⟩ := hgeom y ho hg
  let M := Submodule.span ℂ (Set.range x ∪ Set.range y)
  let : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ
    ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨a,ha,ha1,hav⟩ := finite_projection_positive_lift π hπ M P hP (fun v _ => hPM v)
  have hx (i : ι) : x i ∈ M := Submodule.subset_span (Or.inl (Set.mem_range_self i))
  have hy (i : ι) : y i ∈ M := Submodule.subset_span (Or.inr (Set.mem_range_self i))
  refine ⟨a,ha,ha1,fun i => ?_,fun i => ?_⟩
  · rw [hav _ (M.sub_mem (hx i) (hy i))]
    exact hd i
  · rw [hav _ (M.add_mem (hx i) (hy i))]
    exact hs i

end KOS

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

theorem orthogonal_row_interchange_approx
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (ξ : H) (hξ : ‖ξ‖ = 1)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hfix : ‖π (rowAverage x 1) ξ-ξ‖ ≤ r/8) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : H, ‖η‖ = 1 →
      (∀ i j, ⟪π (star (x i)) ξ,π (star (x j)) η⟫_ℂ = 0) →
      (∀ i j, ‖⟪π (star (x i)) ξ,π (star (x j)) ξ⟫_ℂ-
        ⟪π (star (x i)) η,π (star (x j)) η⟫_ℂ‖ ≤ δ) →
      ‖π (rowAverage x 1) η-η‖ ≤ r/8 →
      ∃ (a : A) (u : unitary A), 0 ≤ a ∧ a ≤ 1 ∧ π u ξ = η ∧
        ∀ b : A, ‖b*(u:A)-(u:A)*b‖ ≤ 192*‖b‖*r +
          4*‖b*rowAverage x a-rowAverage x a*b‖ := by
  let C : ℝ := ∑ i, ‖x i‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let ε := r/(16*(C+1))
  have hε : 0 < ε := div_pos hr (by positivity)
  obtain ⟨δ,hδ,hgeom⟩ := approximate_gram_positive_lift π hπ
    (fun i => π (star (x i)) ξ) ε hε
  refine ⟨δ,hδ,fun η hη ho hg hb => ?_⟩
  obtain ⟨a,ha,ha1,hd,hs⟩ := hgeom (fun i => π (star (x i)) η) ho hg
  have he := rowAverage_pair_error_approx π hπ x a ξ η ε
    (fun i => (hd i).le) (fun i => (hs i).le)
  have hc : 4*C*ε ≤ r/4 := by
    dsimp [ε]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have heq : 4*C*(r/(16*(C+1)))*4 = r*(C/(C+1)) := by field_simp; ring
    rw [heq]
    exact mul_le_of_le_one_right hr.le ((div_le_one (by positivity)).mpr (by linarith))
  have herr : 2*(‖π (rowAverage x a) (ξ-η)-(ξ-η)‖ +
      ‖π (rowAverage x a) (ξ+η)‖) ≤ r := by
    change _ ≤ 2*C*ε+_+_ at he
    linarith
  obtain ⟨u,hu,hcomm⟩ := corrected_projectionSwitch π hπ ξ η hξ hη
    (rowAverage x a) (rowAverage_selfAdjoint x a (IsSelfAdjoint.of_nonneg ha)) r herr hr1
  exact ⟨a,u,ha,ha1,hu,hcomm⟩

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

theorem row_controlled_matching
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (hi : Function.Injective π)
    (hno : ∀ a : A, IsCompactOperator (π a) → π a = 0)
    (x : ι → A) (ξ : H) (hξ : ‖ξ‖ = 1) (hfix : π (rowAverage x 1) ξ = ξ)
    (F : Finset A) (c : ℝ)
    (hcentral : ∀ b ∈ F, ∀ a : A, 0 ≤ a → a ≤ 1 →
      ‖b*rowAverage x a-rowAverage x a*b‖ ≤ c)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : H, ‖η‖ = 1 →
      (∀ a ∈ rowFrameTests x,
        ‖vectorFunctional π ξ a-vectorFunctional π η a‖ < δ) →
      ∃ u : unitary A, π u ξ = η ∧ ∀ b ∈ F,
        ‖b*(u:A)-(u:A)*b‖ ≤ 384*‖b‖*r+8*c := by
  have hone := irreducible_map_one π hπ
  have hξd : ‖π (rowAverage x 1) ξ-ξ‖ ≤ r/8 := by rw [hfix,sub_self,norm_zero]; positivity
  obtain ⟨δ₁,hδ₁,hmatch₁⟩ := orthogonal_row_interchange_approx π hπ x ξ hξ r hr hr1 hξd
  let q : ℝ := (r/16)^2
  have hq : 0 < q := sq_pos_of_pos (div_pos hr (by norm_num))
  let δ : ℝ := min (δ₁/2) q
  have hδ : 0 < δ := lt_min (by positivity) hq
  refine ⟨δ,hδ,fun η hη hclose => ?_⟩
  have hηq : ‖vectorFunctional π η (rowDefectTest x)‖ ≤ q := by
    have hh := hclose _ (defect_mem_rowFrameTests x)
    rw [row_defect_zero π hone x ξ hfix,zero_sub,norm_neg] at hh
    exact hh.le.trans (min_le_right _ _)
  have hηd : ‖π (rowAverage x 1) η-η‖ ≤ r/16 :=
    row_defect_bound π hone x η (r/16) (by positivity) hηq
  obtain ⟨δ₂,hδ₂,hmatch₂⟩ := orthogonal_row_interchange_approx π hπ x η hη r hr hr1
    (hηd.trans (by linarith))
  let α : ℝ := min (δ₁/2) (min δ₂ q)
  have hα : 0 < α := lt_min (by positivity) (lt_min hδ₂ hq)
  obtain ⟨hpη,_⟩ := irreducible_vector_pure_equivalent π hπ η hη
  obtain ⟨ζ,hζ,ho₁,ho₂,htest⟩ := third_vector_two_frames π hπ hi hno x ξ η
    (vectorFunctional π η) hpη (rowFrameTests x) α hα
  have htest' (a : A) (ha : a ∈ rowFrameTests x) :
      ‖vectorFunctional π η a-vectorFunctional π ζ a‖ < α := by
    rw [norm_sub_rev]
    exact htest a ha
  have hζq : ‖vectorFunctional π ζ (rowDefectTest x)‖ ≤ (r/8)^2 := by
    have hb := norm_sub_le_norm_sub_add_norm_sub
      (vectorFunctional π ζ (rowDefectTest x)) (vectorFunctional π η (rowDefectTest x)) 0
    simp only [sub_zero] at hb
    have hh := (htest _ (defect_mem_rowFrameTests x)).le
    have hαq : α ≤ q := (min_le_right _ _).trans (min_le_right _ _)
    change ‖vectorFunctional π ζ (rowDefectTest x)-vectorFunctional π η (rowDefectTest x)‖ ≤ α at hh
    change ‖vectorFunctional π η (rowDefectTest x)‖ ≤ (r/16)^2 at hηq
    change α ≤ (r/16)^2 at hαq
    nlinarith [sq_nonneg r]
  have hζd : ‖π (rowAverage x 1) ζ-ζ‖ ≤ r/8 :=
    row_defect_bound π hone x ζ (r/8) (by positivity) hζq
  have hg₁ (i j : ι) : ‖⟪π (star (x i)) ξ,π (star (x j)) ξ⟫_ℂ-
      ⟪π (star (x i)) ζ,π (star (x j)) ζ⟫_ℂ‖ ≤ δ₁ := by
    rw [row_frame_coefficient,row_frame_coefficient]
    have hh := hclose _ (gram_mem_rowFrameTests x i j)
    have hh' := htest' _ (gram_mem_rowFrameTests x i j)
    have hb := norm_sub_le_norm_sub_add_norm_sub
      (vectorFunctional π ξ (x i*star (x j))) (vectorFunctional π η (x i*star (x j)))
      (vectorFunctional π ζ (x i*star (x j)))
    have hd : δ ≤ δ₁/2 := min_le_left _ _
    have ha : α ≤ δ₁/2 := min_le_left _ _
    linarith
  have hg₂ (i j : ι) : ‖⟪π (star (x i)) η,π (star (x j)) η⟫_ℂ-
      ⟪π (star (x i)) ζ,π (star (x j)) ζ⟫_ℂ‖ ≤ δ₂ := by
    rw [row_frame_coefficient,row_frame_coefficient]
    exact (htest' _ (gram_mem_rowFrameTests x i j)).le.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨a₁,u₁,ha₁,ha₁',hu₁,hc₁⟩ := hmatch₁ ζ hζ ho₁ hg₁ hζd
  obtain ⟨a₂,u₂,ha₂,ha₂',hu₂,hc₂⟩ := hmatch₂ ζ hζ ho₂ hg₂ hζd
  refine ⟨star u₂*u₁,?_,fun b hb => ?_⟩
  · change π (star (u₂:A)*(u₁:A)) ξ = η
    rw [map_mul,mul_apply_eq_comp,hu₁,← hu₂,← mul_apply_eq_comp,← map_mul,
      u₂.property.1,hone,one_apply_eq_self]
  · refine (unitary_commutator_sum (star u₂) u₁ b).trans ?_
    change ‖b*star (u₂:A)-star (u₂:A)*b‖ + ‖b*(u₁:A)-(u₁:A)*b‖ ≤ _
    rw [unitary_commutator_star]
    have h₁ := hc₁ b
    have h₂ := hc₂ b
    have h₁' := hcentral b hb a₁ ha₁ ha₁'
    have h₂' := hcentral b hb a₂ ha₂ ha₂'
    linarith

end KOS

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Homogeneity
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
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

theorem sameClassControl_of_nearCentralRows (hA : IsSimpleCStar A)
    (hinf : ¬ FiniteDimensional ℂ A) (hrow : NearCentralRows (A := A)) :
    SameClassControl (A := A) := by
  classical
  intro f hf F ε hε
  let P := positiveOfSquares f hf.1.2
  let π := pureGNS f hf
  let ξ := gnsVector P
  have hπ : IsIrreducible π := pure_gns_irreducible f hf.1 hf
  have hi : Function.Injective π := simple_nonzeroStarHom_injective hA π hπ.1
  have hno : ∀ a : A, IsCompactOperator (π a) → π a = 0 :=
    simple_infinite_no_compacts hA hinf π hπ
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one P ((isState_iff f).mp hf.1).1
  have hcoeff (a : A) : vectorFunctional π ξ a = f a := gnsVector_coefficient P a
  let B : ℝ := ∑ b ∈ F, ‖b‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let r : ℝ := min 1 (ε/(1536*(B+1)))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hε (by positivity))
  have hr1 : r ≤ 1 := min_le_left _ _
  obtain ⟨n,x,hfix,hcentral⟩ := hrow f hf F (ε/32) (by positivity)
  obtain ⟨δ,hδ,hmatch⟩ := row_controlled_matching π hπ hi hno x ξ hξ hfix
    F (ε/32) hcentral r hr hr1
  refine ⟨rowFrameTests x,δ,hδ,fun g hg he hclose => ?_⟩
  obtain ⟨η,hη,hηcoeff⟩ := equivalent_pure_coefficient_vector
    (StarAlgHom.id ℂ A) f g hf hg he π ξ hcoeff
  change ∀ a : A, ⟪η,π a η⟫_ℂ = g a at hηcoeff
  have hcl (a : A) (ha : a ∈ rowFrameTests x) :
      ‖vectorFunctional π ξ a-vectorFunctional π η a‖ < δ := by
    rw [hcoeff]
    change ‖f a-⟪η,π a η⟫_ℂ‖ < δ
    rw [hηcoeff]
    simpa only [dist_eq_norm] using hclose a ha
  obtain ⟨u,hu,hcomm⟩ := hmatch η hη hcl
  refine ⟨(Unitary.conjStarAlgAut ℂ A u).symm,fun a ha => ?_,?_⟩
  · rw [norm_inverse_inner_displacement]
    have haB : ‖a‖ ≤ B := Finset.single_le_sum (fun b _ => norm_nonneg b) ha
    have hr' : r ≤ ε/(1536*(B+1)) := min_le_right _ _
    have hrB : r*(1536*(B+1)) ≤ ε := (le_div_iff₀ (by positivity)).mp hr'
    have hb : 384*‖a‖*r ≤ ε/4 := by nlinarith [mul_le_mul_of_nonneg_right haB hr.le]
    exact (hcomm a ha).trans_lt (by linarith)
  · ext a
    change f (star (u:A)*a*(u:A)) = g a
    rw [← hcoeff]
    change ⟪ξ,π (star (u:A)*a*(u:A)) ξ⟫_ℂ = g a
    simp only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
    rw [hu]
    exact hηcoeff a

theorem homogeneity_of_nearCentralRows [TopologicalSpace.SeparableSpace A]
    (hA : IsSimpleCStar A) (hinf : ¬ FiniteDimensional ℂ A)
    (hrow : NearCentralRows (A := A))
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a :=
  homogeneity_of_sameClassControl (sameClassControl_of_nearCentralRows hA hinf hrow)
    hA f g hf hg

end KOS

open scoped InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A C X : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [partialOrderC : PartialOrder C] [starOrderedRingC : StarOrderedRing C]
  [CStarAlgebra X] [PartialOrder X] [StarOrderedRing X]

theorem hnn_reorder_via_equivs (B Q : PeakingPairData A)
    (R : PeakingPairData C) (T : PeakingPairData X)
    (eB : B.HNNAlgebra ≃⋆ₐ[ℂ] C) (eQ : Q.HNNAlgebra ≃⋆ₐ[ℂ] X)
    (ht : ∀ a, B.trace a = Q.trace a)
    (hpR : ∀ i n, eB (B.hnnBase (Q.peak i n)) = R.peak i n)
    (hpT : ∀ i n, eQ (Q.hnnBase (B.peak i n)) = T.peak i n)
    (htR : ∀ x, R.trace (eB x) = B.hnnTrace x)
    (htT : ∀ x, T.trace (eQ x) = Q.hnnTrace x) :
    ∃ e : R.HNNAlgebra ≃⋆ₐ[ℂ] T.HNNAlgebra,
      (∀ a, e (R.hnnBase (eB (B.hnnBase a))) = T.hnnBase (eQ (Q.hnnBase a))) ∧
      (∀ i, e (R.hnnBase (eB (B.hnnLetter i))) = T.hnnLetter i) ∧
      (∀ i, e (R.hnnLetter i) = T.hnnBase (eQ (Q.hnnLetter i))) ∧
      (∀ x, T.hnnTrace (e x) = R.hnnTrace x) := by
  let D := R.pullback eB.toStarAlgHom eB.injective (fun i n => B.hnnBase (Q.peak i n)) hpR
  let E := T.pullback eQ.toStarAlgHom eQ.injective (fun i n => Q.hnnBase (B.peak i n)) hpT
  have htD (x : B.HNNAlgebra) : Q.trace (B.hnnExpectation x) = D.trace x := by
    change Q.trace (B.hnnExpectation x) = R.trace (eB x)
    rw [htR,← ht,B.hnnTrace_expectation]
  have htE (x : Q.HNNAlgebra) : B.trace (Q.hnnExpectation x) = E.trace x := by
    change B.trace (Q.hnnExpectation x) = T.trace (eQ x)
    rw [htT,ht,Q.hnnTrace_expectation]
  obtain ⟨s,hsb,hsB,hsQ,hst⟩ := B.hnn_reorder_of_peaks Q D E ht
    (fun _ _ => rfl) (fun _ _ => rfl) htD htE
  obtain ⟨r,hrb,hrw,hrt,_⟩ := D.hnn_equiv_of_peaks R eB hpR (fun _ => rfl)
  obtain ⟨t,htb,htw,htt,_⟩ := E.hnn_equiv_of_peaks T eQ hpT (fun _ => rfl)
  let e := (r.symm.trans s).trans t
  have her (x : D.HNNAlgebra) : e (r x) = t (s x) := by simp [e]
  refine ⟨e,?_,?_,?_,?_⟩
  · intro a
    rw [← hrb,her,hsb,htb]
  · intro i
    rw [← hrb,her,hsB,htw]
  · intro i
    rw [← hrw,her,hsQ,htb]
  · intro x
    obtain ⟨x,rfl⟩ := r.surjective x
    change T.hnnTrace (e (r x)) = R.hnnTrace (r x)
    rw [her,htt,hst,hrt]

end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {S R T U A : Type}
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U] [CStarAlgebra A]

theorem hnn_reorder_ambient_target (B K : PeakingPairData S)
    (D : PeakingPairData R) (E : PeakingPairData T)
    (eP : B.HNNAlgebra ≃⋆ₐ[ℂ] R) (eQ : K.HNNAlgebra ≃⋆ₐ[ℂ] T)
    (eR : D.HNNAlgebra ≃⋆ₐ[ℂ] U)
    (ht : ∀ a, B.trace a = K.trace a)
    (hpD : ∀ i n, eP (B.hnnBase (K.peak i n)) = D.peak i n)
    (hpE : ∀ i n, eQ (K.hnnBase (B.peak i n)) = E.peak i n)
    (htD : ∀ x, D.trace (eP x) = B.hnnTrace x)
    (htE : ∀ x, E.trace (eQ x) = K.hnnTrace x)
    (b : S →⋆ₐ[ℂ] A) (r : R →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (u : U →⋆ₐ[ℂ] A)
    (hu : Function.Injective u) (iTU : T →⋆ₐ[ℂ] U) (hiTU : ∀ a, u (iTU a) = t a)
    (z w : Bool → A)
    (hePb : ∀ a, r (eP (B.hnnBase a)) = b a)
    (hePw : ∀ i, r (eP (B.hnnLetter i)) = z i)
    (heQb : ∀ a, t (eQ (K.hnnBase a)) = b a)
    (heQw : ∀ i, t (eQ (K.hnnLetter i)) = w i)
    (heRb : ∀ a, u (eR (D.hnnBase a)) = r a)
    (heRw : ∀ i, u (eR (D.hnnLetter i)) = w i)
    (g : A →L[ℂ] ℂ) (heRt : ∀ x, g (u (eR x)) = D.hnnTrace x) :
    ∃ e : E.HNNAlgebra ≃⋆ₐ[ℂ] U,
      (∀ a, u (e (E.hnnBase a)) = t a) ∧
      (∀ i, u (e (E.hnnLetter i)) = z i) ∧
      (∀ x, g (u (e x)) = E.hnnTrace x) := by
  obtain ⟨s,hsb,hsP,hsQ,hst⟩ := B.hnn_reorder_via_equivs K D E eP eQ ht hpD hpE htD htE
  let e : E.HNNAlgebra ≃⋆ₐ[ℂ] U := s.symm.trans eR
  have hes (x : D.HNNAlgebra) : e (s x) = eR x := by simp [e]
  have hsP' (i : Bool) : e (E.hnnLetter i) = eR (D.hnnBase (eP (B.hnnLetter i))) := by
    rw [← hsP,hes]
  have hsQ' (i : Bool) : e (E.hnnBase (eQ (K.hnnLetter i))) = eR (D.hnnLetter i) := by
    rw [← hsQ,hes]
  have hsb' (a : S) : e (E.hnnBase (eQ (K.hnnBase a))) =
      eR (D.hnnBase (eP (B.hnnBase a))) := by rw [← hsb,hes]
  let f : K.HNNAlgebra →⋆ₐ[ℂ] U := (e.toStarAlgHom.comp E.hnnBase).comp eQ.toStarAlgHom
  let h : K.HNNAlgebra →⋆ₐ[ℂ] U := iTU.comp eQ.toStarAlgHom
  have hfg : f = h := by
    apply K.hnn_hom_ext f h
    · intro a
      apply hu
      change u (e (E.hnnBase (eQ (K.hnnBase a)))) = u (iTU (eQ (K.hnnBase a)))
      rw [hsb',heRb,hePb,hiTU,heQb]
    · intro i
      apply hu
      change u (e (E.hnnBase (eQ (K.hnnLetter i)))) = u (iTU (eQ (K.hnnLetter i)))
      rw [hsQ',heRw,hiTU,heQw]
  refine ⟨e,?_,?_,?_⟩
  · intro a
    obtain ⟨c,hc⟩ := eQ.surjective a
    change eQ c = a at hc
    have hh := congrArg (fun F : K.HNNAlgebra →⋆ₐ[ℂ] U => u (F c)) hfg
    change u (e (E.hnnBase (eQ c))) = u (iTU (eQ c)) at hh
    rw [hiTU,hc] at hh
    exact hh
  · intro i
    rw [hsP',heRb,hePw]
  · intro x
    obtain ⟨c,hc⟩ := s.surjective x
    change s c = x at hc
    have hh : g (u (e (s c))) = E.hnnTrace (s c) := by rw [hes,heRt,hst]
    simpa only [hc] using hh

end

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {S R T U A : Type}
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra T] [PartialOrder T] [StarOrderedRing T]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U] [CStarAlgebra A]

theorem hnn_reorder_from_ambient_data (B K : PeakingPairData S)
    (D : PeakingPairData R) (E : PeakingPairData T)
    (eP : B.HNNAlgebra ≃⋆ₐ[ℂ] R) (eQ : K.HNNAlgebra ≃⋆ₐ[ℂ] T)
    (eR : D.HNNAlgebra ≃⋆ₐ[ℂ] U)
    (b : S →⋆ₐ[ℂ] A) (r : R →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (u : U →⋆ₐ[ℂ] A)
    (hr : Function.Injective r) (ht : Function.Injective t) (hu : Function.Injective u)
    (iTU : T →⋆ₐ[ℂ] U) (hiTU : ∀ a, u (iTU a) = t a)
    (hpD : ∀ i n, b (K.peak i n) = r (D.peak i n))
    (hpE : ∀ i n, b (B.peak i n) = t (E.peak i n))
    (g : A →L[ℂ] ℂ)
    (hBt : ∀ a, B.trace a = g (b a)) (hKt : ∀ a, K.trace a = g (b a))
    (hDt : ∀ a, D.trace a = g (r a)) (hEt : ∀ a, E.trace a = g (t a))
    (z w : Bool → A)
    (hePb : ∀ a, r (eP (B.hnnBase a)) = b a)
    (hePw : ∀ i, r (eP (B.hnnLetter i)) = z i)
    (heQb : ∀ a, t (eQ (K.hnnBase a)) = b a)
    (heQw : ∀ i, t (eQ (K.hnnLetter i)) = w i)
    (heRb : ∀ a, u (eR (D.hnnBase a)) = r a)
    (heRw : ∀ i, u (eR (D.hnnLetter i)) = w i)
    (hePt : ∀ x, g (r (eP x)) = B.hnnTrace x)
    (heQt : ∀ x, g (t (eQ x)) = K.hnnTrace x)
    (heRt : ∀ x, g (u (eR x)) = D.hnnTrace x) :
    ∃ e : E.HNNAlgebra ≃⋆ₐ[ℂ] U,
      (∀ a, u (e (E.hnnBase a)) = t a) ∧
      (∀ i, u (e (E.hnnLetter i)) = z i) ∧
      (∀ x, g (u (e x)) = E.hnnTrace x) := by
  have hBK (a : S) : B.trace a = K.trace a := (hBt a).trans (hKt a).symm
  have hD (i : Bool) (n : ℕ) : eP (B.hnnBase (K.peak i n)) = D.peak i n :=
    hr ((hePb _).trans (hpD i n))
  have hE (i : Bool) (n : ℕ) : eQ (K.hnnBase (B.peak i n)) = E.peak i n :=
    ht ((heQb _).trans (hpE i n))
  exact B.hnn_reorder_ambient_target K D E eP eQ eR hBK hD hE
    (fun x => (hDt _).trans (hePt x)) (fun x => (hEt _).trans (heQt x))
    b r t u hu iTU hiTU z w hePb hePw heQb heQw heRb heRw g heRt

end

end PeakingPairData

open Topology
namespace PeakingPairData

section
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {S R T U A : Type}
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma HNNAmbientPresentation.swap (P Q : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (r : R →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (u : U →⋆ₐ[ℂ] A)
    (hr : Function.Injective r) (ht : Function.Injective t) (hu : Function.Injective u)
    (iTU : T →⋆ₐ[ℂ] U) (hiTU : ∀ a, u (iTU a) = t a)
    (z w : Bool → A) (htrace : ∀ a, P.trace a = Q.trace a)
    (hP : P.HNNAmbientPresentation b r z)
    (hQ : Q.HNNAmbientPresentation b t w)
    (hR : Q.HNNAmbientPresentation r u w)
    (E : PeakingPairData T) (ep : ∀ i n, t (E.peak i n) = P.peak i n)
    (et : ∀ a, E.trace a = P.trace (t a)) : P.HNNAmbientPresentation t u z := by
  obtain ⟨B,pb,pt,eP,hePb,hePw,hePt⟩ := hP
  obtain ⟨K,qb,qt,eQ,heQb,heQw,heQt⟩ := hQ
  obtain ⟨D,qd,qdt,eR,heRb,heRw,heRt⟩ := hR
  refine ⟨E,ep,et,?_⟩
  exact B.hnn_reorder_from_ambient_data K D E eP eQ eR
    b r t u hr ht hu iTU hiTU
    (fun i n => (qb i n).trans (qd i n).symm)
    (fun i n => (pb i n).trans (ep i n).symm)
    (positiveCLM P.trace) pt
    (fun a => (qt a).trans (htrace _).symm)
    (fun a => (qdt a).trans (htrace _).symm) et
    z w hePb hePw heQb heQw heRb heRw
    hePt (fun x => (htrace _).trans (heQt x)) (fun x => (htrace _).trans (heRt x))

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

theorem ambient_presentation_swap (P Q : PeakingPairData A)
    (S R T U : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (R : Set A)]
    [IsClosed (T : Set A)] [IsClosed (U : Set A)]
    (hTU : T ≤ U)
    (pS : ∀ i n, P.peak i n ∈ S) (qS : ∀ i n, Q.peak i n ∈ S)
    (pT : ∀ i n, P.peak i n ∈ T) (qR : ∀ i n, Q.peak i n ∈ R)
    (z w : A) (ht : ∀ a, P.trace a = Q.trace a)
    (hP : P.AmbientPresentation S pS z R)
    (hQ : Q.AmbientPresentation S qS w T)
    (hR : Q.AmbientPresentation R qR w U) :
    P.AmbientPresentation T pT z U :=
  HNNAmbientPresentation.swap P Q S.subtype R.subtype T.subtype U.subtype
    Subtype.val_injective Subtype.val_injective Subtype.val_injective
    (StarSubalgebra.inclusion hTU) (fun _ => rfl) (starPair z) (starPair w)
    ht hP hQ hR (P.onSubalgebra T pT) (fun _ _ => rfl) (fun _ => rfl)

end

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder

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

include hjS hpeak hchrono hinactive htrace hdep hja in
lemma omitted_model_successor (k : Ordinal.{u}) (hkδ : k < δ)
    (hi : (Q j).OmittedModel base v j S k) : (Q j).OmittedModel base v j S (k+1) := by
  let O := omittedAlgebra base v j S
  let R := omittedAlgebra base v (j+1) S
  let pO (β : Ordinal.{u}) (i : Bool) (n : ℕ) : (Q j).peak i n ∈ O β :=
    omittedAlgebra_contains_initial base v j S β (hpeak j hja i n)
  change (Q j).AmbientPresentation (O k) (pO k) (v j) (R k) at hi
  change (Q j).AmbientPresentation (O (k+1)) (pO (k+1)) (v j) (R (k+1))
  have inert (hO : O (k+1) = O k) (hR : R (k+1) = R k) :
      (Q j).AmbientPresentation (O (k+1)) (pO (k+1)) (v j) (R (k+1)) :=
    AmbientPresentation.congr (Q j) _ _ _ _ (pO k) (pO (k+1)) (v j) hO.symm hR.symm hi
  by_cases hkS : k ∈ S
  · by_cases hkj : k < j
    · exact inert (omittedAlgebra_succ_of_lt base v j S k hkj)
        (omittedAlgebra_succ_of_lt base v (j+1) S k (hkj.trans_le le_self_add))
    · have hjk : j < k := lt_of_le_of_ne (le_of_not_gt hkj) (fun e => hjS (e ▸ hkS))
      by_cases hka : k ∈ active
      · have qO := hdep k hkδ hkS hka hjk
        have hOR : O k ≤ R k := omittedAlgebra_base_mono base v S k le_self_add
        have qR : ∀ i n, (Q k).peak i n ∈ R k := fun i n => hOR (qO i n)
        have hOX : O k ≤ generatedFamily base v (Set.Iio k) :=
          omittedAlgebra_le_chronological base v j S k hjk.le
        have hRX : R k ≤ generatedFamily base v (Set.Iio k) :=
          omittedAlgebra_le_chronological base v (j+1) S k (Order.add_one_le_iff.mpr hjk)
        have Hq := ambient_presentation_inherited (Q k) _ _ (O k)
          (hpeak k hka) qO (v k) hOX (hchrono k hkδ hka)
        have Hr := ambient_presentation_inherited (Q k) _ _ (R k)
          (hpeak k hka) qR (v k) hRX (hchrono k hkδ hka)
        have Hq' := AmbientPresentation.congr (Q k) _ _ _ _ qO qO (v k) rfl
          (omittedAlgebra_succ base v j S k hkS).symm Hq
        have Hr' := AmbientPresentation.congr (Q k) _ _ _ _ qR qR (v k) rfl
          (omittedAlgebra_succ base v (j+1) S k hkS).symm Hr
        exact ambient_presentation_swap (Q j) (Q k) (O k) (R k) (O (k+1)) (R (k+1))
          (omittedAlgebra_base_mono base v S (k+1) le_self_add)
          (pO k) qO (pO (k+1)) qR (v j) (v k) (htrace k hkδ) hi Hq' Hr'
      · exact inert (omittedAlgebra_succ_of_one base v j S k (hinactive k hkδ hka))
          (omittedAlgebra_succ_of_one base v (j+1) S k (hinactive k hkδ hka))
  · exact inert (omittedAlgebra_succ_of_not_mem base v j S k hkS)
      (omittedAlgebra_succ_of_not_mem base v (j+1) S k hkS)

include hj hja hpeak hchrono in
lemma omitted_model_zero : (Q j).OmittedModel base v j S 0 := by
  exact AmbientPresentation.congr (Q j) _ _ _ _ (hpeak j hja)
    (fun i n => omittedAlgebra_contains_initial base v j S 0 (hpeak j hja i n)) (v j)
    (omittedAlgebra_zero base v j S).symm
    (omittedAlgebra_zero base v (j+1) S).symm (hchrono j hj hja)

include hj hja hjS hpeak hchrono hinactive htrace hdep in

theorem omitted_presentation_of_chronological (β : Ordinal.{u}) (hβ : β ≤ δ) :
    (Q j).AmbientPresentation (omittedAlgebra base v j S β)
      (fun i n => omittedAlgebra_contains_initial base v j S β (hpeak j hja i n))
      (v j) (omittedAlgebra base v (j+1) S β) :=
  ordinal_invariant ((Q j).OmittedModel base v j S) δ
    (omitted_model_zero base v Q active S δ j hj hja hpeak hchrono)
    (omitted_model_successor base v Q active S δ j hja hjS hpeak hchrono hinactive htrace hdep)
    (fun β _ hlim ih => omitted_model_limit base v Q active S j hja hpeak β hlim ih)
    β hβ

end

end PeakingPairData

open Topology

open Topology

open Topology

open Topology

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

theorem omitted_endpoint_bridge
    (htrace : ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a) :
    BridgeSuccessor (StarSubalgebra.inclusion
      (omittedAlgebra_base_mono base v S δ (show j ≤ j+1 from le_self_add))) := by
  exact AmbientPresentation.bridge (Q j) _ _
    (fun i n => omittedAlgebra_contains_initial base v j S δ (hpeak j hja i n)) (v j) _
    (omitted_presentation_of_chronological base v Q active S δ j hj hja hjS hpeak
      hchrono hinactive htrace hdep δ le_rfl)
    (omitted_distinct_of_chronological base v Q active S δ j hj hja hjS hpeak
      hchrono hinactive hne hdep h0 δ le_rfl)

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

theorem dependency_closed_retained_successor
    (htrace : ∀ j < δ, ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a)
    (j : Ordinal.{u}) (hj : j < δ) :
    BridgeSuccessor (retainedOrdinalInclusion base v S (show j ≤ j+1 from le_self_add)) := by
  by_cases hjS : j ∈ S
  · exact retainedOrdinalSuccessor_identity base v S j hjS
  · by_cases hja : j ∈ active
    · have hp := omitted_endpoint_bridge base v Q active S δ j hj hja hjS hpeak hchrono
        hinactive hne
        (fun k hkδ hkS hka _ => dependency_peaks_omitted base v Q I S hclosed k j hkS
          (hI k hkδ hka) (hdata k hkδ hka))
        (chronological_simple base v Q active δ hpeak hchrono hinactive hne h0 j hj.le)
        (htrace j hj)
      exact ambient_bridge_congr _ _ _ _ _ _
        (omittedAlgebra_endpoint_eq_retained base v S δ j hS)
        (omittedAlgebra_endpoint_eq_retained base v S δ (j+1) hS) hp
    · exact ambient_identity_bridge _ _ _
        (retainedOrdinal_succ_of_one base v S j (hinactive j hj hja)).symm

include hS hclosed hI hdata hpeak hchrono hinactive hne h0 in

theorem dependency_closed_pureUEP
    (htrace : ∀ j < δ, ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a) :
    PureUEP (retainedOrdinalInclusion base v S (show 0 ≤ δ from bot_le)) := by
  apply retainedOrdinal_pureUEP base v S δ
    (dependency_closed_retained_simple base v Q active S I δ hS hclosed hI hdata hpeak
      hchrono hinactive hne h0)
  exact dependency_closed_retained_successor base v Q active S I δ hS hclosed hI hdata
    hpeak hchrono hinactive hne h0 htrace

end PeakingPairData

open Topology
section
universe u v
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable [PartialOrder A] [StarOrderedRing A]
variable
    (base : Set A) (z : Ordinal.{u} → A) (Q : Ordinal.{u} → PeakingPairData A)
    (active : Set Ordinal.{u}) (I : Ordinal.{u} → Set Ordinal.{u}) (δ : Ordinal.{u})
    (hI : ∀ k < δ, I k ⊆ Set.Iio k)
    (hdata : ∀ k < δ, k ∈ active → ∀ i n, (Q k).peak i n ∈ generatedFamily base z (I k))
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base z (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base z (Set.Iio k)) (hpeak k hk)
        (z k) (generatedFamily base z (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → z k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base z (Set.Iio k)) (hpeak k hk))
    (h0 : IsSimpleCStar (generatedFamily base z (Set.Iio 0)))
    (htrace : ∀ j < δ, ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a)

include hI hdata hpeak hchrono hinactive hne h0 htrace in
lemma literal_dependency_closed_pureUEP
    (S : Set Ordinal.{u}) (hS : S ⊆ Set.Iio δ) (hclosed : DependencyClosed I S) :
    PureUEP (StarSubalgebra.inclusion (generatedFamily_mono base z hS)) := by
  have hz : retainedOrdinalAlgebra base z S 0 = generatedFamily base z S := by
    change generatedFamily base z (S ∪ Set.Iio 0) = _
    rw [show Set.Iio (0:Ordinal.{u}) = ∅ by ext x; simp, Set.union_empty]
  exact subalgebra_pureUEP_congr _ _ _ _ _ _ hz
    (retainedOrdinal_endpoint base z S δ hS)
    (dependency_closed_pureUEP base z Q active S I δ hS hclosed
      (fun k hk _ => hI k hk) hdata hpeak hchrono hinactive hne h0 htrace)

include hI hdata hpeak hchrono hinactive hne h0 htrace in
lemma literal_dependency_closed_ambientUEP
    (hgen : generatedFamily base z (Set.Iio δ) = ⊤)
    (S : Set Ordinal.{u}) (hS : S ⊆ Set.Iio δ) (hclosed : DependencyClosed I S) :
    PureUEP (generatedFamily base z S).subtype :=
  subalgebraSubtype_pureUEP_of_top _ _ (generatedFamily_mono base z hS) hgen
    (literal_dependency_closed_pureUEP base z Q active I δ hI hdata hpeak hchrono
      hinactive hne h0 htrace S hS hclosed)

include hI hdata hpeak hchrono hinactive hne h0 htrace in

theorem literal_countable_determination
    (hIc : ∀ k < δ, (I k).Countable) (hbase : TopologicalSpace.IsSeparable base)
    (hgen : generatedFamily base z (Set.Iio δ) = ⊤)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set Ordinal.{u}, S.Countable ∧ S ⊆ Set.Iio δ ∧ DependencyClosed I S ∧
      TopologicalSpace.IsSeparable (generatedFamily base z S : Set A) ∧
      IsSimpleCStar (generatedFamily base z S) ∧
      IsPureState (restrictState (generatedFamily base z S).subtype f) ∧
      StateExtensionUnique (generatedFamily base z S).subtype
        (restrictState (generatedFamily base z S).subtype f) := by
  let e : δ.ToType → Ordinal.{u} := fun k => (k : Ordinal.{u})
  have hei : Function.Injective e := by
    intro a b h
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext h)
  have her : Set.range e = Set.Iio δ := by
    ext k
    constructor
    · rintro ⟨j,rfl⟩
      exact j.toOrd.property
    · intro hk
      exact ⟨Ordinal.ToType.mk ⟨k,hk⟩,by simp [e,Ordinal.ToType.toOrd]⟩
  let J : δ.ToType → Set δ.ToType := fun k => e ⁻¹' I (e k)
  have hJ : ∀ k, (J k).Countable := fun k => (hIc (e k) k.toOrd.property).preimage hei
  have hgen' : generatedFamily base (z ∘ e) Set.univ = ⊤ := by
    rw [generatedFamily_reindex,Set.image_univ,her,hgen]
  obtain ⟨R,hR,hdep,hRp⟩ := generatedFamily_countable_pure_restriction base (z ∘ e)
    hbase hgen' J hJ f hf
  let S := e '' R
  have hS : S ⊆ Set.Iio δ := fun _ hx => her ▸ Set.mem_range.mpr ⟨hx.choose,hx.choose_spec.2⟩
  have hSd : DependencyClosed I S := by
    intro k hk j hj
    obtain ⟨r,hr,rfl⟩ := hk
    have hjδ : j < δ := (hI (e r) r.toOrd.property hj).trans r.toOrd.property
    let q : δ.ToType := Ordinal.ToType.mk ⟨j,hjδ⟩
    have hq : e q = j := by simp [q,e,Ordinal.ToType.toOrd]
    exact ⟨q,hdep r hr (by change e q ∈ I (e r); rwa [hq]),hq⟩
  have hps : IsPureState (restrictState (generatedFamily base z S).subtype f) := by
    exact subalgebra_pureRestriction_congr _ _ (generatedFamily_reindex base z e R) f hRp
  have hsimp := dependency_closed_retained_simple base z Q active S I δ hS hSd
    (fun k hk _ => hI k hk) hdata hpeak hchrono hinactive hne h0
  have hsimp' : IsSimpleCStar (generatedFamily base z S) := by
    apply (subalgebra_simple_congr _ _ ?_).mp hsimp
    change generatedFamily base z (S ∪ Set.Iio 0) = _
    rw [show Set.Iio (0:Ordinal.{u}) = ∅ by ext x; simp, Set.union_empty]

  refine ⟨S,hR.image e,hS,hSd,generatedFamily_separable base z hbase (hR.image e),hsimp',hps,?_⟩
  exact literal_dependency_closed_ambientUEP base z Q active I δ hI hdata hpeak hchrono
    hinactive hne h0 htrace hgen S hS hSd _ hps

end PeakingPairData
end

open Cardinal Topology TopologicalSpace

open Cardinal Topology TopologicalSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Operators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped BigOperators InnerProductSpace ComplexOrder
open Filter Topology

open scoped InnerProductSpace BigOperators

open scoped BigOperators

open scoped BigOperators

open scoped BigOperators InnerProductSpace

open scoped BigOperators InnerProductSpace

open scoped BigOperators

open scoped InnerProductSpace BigOperators
open Filter Topology

open scoped BigOperators InnerProductSpace
open Filter Topology

open scoped BigOperators InnerProductSpace ComplexStarModule
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem homogeneity [TopologicalSpace.SeparableSpace A]
    (hA : IsSimpleCStar A) (hinf : ¬ FiniteDimensional ℂ A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a :=
  homogeneity_of_nearCentralRows hA hinf nearCentralRows f g hf hg

end KOS

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

namespace TracialStage
variable (X : TracialStage)

def dummyPair : PeakingPairData X :=
  homogeneousCARPeakPair (StarAlgHom.id ℂ CAR) X.base X.base_injective
    X.reference X.reference X.reference_peaks
    (by simpa only [X.reference_spec.2] using carVector_isPure)
    X.reference_spec.1.1 X.baseUEP (StarAlgEquiv.refl ℂ CAR) rfl
    X.positiveTrace X.tracial X.positiveTrace_normalized X.positiveTrace_faithful

end TracialStage

namespace ChronologicalData
variable {X : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalData X δ)

lemma pureUEP (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio δ)
    (hclosed : DependencyClosed D.dependency S) : PureUEP (D.algebra S).subtype :=
  PeakingPairData.literal_dependency_closed_ambientUEP (Set.range X.base) D.generator
    D.pair D.active D.dependency δ D.lower D.supported D.peak_mem D.chronological
    (fun k _ => D.inactive k) D.inequivalent (X.base_simple D.generator)
    (fun j _ k _ a => (D.trace j a).trans (D.trace k a).symm) D.generated S hS hclosed

lemma countable_determination (f : X →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set Ordinal.{0}, S.Countable ∧ S ⊆ Set.Iio δ ∧ DependencyClosed D.dependency S ∧
      TopologicalSpace.IsSeparable (D.algebra S : Set X) ∧ IsSimpleCStar (D.algebra S) ∧
      IsPureState (restrictState (D.algebra S).subtype f) ∧
      StateExtensionUnique (D.algebra S).subtype (restrictState (D.algebra S).subtype f) :=
  PeakingPairData.literal_countable_determination (Set.range X.base) D.generator
    D.pair D.active D.dependency δ D.lower D.supported D.peak_mem D.chronological
    (fun k _ => D.inactive k) D.inequivalent (X.base_simple D.generator)
    (fun j _ k _ a => (D.trace j a).trans (D.trace k a).symm)
    D.countable X.base_separable D.generated f hf

end ChronologicalData
end

section
open CategoryTheory
attribute [local instance] generatedFamily_isClosed

namespace ChronologicalStage

def forget : ChronologicalStage ⥤ TracialStage where
  obj := ChronologicalStage.stage
  map f := f.embedding
  map_id _ := rfl
  map_comp _ _ := rfl

def initialHistory : ChronologicalData TracialStage.initial 0 where
  generator _ := 1
  active := ∅
  active_lt := Set.empty_subset _
  dependency _ := ∅
  lower _ _ := Set.empty_subset _
  countable _ _ := Set.countable_empty
  pair _ := TracialStage.initial.dummyPair
  trace _ _ := rfl
  leftPeak _ _ := rfl
  supported _ _ h := False.elim h
  peak_mem _ h := False.elim h
  chronological _ _ h := False.elim h
  inactive _ _ := rfl
  inequivalent _ _ h := False.elim h
  generated := by
    rw [TracialStage.generatedFamily_zero]
    ext a
    constructor
    · intro _; trivial
    · intro _; exact ⟨a,rfl⟩

def initial : ChronologicalStage := ⟨TracialStage.initial,0,initialHistory⟩

end ChronologicalStage
end

namespace PeakingPairData
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A S T R U : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U]

variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit partialOrderT starOrderedRingT in
lemma HNNAmbientPresentation.transport [PartialOrder T] [StarOrderedRing T] (G : PeakingPairData A) (G' : PeakingPairData B)
    (φ : A →⋆ₐ[ℂ] B) (hp : ∀ i n, φ (G.peak i n) = G'.peak i n)
    (ht : ∀ a, G'.trace (φ a) = G.trace a)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (b' : R →⋆ₐ[ℂ] B) (t' : U →⋆ₐ[ℂ] B)
    (s : S ≃⋆ₐ[ℂ] R) (r : T ≃⋆ₐ[ℂ] U)
    (hs : ∀ a, b' (s a) = φ (b a)) (hr : ∀ a, t' (r a) = φ (t a))
    (H : G.HNNAmbientPresentation b t z) :
    G'.HNNAmbientPresentation b' t' (φ ∘ z) := by
  obtain ⟨D,hDp,hDt,e,heb,hew,het⟩ := H
  obtain ⟨D',hdp,hdt⟩ := exists_reparam_pair D s
  obtain ⟨E,hEb,hEw,hEt,_⟩ := D'.hnn_equiv_of_peaks D s.symm hdp hdt
  have hs' (a : R) : b' a = φ (b (s.symm a)) := by
    simpa only [s.apply_symm_apply] using hs (s.symm a)
  refine hnnAmbient_of_data G' b' t' (φ ∘ z) D' ?_ ?_ (E.trans (e.trans r)) ?_ ?_ ?_
  · intro i n
    rw [hs',hdp,hDp,hp]
  · intro a
    rw [hs',ht,← hdt,hDt]
  · intro a
    change t' (r (e (E (D'.hnnBase a)))) = b' a
    rw [hr,hEb,heb,hs']
  · intro i
    change t' (r (e (E (D'.hnnLetter i)))) = φ (z i)
    rw [hr,hEw,hew]
  · intro a
    change G'.trace (t' (r (e (E a)))) = D'.hnnTrace a
    rw [hr,ht,het,hEt]

lemma HNNAmbientPresentation.same_data (G G' : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (hp : ∀ i n, G.peak i n = G'.peak i n)
    (ht : ∀ a, G.trace a = G'.trace a)
    (H : G.HNNAmbientPresentation b t z) : G'.HNNAmbientPresentation b t z := by
  obtain ⟨D,hDp,hDt,e,heb,hew,het⟩ := H
  exact hnnAmbient_of_data G' b t z D (fun i n => (hDp i n).trans (hp i n))
    (fun a => (hDt a).trans (ht _)) e heb hew (fun a => (ht _).symm.trans (het a))

end PeakingPairData

open Topology
section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
attribute [local irreducible] HNNAlgebra hnnCStar hnnOrder
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (P : PeakingPairData A) (Q : PeakingPairData B) (φ : A →⋆ₐ[ℂ] B)
  (hφ : Function.Injective φ)
  (hp : ∀ i n, φ (P.peak i n) = Q.peak i n)
  (ht : ∀ a, Q.trace (φ a) = P.trace a)

include hp ht hφ in
lemma AmbientPresentation.map
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (S.map φ : Set B)] [IsClosed (T.map φ : Set B)]
    (pS : ∀ i n, P.peak i n ∈ S) (z : A)
    (H : P.AmbientPresentation S pS z T) :
    Q.AmbientPresentation (S.map φ)
      (fun i n => hp i n ▸ (show φ (P.peak i n) ∈ S.map φ from ⟨_,pS i n,rfl⟩))
      (φ z) (T.map φ) := by
  have hz : (φ ∘ starPair z) = starPair (φ z) := by
    funext i
    cases i
    · rfl
    · exact map_star φ z
  have H' := HNNAmbientPresentation.transport P Q φ hp ht S.subtype T.subtype
    (starPair z) (S.map φ).subtype (T.map φ).subtype
    (closedMapEquiv S φ hφ) (closedMapEquiv T φ hφ) (fun _ => rfl) (fun _ => rfl) H
  rw [hz] at H'
  exact H'

include hp in
lemma PairDistinctOn.map
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (pS : ∀ i n, P.peak i n ∈ S) (H : P.PairDistinctOn S pS) :
    letI := closed_map_isClosed S φ hφ
    Q.PairDistinctOn (S.map φ)
      (fun i n => hp i n ▸ (show φ (P.peak i n) ∈ S.map φ from ⟨_,pS i n,rfl⟩)) := by
  let := closed_map_isClosed S φ hφ
  let pQ : ∀ i n, Q.peak i n ∈ S.map φ :=
    fun i n => hp i n ▸ ⟨_,pS i n,rfl⟩
  let e := closedMapEquiv S φ hφ
  have hstate (i : Bool) : restrictState e.toStarAlgHom ((Q.onSubalgebra (S.map φ) pQ).state i) =
      (P.onSubalgebra S pS).state i := by
    ext a
    exact congrArg (fun f : A →L[ℂ] ℂ => f a) (states_restrict_of_peaks P Q φ hp i)
  intro he
  have hh := pureStateEquivalent_restrict_equiv e _ _
    ((Q.onSubalgebra (S.map φ) pQ).peaks false).isPureState
    ((Q.onSubalgebra (S.map φ) pQ).peaks true).isPureState he
  exact H (by simpa only [hstate] using hh)

end PeakingPairData
end

open Topology
section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

namespace ChronologicalHistory
variable {X Y : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalHistory X δ)
  (φ : TracialStage.Hom X Y)

lemma mapped_presentation (k : Ordinal.{0}) (hk : k < δ) (ha : k ∈ D.active) :
    (φ.pushPair (D.pair k) (D.trace k)).AmbientPresentation
      (generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio k))
      (fun i n => φ.mapped_mem D.generator (Set.Iio k) (D.peak_mem k ha i n))
      (φ.map (D.generator k))
      (generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio (k+1))) := by
  let S := generatedFamily (Set.range X.base) D.generator (Set.Iio k)
  let T := generatedFamily (Set.range X.base) D.generator (Set.Iio (k+1))
  let := closed_map_isClosed S φ.map φ.injective
  let := closed_map_isClosed T φ.map φ.injective
  have h := PeakingPairData.AmbientPresentation.map (D.pair k)
    (φ.pushPair (D.pair k) (D.trace k)) φ.map φ.injective
    (fun _ _ => rfl) (fun a => (φ.trace_map a).trans (D.trace k a).symm)
    S T (D.peak_mem k ha) (D.generator k) (D.chronological k hk ha)
  exact PeakingPairData.AmbientPresentation.congr _ _ _ _ _ _ _ _
    (φ.generatedFamily_map D.generator (Set.Iio k))
    (φ.generatedFamily_map D.generator (Set.Iio (k+1))) h

lemma mapped_inequivalent (k : Ordinal.{0}) (hk : k < δ) (ha : k ∈ D.active) :
    (φ.pushPair (D.pair k) (D.trace k)).PairDistinctOn
      (generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio k))
      (fun i n => φ.mapped_mem D.generator (Set.Iio k) (D.peak_mem k ha i n)) := by
  let S := generatedFamily (Set.range X.base) D.generator (Set.Iio k)
  let := closed_map_isClosed S φ.map φ.injective
  have h := PeakingPairData.PairDistinctOn.map (D.pair k)
    (φ.pushPair (D.pair k) (D.trace k)) φ.map φ.injective (fun _ _ => rfl)
    S (D.peak_mem k ha) (D.inequivalent k hk ha)
  exact PeakingPairData.PairDistinctOn.congr _ _ _ _ _
    (φ.generatedFamily_map D.generator (Set.Iio k)) h

def push : ChronologicalHistory Y δ where
  generator := φ.map ∘ D.generator
  active := D.active
  active_lt := D.active_lt
  dependency := D.dependency
  lower := D.lower
  countable := D.countable
  pair k := φ.pushPair (D.pair k) (D.trace k)
  trace _ _ := rfl
  leftPeak k n := by
    change φ.map ((D.pair k).peak false n) = _
    rw [D.leftPeak,φ.base_map]
  supported k hk ha i n := φ.mapped_mem D.generator _ (D.supported k hk ha i n)
  peak_mem k ha i n := φ.mapped_mem D.generator _ (D.peak_mem k ha i n)
  chronological := D.mapped_presentation φ
  inactive k hk := by change φ.map (D.generator k) = 1; rw [D.inactive k hk,map_one]
  inequivalent := D.mapped_inequivalent φ

end ChronologicalHistory

end

open Topology

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (P Q : PeakingPairData A) (hp : ∀ i n, P.peak i n = Q.peak i n)

include hp in
lemma AmbientPresentation.same_data
    (ht : ∀ a,P.trace a = Q.trace a)
    (S T : StarSubalgebra ℂ A) [IsClosed (S:Set A)] [IsClosed (T:Set A)]
    (pS : ∀ i n,P.peak i n ∈ S) (qS : ∀ i n,Q.peak i n ∈ S) (z : A)
    (H : P.AmbientPresentation S pS z T) : Q.AmbientPresentation S qS z T :=
  HNNAmbientPresentation.same_data P Q S.subtype T.subtype (starPair z) hp ht H

include hp in
lemma PairDistinctOn.same_peaks
    (S : StarSubalgebra ℂ A) [IsClosed (S:Set A)]
    (pS : ∀ i n,P.peak i n ∈ S) (qS : ∀ i n,Q.peak i n ∈ S)
    (H : P.PairDistinctOn S pS) : Q.PairDistinctOn S qS := by
  have hs (i : Bool) : (Q.onSubalgebra S qS).state i = (P.onSubalgebra S pS).state i := by
    have h := states_restrict_of_peaks (P.onSubalgebra S pS) (Q.onSubalgebra S qS)
      (StarAlgHom.id ℂ S) (fun i n => Subtype.ext (hp i n)) i
    exact h
  unfold PairDistinctOn at H ⊢
  simpa only [hs] using H

end PeakingPairData

section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

namespace ChronologicalHistory
attribute [local instance] OAI.NaimarkZFC.instDecidableEqOrdinal_solutions_1
variable {X : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalHistory X δ)
  (Q : PeakingPairData X) (htrace : ∀ a,Q.trace a = X.trace a)
  (hleft : ∀ n,Q.peak false n = X.base (carPeak n))
  (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio δ) (hSc : S.Countable)
  (hsupport : ∀ i n,Q.peak i n ∈ generatedFamily (Set.range X.base) D.generator S)
  (z : X)

variable (HP : Q.AmbientPresentation (generatedFamily (Set.range X.base) D.generator (Set.Iio δ))
    (D.inserted_peak_mem Q S hS hsupport) z
    (generatedFamily (Set.range X.base) (Function.update D.generator δ z) (Set.Iio (δ+1))))
  (HD : Q.PairDistinctOn (generatedFamily (Set.range X.base) D.generator (Set.Iio δ))
    (D.inserted_peak_mem Q S hS hsupport))

def insertActive : ChronologicalHistory X (δ+1) where
  generator := Function.update D.generator δ z
  active := insert δ D.active
  active_lt := by
    intro k hk
    rcases hk with rfl | hk
    · exact (lt_add_one k)
    · exact (show k < δ from D.active_lt hk).trans ((lt_add_one δ))
  dependency := Function.update D.dependency δ S
  lower k hk := by
    by_cases he : k=δ
    · subst k; simpa only [Function.update_self] using hS
    · rw [Function.update_of_ne he]
      exact D.lower k (lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he)
  countable k hk := by
    by_cases he : k=δ
    · subst k; simpa only [Function.update_self] using hSc
    · rw [Function.update_of_ne he]
      exact D.countable k (lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he)
  pair := Function.update D.pair δ Q
  trace k a := by
    by_cases he : k=δ
    · subst k; simpa only [Function.update_self] using htrace a
    · simpa only [Function.update_of_ne he] using D.trace k a
  leftPeak k n := by
    by_cases he : k=δ
    · subst k; simpa only [Function.update_self] using hleft n
    · simpa only [Function.update_of_ne he] using D.leftPeak k n
  supported k hk ha i n := by
    by_cases he : k=δ
    · subst k
      rw [Function.update_self,Function.update_self,
        generatedFamily_update_before _ _ _ _ _ hS]
      exact hsupport i n
    · rw [Function.update_of_ne he,Function.update_of_ne he,
        generatedFamily_update_before _ _ _ _ _ ((D.lower k
          (lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he)).trans
          (Set.Iio_subset_Iio (Order.lt_add_one_iff.mp hk)))]
      exact D.supported k (lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he)
        ((Set.mem_insert_iff.mp ha).resolve_left he) i n
  peak_mem k ha i n := by
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · rw [Function.update_self,generatedFamily_update_before _ _ _ _ _ (fun _ h => h)]
      exact D.inserted_peak_mem Q S hS hsupport i n
    · have hk := D.active_lt ha
      rw [Function.update_of_ne hk.ne,generatedFamily_update_before _ _ _ _ _
        (Set.Iio_subset_Iio hk.le)]
      exact D.peak_mem k ha i n
  chronological k hk ha := by
    by_cases he : k=δ
    · subst k
      simpa only [Function.update_self,
        generatedFamily_update_before _ _ _ _ (Set.Iio δ) (fun _ h => h)] using HP
    · have hkδ : k < δ := lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he
      have ha' : k ∈ D.active := (Set.mem_insert_iff.mp ha).resolve_left he
      simp only [Function.update_of_ne he]
      exact PeakingPairData.AmbientPresentation.congr _ _ _ _ _ _ _ _
        (generatedFamily_update_before _ _ _ _ _ (Set.Iio_subset_Iio hkδ.le)).symm
        (generatedFamily_update_before _ _ _ _ _
          (Set.Iio_subset_Iio (Order.add_one_le_iff.mpr hkδ))).symm (D.chronological k hkδ ha')
  inactive k hk := by
    have hne : k≠δ := fun he => hk (he ▸ Set.mem_insert δ D.active)
    rw [Function.update_of_ne hne]
    exact D.inactive k (fun ha => hk (Set.mem_insert_of_mem _ ha))
  inequivalent k hk ha := by
    by_cases he : k=δ
    · subst k
      simpa only [Function.update_self,
        generatedFamily_update_before _ _ _ _ (Set.Iio δ) (fun _ h => h)] using HD
    · have hkδ : k < δ := lt_of_le_of_ne (Order.lt_add_one_iff.mp hk) he
      have ha' : k ∈ D.active := (Set.mem_insert_iff.mp ha).resolve_left he
      simp only [Function.update_of_ne he]
      exact PeakingPairData.PairDistinctOn.congr _ _ _ _ _
        (generatedFamily_update_before _ _ _ _ _ (Set.Iio_subset_Iio hkδ.le)).symm
        (D.inequivalent k hkδ ha')

end ChronologicalHistory
end

section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma HNNAmbientPresentation.fullImage (G : PeakingPairData B)
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) (z : B)
    (S T : StarSubalgebra ℂ B) [IsClosed (S : Set B)] [IsClosed (T : Set B)]
    (hS : S = φ.range) (hT : T = ⊤) (hp : ∀ i n,G.peak i n ∈ S)
    (H : G.HNNAmbientPresentation φ (StarAlgHom.id ℂ B) (starPair z)) :
    G.AmbientPresentation S hp z T := by
  exact HNNAmbientPresentation.transport G G (StarAlgHom.id ℂ B)
    (fun _ _ => rfl) (fun _ => rfl) φ (StarAlgHom.id ℂ B) (starPair z)
    S.subtype T.subtype (fullImageEquiv φ hφ S hS) (fullTopEquiv T hT)
    (fun _ => rfl) (fun _ => rfl) H

lemma PairDistinctOn.fullImage (P : PeakingPairData A) (G : PeakingPairData B)
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (hp : ∀ i n,φ (P.peak i n) = G.peak i n)
    (S : StarSubalgebra ℂ B) [IsClosed (S : Set B)] (hS : S = φ.range)
    (pS : ∀ i n,G.peak i n ∈ S)
    (H : ¬ PureStateEquivalent (P.state false) (P.peaks false).isPureState
      (P.state true) (P.peaks true).isPureState) : G.PairDistinctOn S pS := by
  let e := fullImageEquiv φ hφ S hS
  have he (i : Bool) (n : ℕ) : e (P.peak i n) = (G.onSubalgebra S pS).peak i n :=
    Subtype.ext (hp i n)
  have hstate := states_restrict_of_peaks P (G.onSubalgebra S pS) e.toStarAlgHom he
  intro hh
  have h := pureStateEquivalent_restrict_equiv e _ _
    ((G.onSubalgebra S pS).peaks false).isPureState
    ((G.onSubalgebra S pS).peaks true).isPureState hh
  exact H (by simpa only [hstate] using h)

end PeakingPairData
end

open Topology
namespace PeakingPairData
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
attribute [local irreducible] HNNAlgebra hnnCStar hnnOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma hnn_generated_starPair (Q : PeakingPairData A) :
    Dense (StarAlgebra.adjoin ℂ (Set.range Q.hnnBase ∪
      Set.range (starPair (Q.hnnLetter false))) : Set Q.HNNAlgebra) := by
  rw [← Q.hnnLetter_starPair]
  exact Q.hnn_generated

lemma hnn_ambient_literal (Q : PeakingPairData A) (G : PeakingPairData Q.HNNAlgebra)
    (hp : ∀ i n,G.peak i n = Q.hnnBase (Q.peak i n))
    (ht : ∀ a,G.trace a = Q.hnnTrace a) :
    G.HNNAmbientPresentation Q.hnnBase (StarAlgHom.id ℂ Q.HNNAlgebra)
      (starPair (Q.hnnLetter false)) := by
  exact hnnAmbient_of_data G Q.hnnBase (StarAlgHom.id ℂ Q.HNNAlgebra)
    (starPair (Q.hnnLetter false)) Q (fun i n => (hp i n).symm)
    (fun a => (Q.hnnTrace_base a).symm.trans (ht _).symm)
    (StarAlgEquiv.refl _ _) (fun _ => rfl) (fun i => congrFun Q.hnnLetter_starPair i) ht

end PeakingPairData

open Topology
namespace ChronologicalStage
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
attribute [local instance 2000] PeakingPairData.hnnCStar PeakingPairData.hnnOrder PeakingPairData.hnnStarOrder
attribute [local instance] OAI.NaimarkZFC.ChronologicalStage.instDecidableEqOrdinal
variable (X : ChronologicalStage) (Q : PeakingPairData X.stage) (hs : Q.Separated)
  (ht : ∀ a,Q.trace a = X.stage.trace a)
  (hl : ∀ n,Q.peak false n = X.stage.base (carPeak n))
  (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio X.height) (hSc : S.Countable)
  (hp : ∀ i n,Q.peak i n ∈ X.history.algebra S)
  (hne : ¬ PureStateEquivalent (Q.state false) (Q.peaks false).isPureState
    (Q.state true) (Q.peaks true).isPureState)

abbrev hnnEmbedding := TracialStage.hnnHom X.stage Q hs ht
abbrev hnnPriorHistory := X.history.toChronologicalHistory.push (hnnEmbedding X Q hs ht)
abbrev hnnNewPair := (hnnEmbedding X Q hs ht).pushPair Q ht

include hl in
lemma hnn_new_left (n : ℕ) : (hnnNewPair X Q hs ht).peak false n =
    (TracialStage.hnn X.stage Q hs).base (carPeak n) := by
  change Q.hnnBase (Q.peak false n) = Q.hnnBase (X.stage.base (carPeak n))
  rw [hl]

include hp in
lemma hnn_new_supported (i : Bool) (n : ℕ) :
    (hnnNewPair X Q hs ht).peak i n ∈ generatedFamily
      (Set.range (TracialStage.hnn X.stage Q hs).base) (hnnPriorHistory X Q hs ht).generator S :=
  (hnnEmbedding X Q hs ht).mapped_mem X.history.generator S (hp i n)

lemma hnn_before_range : generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
    (hnnPriorHistory X Q hs ht).generator (Set.Iio X.height) = Q.hnnBase.range :=
  X.history.image_generated_range (hnnEmbedding X Q hs ht)

lemma hnn_after_generated : generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
    (Function.update (hnnPriorHistory X Q hs ht).generator X.height (Q.hnnLetter false))
    (Set.Iio (X.height+1)) = ⊤ :=
  X.history.updated_generated (hnnEmbedding X Q hs ht) (Q.hnnLetter false) Q.hnn_generated_starPair

lemma hnn_new_presentation :
    (hnnNewPair X Q hs ht).AmbientPresentation
      (generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
        (hnnPriorHistory X Q hs ht).generator (Set.Iio X.height))
      ((hnnPriorHistory X Q hs ht).inserted_peak_mem (hnnNewPair X Q hs ht) S hS
        (hnn_new_supported X Q hs ht S hp))
      (Q.hnnLetter false)
      (generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
        (Function.update (hnnPriorHistory X Q hs ht).generator X.height (Q.hnnLetter false))
        (Set.Iio (X.height+1))) := by
  exact PeakingPairData.HNNAmbientPresentation.fullImage (hnnNewPair X Q hs ht)
    Q.hnnBase Q.hnnBase_injective (Q.hnnLetter false) _ _
    (hnn_before_range X Q hs ht) (hnn_after_generated X Q hs ht) _
    (Q.hnn_ambient_literal (hnnNewPair X Q hs ht) (fun _ _ => rfl) (fun _ => rfl))

include hne in
lemma hnn_new_inequivalent :
    (hnnNewPair X Q hs ht).PairDistinctOn
      (generatedFamily (Set.range (TracialStage.hnn X.stage Q hs).base)
        (hnnPriorHistory X Q hs ht).generator (Set.Iio X.height))
      ((hnnPriorHistory X Q hs ht).inserted_peak_mem (hnnNewPair X Q hs ht) S hS
        (hnn_new_supported X Q hs ht S hp)) :=
  PeakingPairData.PairDistinctOn.fullImage Q (hnnNewPair X Q hs ht)
    Q.hnnBase Q.hnnBase_injective (fun _ _ => rfl) _ (hnn_before_range X Q hs ht) _ hne

def hnnHistory : ChronologicalData (TracialStage.hnn X.stage Q hs) (X.height+1) where
  toChronologicalHistory := (hnnPriorHistory X Q hs ht).insertActive
    (hnnNewPair X Q hs ht) (fun _ => rfl) (hnn_new_left X Q hs ht hl)
    S hS hSc (hnn_new_supported X Q hs ht S hp) (Q.hnnLetter false)
    (hnn_new_presentation X Q hs ht S hS hp) (hnn_new_inequivalent X Q hs ht S hS hp hne)
  generated := hnn_after_generated X Q hs ht

abbrev hnnSuccessor : ChronologicalStage :=
  ⟨TracialStage.hnn X.stage Q hs,X.height+1,hnnHistory X Q hs ht hl S hS hSc hp hne⟩

def hnnHom : Hom X (hnnSuccessor X Q hs ht hl S hS hSc hp hne) where
  embedding := hnnEmbedding X Q hs ht
  height_le := (lt_add_one X.height).le
  generator k hk := by
    exact (Function.update_of_ne hk.ne (Q.hnnLetter false)
      (hnnPriorHistory X Q hs ht).generator).symm
  active k hk := by
    change k ∈ X.history.active ↔ k ∈ insert X.height X.history.active
    simp only [Set.mem_insert_iff,hk.ne,false_or]
  dependency k hk := by
    dsimp only [hnnSuccessor,hnnHistory,ChronologicalHistory.insertActive]
    rw [Function.update_of_ne hk.ne]
    rfl
  peak k hk i n := by
    dsimp only [hnnSuccessor,hnnHistory,ChronologicalHistory.insertActive]
    rw [Function.update_of_ne hk.ne]
    rfl

end ChronologicalStage

section
attribute [local instance] generatedFamily_isClosed
namespace ChronologicalStage
variable (X : ChronologicalStage)

def inactiveHom : Hom X X.inactiveSuccessor where
  embedding := TracialStage.Hom.id X.stage
  height_le := le_add_right (le_rfl : X.height ≤ X.height)
  generator _ _ := rfl
  active _ _ := Iff.rfl
  dependency k hk := by change _ = if k < X.height then _ else _; rw [ite_eq_left hk]
  peak _ _ _ _ := rfl

end ChronologicalStage
end

open CategoryTheory
namespace TracialStage

variable {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (D : J ⥤ TracialStage)

lemma directLimitHom_dense :
    Dense (⋃ i, Set.range (directLimitHom D i).map) :=
  cstarDirectLimitInclude_dense _ _

end TracialStage

open CategoryTheory
namespace ChronologicalStage
attribute [local instance] generatedFamily_isClosed
variable {J : Type} [Preorder J] [isDirectedOrderJ : IsDirectedOrder J] [nonemptyJ : Nonempty J]
  (F : J ⥤ ChronologicalStage)

def limitStage : TracialStage := TracialStage.directLimit (F ⋙ forget)
def limitEmbedding (i : J) : TracialStage.Hom (F.obj i).stage (limitStage F) :=
  TracialStage.directLimitHom (F ⋙ forget) i

def limitHeight : Ordinal.{0} := ⨆ i, (F.obj i).height
omit isDirectedOrderJ nonemptyJ in
lemma height_le_limit [IsDirectedOrder J] [Nonempty J] (i : J) : (F.obj i).height ≤ limitHeight F :=
  Ordinal.le_iSup _ i

def limitIndex (k : Ordinal.{0}) (hk : k < limitHeight F) : J :=
  Classical.choose (Ordinal.lt_iSup_iff.mp hk)
omit isDirectedOrderJ nonemptyJ in
lemma limitIndex_spec [IsDirectedOrder J] [Nonempty J] (k : Ordinal.{0}) (hk : k < limitHeight F) :
    k < (F.obj (limitIndex F k hk)).height :=
  Classical.choose_spec (Ordinal.lt_iSup_iff.mp hk)

lemma limit_embedding_compatible (i j : J) (h : i ≤ j) (a : (F.obj i).stage) :
    (limitEmbedding F j).map ((F.map (homOfLE h)).embedding.map a) =
      (limitEmbedding F i).map a :=
  TracialStage.limitIncl_compatible (F ⋙ forget) i j h a

lemma limit_generator_agree (i j : J) (k : Ordinal.{0})
    (hi : k < (F.obj i).height) (hj : k < (F.obj j).height) :
    (limitEmbedding F i).map ((F.obj i).history.generator k) =
      (limitEmbedding F j).map ((F.obj j).history.generator k) := by
  obtain ⟨m,him,hjm⟩ := exists_ge_ge i j
  rw [← limit_embedding_compatible F i m him,← limit_embedding_compatible F j m hjm,
    (F.map (homOfLE him)).generator k hi,(F.map (homOfLE hjm)).generator k hj]

lemma limit_peak_agree (i j : J) (k : Ordinal.{0})
    (hi : k < (F.obj i).height) (hj : k < (F.obj j).height) (b : Bool) (n : ℕ) :
    (limitEmbedding F i).map (((F.obj i).history.pair k).peak b n) =
      (limitEmbedding F j).map (((F.obj j).history.pair k).peak b n) := by
  obtain ⟨m,him,hjm⟩ := exists_ge_ge i j
  rw [← limit_embedding_compatible F i m him,← limit_embedding_compatible F j m hjm,
    (F.map (homOfLE him)).peak k hi,(F.map (homOfLE hjm)).peak k hj]

omit nonemptyJ in
lemma limit_active_agree [Nonempty J] (i j : J) (k : Ordinal.{0})
    (hi : k < (F.obj i).height) (hj : k < (F.obj j).height) :
    k ∈ (F.obj i).history.active ↔ k ∈ (F.obj j).history.active := by
  obtain ⟨m,him,hjm⟩ := exists_ge_ge i j
  exact ((F.map (homOfLE him)).active k hi).trans ((F.map (homOfLE hjm)).active k hj).symm

omit nonemptyJ in
lemma limit_dependency_agree [Nonempty J] (i j : J) (k : Ordinal.{0})
    (hi : k < (F.obj i).height) (hj : k < (F.obj j).height) :
    (F.obj i).history.dependency k = (F.obj j).history.dependency k := by
  obtain ⟨m,him,hjm⟩ := exists_ge_ge i j
  exact ((F.map (homOfLE him)).dependency k hi).trans
    ((F.map (homOfLE hjm)).dependency k hj).symm

def limitGenerator (k : Ordinal.{0}) : limitStage F :=
  if hk : k < limitHeight F then
    (limitEmbedding F (limitIndex F k hk)).map
      ((F.obj (limitIndex F k hk)).history.generator k) else 1

def limitActive : Set Ordinal.{0} :=
  {k | ∃ hk : k < limitHeight F, k ∈ (F.obj (limitIndex F k hk)).history.active}

def limitDependency (k : Ordinal.{0}) : Set Ordinal.{0} :=
  if hk : k < limitHeight F then (F.obj (limitIndex F k hk)).history.dependency k else ∅

def limitPair (k : Ordinal.{0}) : PeakingPairData (limitStage F) :=
  if hk : k < limitHeight F then
    (limitEmbedding F (limitIndex F k hk)).pushPair
      ((F.obj (limitIndex F k hk)).history.pair k)
      ((F.obj (limitIndex F k hk)).history.trace k)
  else (limitStage F).dummyPair

lemma limitGenerator_stage (i : J) (k : Ordinal.{0}) (hk : k < (F.obj i).height) :
    limitGenerator F k = (limitEmbedding F i).map ((F.obj i).history.generator k) := by
  have hl := hk.trans_le (height_le_limit F i)
  rw [limitGenerator,dite_eq_left hl]
  exact limit_generator_agree F _ i k (limitIndex_spec F k hl) hk

lemma limitActive_stage (i : J) (k : Ordinal.{0}) (hk : k < (F.obj i).height) :
    k ∈ limitActive F ↔ k ∈ (F.obj i).history.active := by
  constructor
  · rintro ⟨hl,ha⟩
    exact (limit_active_agree F _ i k (limitIndex_spec F k hl) hk).mp ha
  · intro ha
    have hl := hk.trans_le (height_le_limit F i)
    exact ⟨hl,(limit_active_agree F _ i k (limitIndex_spec F k hl) hk).mpr ha⟩

lemma limitDependency_stage (i : J) (k : Ordinal.{0}) (hk : k < (F.obj i).height) :
    limitDependency F k = (F.obj i).history.dependency k := by
  have hl := hk.trans_le (height_le_limit F i)
  rw [limitDependency,dite_eq_left hl]
  exact limit_dependency_agree F _ i k (limitIndex_spec F k hl) hk

lemma limitPair_peak_stage (i : J) (k : Ordinal.{0}) (hk : k < (F.obj i).height)
    (b : Bool) (n : ℕ) :
    (limitPair F k).peak b n = (limitEmbedding F i).map (((F.obj i).history.pair k).peak b n) := by
  have hl := hk.trans_le (height_le_limit F i)
  rw [limitPair,dite_eq_left hl,TracialStage.Hom.pushPair_peak]
  exact limit_peak_agree F _ i k (limitIndex_spec F k hl) hk b n

lemma limitPair_trace (k : Ordinal.{0}) (a : limitStage F) :
    (limitPair F k).trace a = (limitStage F).trace a := by
  unfold limitPair
  split <;> rfl

lemma limitPair_leftPeak (k : Ordinal.{0}) (n : ℕ) :
    (limitPair F k).peak false n = (limitStage F).base (carPeak n) := by
  unfold limitPair
  split
  · simp only [TracialStage.Hom.pushPair_peak,ChronologicalHistory.leftPeak,
      TracialStage.Hom.base_map]
  · rfl

lemma limit_algebra_map (i : J) (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio (F.obj i).height) :
    ((F.obj i).history.algebra S).map (limitEmbedding F i).map =
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) S := by
  rw [ChronologicalData.algebra,TracialStage.Hom.generatedFamily_map]
  exact generatedFamily_congr_on _ _ _ _ (fun k hk => (limitGenerator_stage F i k (hS hk)).symm)

end ChronologicalStage

open CategoryTheory Topology
namespace ChronologicalStage
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
variable {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (F : J ⥤ ChronologicalStage)

lemma limit_generated_eq (i : J) (S : Set Ordinal.{0}) (hS : S ⊆ Set.Iio (F.obj i).height) :
    generatedFamily (Set.range (limitStage F).base)
      ((limitEmbedding F i).map ∘ (F.obj i).history.generator) S =
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) S :=
  generatedFamily_congr_on _ _ _ _ (fun k hk => (limitGenerator_stage F i k (hS hk)).symm)

lemma limit_peak_mem (k : Ordinal.{0}) (ha : k ∈ limitActive F) (b : Bool) (n : ℕ) :
    (limitPair F k).peak b n ∈
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k) := by
  obtain ⟨hk,ha⟩ := ha
  let i := limitIndex F k hk
  have hi : k < (F.obj i).height := limitIndex_spec F k hk
  rw [limitPair_peak_stage F i k hi,← limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le)]
  exact (limitEmbedding F i).mapped_mem _ _ ((F.obj i).history.peak_mem k ha b n)

lemma limit_supported (k : Ordinal.{0}) (hk : k < limitHeight F)
    (ha : k ∈ limitActive F) (b : Bool) (n : ℕ) :
    (limitPair F k).peak b n ∈ generatedFamily (Set.range (limitStage F).base)
      (limitGenerator F) (limitDependency F k) := by
  let i := limitIndex F k hk
  have hi : k < (F.obj i).height := limitIndex_spec F k hk
  have hai := (limitActive_stage F i k hi).mp ha
  rw [limitPair_peak_stage F i k hi,limitDependency_stage F i k hi,
    ← limit_generated_eq F i _ (((F.obj i).history.lower k hi).trans (Set.Iio_subset_Iio hi.le))]
  exact (limitEmbedding F i).mapped_mem _ _ ((F.obj i).history.supported k hi hai b n)

lemma limit_chronological (k : Ordinal.{0}) (hk : k < limitHeight F)
    (ha : k ∈ limitActive F) :
    (limitPair F k).AmbientPresentation
      (generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k))
      (limit_peak_mem F k ha) (limitGenerator F k)
      (generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio (k+1))) := by
  let i := limitIndex F k hk
  have hi : k < (F.obj i).height := limitIndex_spec F k hk
  let E := (F.obj i).history.toChronologicalHistory.push (limitEmbedding F i)
  have hai : k ∈ E.active := (limitActive_stage F i k hi).mp ha
  have H := E.chronological k hi hai
  have pS : ∀ b n, (E.pair k).peak b n ∈
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k) := by
    intro b n
    rw [← limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le)]
    exact E.peak_mem k hai b n
  have H' := PeakingPairData.AmbientPresentation.congr _ _ _ _ _ _ pS _
    (limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le))
    (limit_generated_eq F i _ (Set.Iio_subset_Iio (Order.add_one_le_iff.mpr hi))) H
  have hz : E.generator k = limitGenerator F k := (limitGenerator_stage F i k hi).symm
  rw [hz] at H'
  exact PeakingPairData.AmbientPresentation.same_data (E.pair k) (limitPair F k)
    (fun b n => (limitPair_peak_stage F i k hi b n).symm)
    (fun a => (E.trace k a).trans (limitPair_trace F k a).symm) _ _ pS (limit_peak_mem F k ha) _ H'

lemma limit_inequivalent (k : Ordinal.{0}) (hk : k < limitHeight F)
    (ha : k ∈ limitActive F) :
    (limitPair F k).PairDistinctOn
      (generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k))
      (limit_peak_mem F k ha) := by
  let i := limitIndex F k hk
  have hi : k < (F.obj i).height := limitIndex_spec F k hk
  let E := (F.obj i).history.toChronologicalHistory.push (limitEmbedding F i)
  have hai : k ∈ E.active := (limitActive_stage F i k hi).mp ha
  have pS : ∀ b n, (E.pair k).peak b n ∈
      generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio k) := by
    intro b n
    rw [← limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le)]
    exact E.peak_mem k hai b n
  have H := PeakingPairData.PairDistinctOn.congr _ _ _ _ pS
    (limit_generated_eq F i _ (Set.Iio_subset_Iio hi.le)) (E.inequivalent k hi hai)
  exact PeakingPairData.PairDistinctOn.same_peaks (E.pair k) (limitPair F k)
    (fun b n => (limitPair_peak_stage F i k hi b n).symm) _ pS (limit_peak_mem F k ha) H

lemma limit_inactive (k : Ordinal.{0}) (ha : k ∉ limitActive F) : limitGenerator F k = 1 := by
  by_cases hk : k < limitHeight F
  · let i := limitIndex F k hk
    have hi : k < (F.obj i).height := limitIndex_spec F k hk
    rw [limitGenerator_stage F i k hi,
      (F.obj i).history.inactive k (fun h => ha ((limitActive_stage F i k hi).mpr h)),map_one]
  · exact dite_eq_right hk

lemma limit_generated :
    generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio (limitHeight F)) = ⊤ := by
  apply top_unique
  intro a _
  have hs : (⋃ i,Set.range (limitEmbedding F i).map) ⊆
      (generatedFamily (Set.range (limitStage F).base) (limitGenerator F) (Set.Iio (limitHeight F)) : Set (limitStage F)) := by
    rintro a ⟨_,⟨i,rfl⟩,⟨x,rfl⟩⟩
    have hx : (limitEmbedding F i).map x ∈ ((F.obj i).history.algebra (Set.Iio (F.obj i).height)).map
        (limitEmbedding F i).map := by
      refine ⟨x,?_,rfl⟩
      rw [ChronologicalData.algebra,(F.obj i).history.generated]
      trivial
    rw [limit_algebra_map F i _ (fun _ h => h)] at hx
    exact generatedFamily_mono _ _ (Set.Iio_subset_Iio (height_le_limit F i)) hx
  exact (show IsClosed (generatedFamily (Set.range (limitStage F).base) (limitGenerator F)
    (Set.Iio (limitHeight F)) : Set (limitStage F)) from inferInstance).closure_subset_iff.mpr hs
      (TracialStage.directLimitHom_dense (F ⋙ forget) a)

def limitHistory : ChronologicalData (limitStage F) (limitHeight F) where
  generator := limitGenerator F
  active := limitActive F
  active_lt := fun k hk => hk.choose
  dependency := limitDependency F
  lower k hk := by
    rw [limitDependency_stage F (limitIndex F k hk) k (limitIndex_spec F k hk)]
    exact (F.obj _).history.lower k (limitIndex_spec F k hk)
  countable k hk := by
    rw [limitDependency_stage F (limitIndex F k hk) k (limitIndex_spec F k hk)]
    exact (F.obj _).history.countable k (limitIndex_spec F k hk)
  pair := limitPair F
  trace := limitPair_trace F
  leftPeak := limitPair_leftPeak F
  supported := limit_supported F
  peak_mem := limit_peak_mem F
  chronological := limit_chronological F
  inactive := limit_inactive F
  inequivalent := limit_inequivalent F
  generated := limit_generated F

def directLimit : ChronologicalStage := ⟨limitStage F,limitHeight F,limitHistory F⟩
def directLimitHom (i : J) : Hom (F.obj i) (directLimit F) where
  embedding := limitEmbedding F i
  height_le := height_le_limit F i
  generator k hk := (limitGenerator_stage F i k hk).symm
  active k hk := (limitActive_stage F i k hk).symm
  dependency k hk := (limitDependency_stage F i k hk).symm
  peak k hk b n := (limitPair_peak_stage F i k hk b n).symm

def directLimitCocone : CategoryTheory.Limits.Cocone F where
  pt := directLimit F
  ι := {app := directLimitHom F
        naturality := fun i j h => by
          apply Hom.ext
          apply TracialStage.Hom.ext
          ext a
          exact limit_embedding_compatible F i j (leOfHom h) a}

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable {J : Type} [LinearOrder J] (S : Set J)
  (F : ∀ j : S, Set.Iic (j : J) ⥤ ChronologicalStage)
  (hF : ∀ (i j : S) (h : i ≤ j), restrictionLE (F j) h = F i)

include hF in
lemma prefix_congr_arrow (i j : S) {k l : J} (hkl : k ≤ l) (hi : l ≤ i) (hj : l ≤ j) :
    arrowMap (F i) k l hkl hi = arrowMap (F j) k l hkl hj := by
  rcases le_total i j with hij | hji
  · have hh := congrArg (fun D => arrowMap D k l hkl hi) (hF i j hij)
    exact hh.symm
  · exact congrArg (fun D => arrowMap D k l hkl hj) (hF j i hji)

lemma prefix_congr_map (i j : S) {k l : J} (hkl : k ≤ l) (hi : l ≤ i) (hj : l ≤ j) :
    (F i).map (homOfLE hkl : ⟨k,hkl.trans hi⟩ ⟶ ⟨l,hi⟩) =
      eqToHom (prefix_congr_obj S F hF i j k (hkl.trans hi) (hkl.trans hj)) ≫
        (F j).map (homOfLE hkl) ≫
        eqToHom (prefix_congr_obj S F hF i j l hi hj).symm := by
  have hh := (Arrow.mk_eq_mk_iff _ _).mp (prefix_congr_arrow S F hF i j hkl hi hj)
  tauto

lemma prefixMap_comp (i j k : S) (hij : i ≤ j) (hjk : j ≤ k) :
    prefixMap S F hF i j hij ≫ prefixMap S F hF j k hjk =
      prefixMap S F hF i k (hij.trans hjk) := by
  simp [prefixMap,prefix_congr_map S F hF j k hij le_rfl hjk,← Functor.map_comp]

def gluePrefixes : S ⥤ ChronologicalStage where
  obj i := (F i).obj ⟨i,le_rfl⟩
  map {i j} f := prefixMap S F hF i j (leOfHom f)
  map_id i := prefixMap_refl S F hF i
  map_comp {i j k} f g := (prefixMap_comp S F hF i j k (leOfHom f) (leOfHom g)).symm

lemma gluePrefixes_arrow (i j : S) (hij : i ≤ j) :
    Arrow.mk ((gluePrefixes S F hF).map (homOfLE hij)) =
      arrowMap (F j) i j hij le_rfl := by
  simp [gluePrefixes,prefixMap,arrowMap]

variable {S F hF}

lemma restrictionLE_of_glued_cocone (l : J)
    (F : ∀ j : Set.Iio l, Set.Iic (j : J) ⥤ ChronologicalStage)
    (hF : ∀ (i j : Set.Iio l) (h : i ≤ j), restrictionLE (F j) h = F i)
    (c : Cocone (gluePrefixes (Set.Iio l) F hF)) (i : J) (hi : i < l) :
    restrictionLE (SuccStruct.ofCocone c) hi.le = F ⟨i,hi⟩ := by
  apply Arrow.functor_ext
  intro k m f
  change arrowMap (restrictionLE (SuccStruct.ofCocone c) hi.le) k m
    (leOfHom f) (show (m : J) ≤ i from m.property) = _
  exact (arrowMap_restrictionLE (SuccStruct.ofCocone c) hi.le k m
      (leOfHom f) (show (m : J) ≤ i from m.property)).trans
    ((SuccStruct.arrowMap_ofCocone c k m (leOfHom f) (lt_of_le_of_lt m.property hi)).trans
      ((gluePrefixes_arrow (Set.Iio l) F hF
        ⟨k,lt_of_le_of_lt k.property hi⟩ ⟨m,lt_of_le_of_lt m.property hi⟩ (leOfHom f)).trans
        (prefix_congr_arrow (Set.Iio l) F hF
          ⟨m,lt_of_le_of_lt m.property hi⟩ ⟨i,hi⟩ (leOfHom f) le_rfl m.property)))

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable (J : Type) [LinearOrder J]

def prefixSystem : Jᵒᵖ ⥤ Type 1 where
  obj j := Set.Iic j.unop ⥤ ChronologicalStage
  map {i j} f := ↾fun D => restrictionLE D (leOfHom f.unop)
  map_id i := by
    apply ConcreteCategory.hom_ext
    intro D
    apply Arrow.functor_ext
    intro k l f
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro D
    apply Arrow.functor_ext
    intro k l f
    rfl

variable [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]

omit orderBotJ in
lemma restriction_extendToSucc [OrderBot J] (j : J) (hj : ¬ IsMax j)
    (D : Set.Iic j ⥤ ChronologicalStage) {X : ChronologicalStage}
    (τ : D.obj ⟨j,le_rfl⟩ ⟶ X) :
    restrictionLE (extendToSucc hj D τ) (Order.le_succ j) = D := by
  apply Arrow.functor_ext
  intro k l f
  exact (arrowMap_restrictionLE (extendToSucc hj D τ) (Order.le_succ j) k l
    (leOfHom f) l.property).trans
    (arrowMap_extendToSucc hj D τ k l (leOfHom f) l.property)

variable (R : SuccessorRule J)

omit succOrderJ orderBotJ in
lemma section_coherent [SuccOrder J] [OrderBot J] (j : J)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ prefixSystem J).sections)
    (i k : Set.Iio j) (h : i ≤ k) :
    restrictionLE (x.val (op k)) h = x.val (op i) :=
  x.property (homOfLE h).op

def recursionData : (prefixSystem J).WellOrderInductionData where
  succ j hj D := extendToSucc hj D (R j hj D).2
  map_succ j hj D := restriction_extendToSucc J j hj D (R j hj D).2
  lift j hj x := by
    letI : Nonempty (Set.Iio j) := ⟨⟨⊥,hj.bot_lt⟩⟩
    exact SuccStruct.ofCocone (directLimitCocone
      (gluePrefixes (Set.Iio j) (fun i => x.val (op i)) (section_coherent J j x)))
  map_lift j hj x i hi := by
    let : Nonempty (Set.Iio j) := ⟨⟨⊥,hj.bot_lt⟩⟩
    exact restrictionLE_of_glued_cocone j (fun i => x.val (op i))
      (section_coherent J j x) (directLimitCocone
        (gluePrefixes (Set.Iio j) (fun i => x.val (op i)) (section_coherent J j x))) i hi

variable [WellFoundedLT J]

def recursivePrefixes : (prefixSystem J).sections :=
  (recursionData J R).sectionsMk ((Functor.const (Set.Iic (⊥ : J))).obj initial)

lemma recursivePrefixes_compatible (i j : J) (h : i ≤ j) :
    restrictionLE ((recursivePrefixes J R).val (op j)) h =
      (recursivePrefixes J R).val (op i) :=
  (recursivePrefixes J R).property (homOfLE h).op

def recursiveTower : J ⥤ ChronologicalStage :=
  (OrderIso.Set.univ : Set.univ ≃o J).symm.monotone.functor ⋙
    gluePrefixes Set.univ (fun j => (recursivePrefixes J R).val (op j.val))
      (fun i j h => recursivePrefixes_compatible J R i j h)

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable (J : Type) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (R : SuccessorRule J)

def earlierPrefixes (j : J) :
    ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ prefixSystem J).sections where
  val k := (recursivePrefixes J R).val (op k.unop.val)
  property {i k} f := recursivePrefixes_compatible J R k.unop.val i.unop.val (leOfHom f.unop)

end ChronologicalStage

open CategoryTheory Cardinal Classical
namespace TracialStage.Hom
variable {X Y : TracialStage} (j : Hom X Y) (f : X →L[ℂ] ℂ) (hf : IsPureState f)

def pureLift : Y →L[ℂ] ℂ :=
  ((j.uep f hf).exists_unique_pure j.injective hf).choose
lemma pureLift_pure : IsPureState (j.pureLift f hf) :=
  ((j.uep f hf).exists_unique_pure j.injective hf).choose_spec.1
end TracialStage.Hom

namespace ChronologicalStage
variable (K : Type) (hK : 𝔠 ≤ #K) (X : ChronologicalStage)

def pureList : K → X.stage →L[ℂ] ℂ :=
  if h : #({f : X.stage →L[ℂ] ℂ // IsPureState f}) ≤ 𝔠 then
    (exists_pureState_list K hK h X.stage.reference X.stage.reference_spec.1).choose
  else fun _ => X.stage.reference

lemma pureList_pure (k : K) : IsPureState (pureList K hK X k) := by
  classical
  unfold pureList
  split_ifs with h
  · exact (exists_pureState_list K hK h X.stage.reference X.stage.reference_spec.1).choose_spec.1 k
  · exact X.stage.reference_spec.1

variable {J : Type} [LinearOrder J]
  (σ : J × K → J) (hσ : ∀ p, p.1 ≤ σ p)
  (j : J) (D : Set.Iic j ⥤ ChronologicalStage)

def scheduledTarget : (D.obj ⟨j,le_rfl⟩).stage →L[ℂ] ℂ :=
  if h : ∃ p, σ p = j then
    let p := h.choose
    let hp : p.1 ≤ j := (hσ p).trans_eq h.choose_spec
    let e := (D.map (homOfLE hp : ⟨p.1,hp⟩ ⟶ ⟨j,le_rfl⟩)).embedding
    e.pureLift (pureList K hK (D.obj ⟨p.1,hp⟩) p.2)
      (pureList_pure K hK (D.obj ⟨p.1,hp⟩) p.2)
  else (D.obj ⟨j,le_rfl⟩).stage.reference

lemma scheduledTarget_pure : IsPureState (scheduledTarget K hK σ hσ j D) := by
  classical
  unfold scheduledTarget
  split_ifs
  · exact TracialStage.Hom.pureLift_pure _ _ _
  · exact (D.obj ⟨j,le_rfl⟩).stage.reference_spec.1

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable {J : Type} [LinearOrder J] [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]

variable (K : Type) (hK : 𝔠 ≤ #K)

def Treated (η : K) (a : Arrow ChronologicalStage) : Prop :=
  ∃ F : a.right.stage →L[ℂ] ℂ, ∃ hF : IsPureState F,
    restrictState a.hom.embedding.map F = pureList K hK a.left η ∧
    PureStateEquivalent a.right.stage.reference a.right.stage.reference_spec.1 F hF

end ChronologicalStage

open Cardinal Ordinal

open CategoryTheory Topology

open CategoryTheory Cardinal

section

universe u v
section
variable (A : Type u) [CStarAlgebra A]

instance liftStarRing : StarRing (ULift.{v} A) where
  star a := ⟨star a.down⟩
  star_involutive a := by cases a; simp
  star_mul a b := by cases a; cases b; exact congrArg ULift.up (star_mul _ _)
  star_add a b := by cases a; cases b; exact congrArg ULift.up (star_add _ _)

instance liftStarModule : StarModule ℂ (ULift.{v} A) where
  star_smul c a := by cases a; exact congrArg ULift.up (star_smul c _)

instance liftCStarRing : CStarRing (ULift.{v} A) where
  norm_mul_self_le a := by
    change ‖a.down‖ * ‖a.down‖ ≤ ‖star a.down * a.down‖
    exact CStarRing.norm_mul_self_le a.down

instance liftCStarAlgebra : CStarAlgebra (ULift.{v} A) where

def liftStarAlgEquiv : A ≃⋆ₐ[ℂ] ULift.{v} A where
  toFun := ULift.up
  invFun := ULift.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp] lemma liftStarAlgEquiv_apply (a : A) : liftStarAlgEquiv A a = ULift.up a := rfl

end
end

universe u v w

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Tracial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder
namespace TracialStage

variable (X : TracialStage) {B : Type} [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  (hB : IsSimpleCStar B) (ψ : CAR →⋆ₐ[ℂ] B) (φ : B →⋆ₐ[ℂ] X)
  (hφ : Function.Injective φ) (hbase : ∀ a, φ (ψ a) = X.base a)
  (hU : PureUEP φ) (f : X →L[ℂ] ℂ) (hf : IsPureState f)
  (hfr : IsPureState (restrictState φ f))

include hB hφ hbase hU hf hfr in

theorem exists_supported_peak_pair_unconditional :
    ∃ Q : PeakingPairData X,
      (∀ a, Q.trace a = X.trace a) ∧ Q.state false = X.reference ∧
      Q.state true = f ∧ (∀ n, Q.peak false n = X.base (carPeak n)) ∧
      (∀ i n, Q.peak i n ∈ Set.range φ) := by
  have hp := core_reference_peaks X ψ φ hbase
  have hpr := (hp.restrict φ hφ).1.isPureState
  obtain ⟨γ,hγ⟩ := KOS.homogeneity hB
    (core_infinite X ψ φ hbase) (restrictState φ f)
    (restrictState φ X.reference) hfr hpr
  have he : restrictState γ.toStarAlgHom (restrictState φ f) =
      restrictState φ X.reference := by
    ext a
    exact hγ a
  let Q := homogeneousCARPeakPair ψ φ hφ X.reference f hp hfr hf.1 hU γ he
    X.positiveTrace X.tracial X.positiveTrace_normalized X.positiveTrace_faithful
  refine ⟨Q,fun _ => rfl,rfl,rfl,fun n => hbase _,?_⟩
  intro i n
  cases i
  · exact ⟨ψ (carPeak n),rfl⟩
  · exact ⟨γ (ψ (carPeak n)),rfl⟩

end TracialStage

section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
namespace ChronologicalStage
variable (X : ChronologicalStage)

lemma exists_supported_pair_unconditional
    (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set Ordinal.{0}, S.Countable ∧ S ⊆ Set.Iio X.height ∧
      ∃ Q : PeakingPairData X.stage,
        (∀ a,Q.trace a = X.stage.trace a) ∧ Q.state false = X.stage.reference ∧
        Q.state true = f ∧ (∀ n,Q.peak false n = X.stage.base (carPeak n)) ∧
        (∀ i n,Q.peak i n ∈ X.history.algebra S) := by
  obtain ⟨S,hSc,hS,hclosed,hsep,hsimple,hfr,_⟩ := X.history.countable_determination f hf
  let : TopologicalSpace.SeparableSpace (X.history.algebra S) := hsep.separableSpace
  let ψ := X.coreBase S
  let φ := (X.history.algebra S).subtype
  have hbase : ∀ a,φ (ψ a) = X.stage.base a := fun _ => rfl
  obtain ⟨Q,ht,h0,h1,hl,hp⟩ := TracialStage.exists_supported_peak_pair_unconditional X.stage
    hsimple ψ φ Subtype.val_injective hbase (X.history.pureUEP S hS hclosed) f hf hfr
  refine ⟨S,hSc,hS,Q,ht,h0,h1,hl,?_⟩
  intro i n
  obtain ⟨a,ha⟩ := hp i n
  exact ha ▸ a.property

theorem exists_joining_successor_unconditional
    (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ Y : ChronologicalStage, ∃ j : Hom X Y,
      Y.height = X.height+1 ∧
      ∃ F : Y.stage →L[ℂ] ℂ, ∃ hF : IsPureState F,
        restrictState j.embedding.map F = f ∧
        PureStateEquivalent Y.stage.reference Y.stage.reference_spec.1 F hF := by
  by_cases he : PureStateEquivalent X.stage.reference X.stage.reference_spec.1 f hf
  · exact ⟨X.inactiveSuccessor,X.inactiveHom,rfl,f,hf,rfl,he⟩
  · obtain ⟨S,hSc,hS,Q,ht,h0,h1,hl,hp⟩ := X.exists_supported_pair_unconditional f hf
    have hne : ¬ PureStateEquivalent (Q.state false) (Q.peaks false).isPureState
        (Q.state true) (Q.peaks true).isPureState := by
      simpa only [h0,h1] using he
    let hs := Q.separated_of_inequivalent hne
    obtain ⟨F,hF,hr,hjoin⟩ := TracialStage.hnn_reference_join X.stage Q hs ht f hf h0 h1
    exact ⟨X.hnnSuccessor Q hs ht hl S hS hSc hp hne,
      X.hnnHom Q hs ht hl S hS hSc hp hne,rfl,F,hF,hr,hjoin⟩

end ChronologicalStage
end

open CategoryTheory Cardinal Classical
namespace ChronologicalStage
variable (X : ChronologicalStage)

def joiningChoice_unconditional (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    Σ Y : ChronologicalStage, Hom X Y :=
  ⟨(X.exists_joining_successor_unconditional f hf).choose,
    (X.exists_joining_successor_unconditional f hf).choose_spec.choose⟩

variable (K : Type) (hK : 𝔠 ≤ #K)
variable {J : Type} [LinearOrder J] [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]
  (σ : J × K → J) (hσ : ∀ p,p.1 ≤ σ p)

def scheduledRule_unconditional : SuccessorRule J := fun j _ D =>
  joiningChoice_unconditional (D.obj ⟨j,le_rfl⟩) (scheduledTarget K hK σ hσ j D)
    (scheduledTarget_pure K hK σ hσ j D)

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory Cardinal
namespace ChronologicalStage

abbrev FullRule_unconditional
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p) :=
  scheduledRule_unconditional ConstructionIndex constructionIndex_cardinal σ hσ

abbrev fullTower_unconditional
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p) := recursiveTower ConstructionIndex (FullRule_unconditional σ hσ)

end ChronologicalStage

universe u v w

end NaimarkZFC

end

end OAI
end


