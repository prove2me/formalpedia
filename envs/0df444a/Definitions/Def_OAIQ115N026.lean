-- Prove2me | Definitions.Def_OAIQ115N026
-- name    : OAIQ115N026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T02:13:02.219156+00:00
-- url     : https://prove2.me/theorems/5db396bc-2eec-47d8-8846-8d914bf178a5
-- title:
--   Definitions bundle OAIQ115N026 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 108 declarations of OpenAI's Lean: 13 definitions, 1 inductive type or structure, 4 instances and 90 theorems. The definitions and types are `OAI.NaimarkZFC.ChronologicalStage.Hom.id`, `OAI.NaimarkZFC.ChronologicalStage.SuccessorRule`, `OAI.NaimarkZFC.ChronologicalStage.coreBase`, `OAI.NaimarkZFC.ChronologicalStage.inactiveSuccessor`, `OAI.NaimarkZFC.ChronologicalStage.prefixMap`, `OAI.NaimarkZFC.KOS.Stage`, `OAI.NaimarkZFC.KOS.Step`, `OAI.NaimarkZFC.KOS.data`, `OAI.NaimarkZFC.TracialStage.LimitCarrier`, `OAI.NaimarkZFC.TracialStage.bond`, `OAI.NaimarkZFC.TracialStage.directLimit`, `OAI.NaimarkZFC.TracialStage.directLimitHom`, `OAI.NaimarkZFC.TracialStage.limitIncl`, `OAI.NaimarkZFC.TracialStage.limitTrace`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean), [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Homogeneity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Homogeneity.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean), [`Naimark_Operators`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Operators.lean), [`Naimark_Recursion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Recursion.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N021`, `OAIQ115N022`, `OAIQ115N023` and `OAIQ115N024` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ115N028`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N021
import Definitions.Def_OAIQ115N022
import Definitions.Def_OAIQ115N023
import Definitions.Def_OAIQ115N024

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.PeakingPairData.pairHNN_cstar _root_.OAI.NaimarkZFC.carOrder _root_.OAI.NaimarkZFC.constructionIndex_orderBot _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
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

theorem traceCorner_tracial (a b : B.Corner) : B.traceCorner (a*b) = B.traceCorner (b*a) :=
  cornerTrace_tracial _ _ B.modelTrace 2 (atomicTrace_mul B.atoms B.amalgam) a b

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

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

theorem hnnTrace_tracial (a b : B.HNNAlgebra) : B.hnnTrace (a*b) = B.hnnTrace (b*a) :=
  B.traceCorner_tracial a b

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
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem hnnExpectation_left (a : A) (x : B.HNNAlgebra) :
    B.hnnExpectation (B.hnnBase a*x) = a*B.hnnExpectation x :=
  matrixCornerExpectation_left B.embedBase B.modelExpectation
    (atomicExpectation_factor_mul B.atoms B.amalgam false)
    (atomicExpectation_mul_factor B.atoms B.amalgam false) a x

theorem hnnExpectation_right (x : B.HNNAlgebra) (a : A) :
    B.hnnExpectation (x*B.hnnBase a) = B.hnnExpectation x*a :=
  matrixCornerExpectation_right B.embedBase B.modelExpectation
    (atomicExpectation_factor_mul B.atoms B.amalgam false)
    (atomicExpectation_mul_factor B.atoms B.amalgam false) x a

end PeakingPairData
end

open scoped CStarAlgebra ComplexOrder

open Topology

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology
section
universe u v

theorem pureUEP_ordinal_chain
    (A : Ordinal.{u} → Type v) [∀ i, CStarAlgebra (A i)]
    (incl : ∀ {i j : Ordinal.{u}}, i ≤ j → A i →⋆ₐ[ℂ] A j)
    (hid : ∀ i, incl (le_refl i) = StarAlgHom.id ℂ (A i))
    (hcomp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
      (incl hjk).comp (incl hij) = incl (hij.trans hjk))
    (L : Ordinal.{u})
    (hnext : ∀ i < L, PureUEP (incl (show i ≤ i+1 by exact le_self_add)))
    (hcont : ∀ j ≤ L, Order.IsSuccLimit j →
      Dense (⋃ k : {k : Ordinal.{u} // k < j}, Set.range (incl k.property.le)))
    (j : Ordinal.{u}) (hj : j ≤ L) (i : Ordinal.{u}) (hij : i ≤ j) :
    PureUEP (incl hij) := by
  induction j using Ordinal.limitRecOn generalizing i with
  | zero =>
    have hi : i = 0 := le_antisymm hij bot_le
    subst i
    rw [hid]
    exact PureUEP.id
  | add_one j ih =>
    by_cases he : i = j+1
    · subst i
      rw [hid]
      exact PureUEP.id
    · have hlt : i < j+1 := lt_of_le_of_ne hij he
      have hi : i ≤ j := by simpa only [Order.lt_add_one_iff] using hlt
      have hjL : j < L := (show j < j+1 from lt_add_one j).trans_le hj
      have hu := (ih hjL.le i hi).comp (hnext j hjL)
      rwa [hcomp] at hu
  | limit j hjlim ih =>
    by_cases he : i = j
    · subst i
      rw [hid]
      exact PureUEP.id
    · have hi : i < j := lt_of_le_of_ne hij he
      let J := {k : Ordinal.{u} // i ≤ k ∧ k < j}
      have hd : Dense (⋃ k : J, Set.range (incl k.property.2.le)) := by
        apply (hcont j hj hjlim).mono
        intro a ha
        obtain ⟨k,b,rfl⟩ := Set.mem_iUnion.mp ha
        let m : J := ⟨max i k.val,le_max_left _ _,max_lt hi k.property⟩
        apply Set.mem_iUnion.mpr
        refine ⟨m, incl (le_max_right i k.val) b, ?_⟩
        have hh := congrArg (fun φ : A k.val →⋆ₐ[ℂ] A j => φ b)
          (hcomp (le_max_right i k.val) m.property.2.le)
        exact hh
      exact PureUEP.of_dense_cover (fun k : J => A k.val) (incl hij)
        (fun k => incl k.property.1) (fun k => incl k.property.2.le)
        (fun k => hcomp k.property.1 k.property.2.le)
        (fun k => ih k.val k.property.2 (k.property.2.le.trans hj) i k.property.1) hd

end

open Topology
section

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

theorem bridge_ordinal_pureUEP
    (hid : ∀ i, incl (le_refl i) = StarAlgHom.id ℂ (A i))
    (hcomp : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k),
      (incl hjk).comp (incl hij) = incl (hij.trans hjk))
    (j : Ordinal.{u}) (hj : j ≤ L) (i : Ordinal.{u}) (hij : i ≤ j) :
    PureUEP (incl hij) := by
  apply pureUEP_ordinal_chain A incl hid hcomp L _ hcont j hj i hij
  intro k hk
  exact ((hnext k hk).properties (bridge_ordinal_simple A incl L hbase hnext hi hcont k hk.le)).2.2

end

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
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C)

theorem hnn_kernel_reduced {x : B.HNNAlgebra} (hx : B.hnnExpectation x = 0) :
    x ∈ closure (hnnReducedSpan B.hnnBase B.hnnLetter B.turnCentered : Set B.HNNAlgebra) :=
  hnn_kernel_mem_closure_reducedSpan B.hnnBase B.hnnLetter B.turnCentered
    B.hnnExpectation B.hnnExpectation_base B.hnnExpectation_word
    (hnnWordSpan_dense B.hnnBase B.hnnLetter B.turnCentered B.hnnLetter_star
      B.turnCenter B.turnRemainder B.turnCenter_centered B.hnnLetter_turn B.hnn_generated) hx

variable (ι : A →⋆ₐ[ℂ] C) (hp : ∀ i n, ι (B.peak i n) = D.peak i n)
  (F : C →L[ℂ] A) (hfix : ∀ a, F (ι a) = a)
  (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp F))
  (hleft : ∀ a x, F (ι a*x) = a*F x) (hright : ∀ x a, F (x*ι a) = F x*a)
  (ht : ∀ x, B.trace (F x) = D.trace x)
  (J : B.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra)
  (hJa : ∀ a, J (B.hnnBase a) = D.hnnBase (ι a))
  (hJv : ∀ i, J (B.hnnLetter i) = D.hnnLetter i)

include hJa hJv in
theorem hnn_mapped_kernel {x : B.HNNAlgebra} (hx : B.hnnExpectation x = 0) :
    J x ∈ closure (hnnReducedSpan (D.hnnBase.comp ι) D.hnnLetter B.turnCentered : Set D.HNNAlgebra) :=
  hnnReducedClosure_map B.hnnBase (D.hnnBase.comp ι) B.hnnLetter D.hnnLetter
    B.turnCentered J hJa hJv (B.hnn_kernel_reduced hx)

include hp hfix hstate hleft hright ht in

theorem hnn_free_blocks (r : List (Bool × D.HNNAlgebra)) (hne : r ≠ [])
    (hr : ∀ p ∈ r, HNNCenteredBlock ι D.hnnBase D.hnnLetter B.turnCentered F p.1 p.2)
    (hc : r.IsChain (fun p q => p.1 ≠ q.1)) :
    F (D.hnnExpectation (wordValue r)) = 0 := by
  have htrace (a : A) : D.trace (ι a) = B.trace a := by rw [← ht,hfix]
  have hKL (i : Bool) (a : A) (ha : B.turnCentered i a) : D.turnCentered i (ι a) := by
    change (D.input false).expectation (!i) (ι a) = 0
    rw [B.expectation_natural D ι hp htrace]
    exact ha
  exact hnn_alternating_expectation_zero ι D.hnnBase D.hnnLetter B.turnCentered D.turnCentered
    hKL F D.hnnExpectation
    (fun x hx i a b => B.turnCentered_of_expectation_zero D ι hp F hfix hstate
      hleft hright ht x hx i a b)
    D.hnnExpectation_word D.hnnExpectation_left D.hnnExpectation_right
    D.hnnExpectation_base r hne hr hc

end PeakingPairData

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

theorem hnn_two_factors_dense (J : B.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra)
    (hv : ∀ i, J (B.hnnLetter i) = D.hnnLetter i)
    (V : Bool → Type*) [∀ i, Ring (V i)] [∀ i, StarRing (V i)] [∀ i, Algebra ℂ (V i)]
    (φ : ∀ i, V i →⋆ₐ[ℂ] D.HNNAlgebra)
    (hb : Set.range D.hnnBase ⊆ ⋃ i, Set.range (φ i))
    (hj : Set.range J ⊆ ⋃ i, Set.range (φ i)) :
    Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (φ i)) : Set D.HNNAlgebra) := by
  apply D.hnn_generated.mono
  apply StarAlgebra.adjoin_mono
  intro x hx
  rcases hx with hx | ⟨i,rfl⟩
  · exact hb hx
  · exact hj ⟨B.hnnLetter i,hv i⟩

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

variable (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
  (jQ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra) (jB : B.HNNAlgebra →⋆ₐ[ℂ] E.HNNAlgebra)

theorem leftHNNFamily_dense (hv : ∀ i, jQ (Q.hnnLetter i) = D.hnnLetter i) :
    Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (leftHNNFamily B Q D jQ i)) : Set D.HNNAlgebra) := by
  apply Q.hnn_two_factors_dense D jQ hv (pairHNN B Q) (leftHNNFamily B Q D jQ)
  · rintro _ ⟨x,rfl⟩; exact Set.mem_iUnion.mpr ⟨false,x,rfl⟩
  · rintro _ ⟨x,rfl⟩; exact Set.mem_iUnion.mpr ⟨true,x,rfl⟩

theorem rightHNNFamily_dense (hv : ∀ i, jB (B.hnnLetter i) = E.hnnLetter i) :
    Dense (StarAlgebra.adjoin ℂ (⋃ i, Set.range (rightHNNFamily B Q E jB i)) : Set E.HNNAlgebra) := by
  apply B.hnn_two_factors_dense E jB hv (pairHNN B Q) (rightHNNFamily B Q E jB)
  · rintro _ ⟨x,rfl⟩; exact Set.mem_iUnion.mpr ⟨true,x,rfl⟩
  · rintro _ ⟨x,rfl⟩; exact Set.mem_iUnion.mpr ⟨false,x,rfl⟩

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
-- module Solutions.OAIQ115_Naimark.Naimark_CAR
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty
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
section

theorem carStage_normalizedTrace_peak (n : ℕ) (f : CARStage n →ₗ[ℂ] ℂ)
    (h1 : f 1 = 1) (htr : ∀ a b, f (a*b) = f (b*a)) :
    f (carStagePeak n) = (2:ℂ)⁻¹^n := by
  induction n with
  | zero => simpa only [carStagePeak, pow_zero] using h1
  | succ n ih =>
    let F : CStarMatrix Bool Bool (CARStage n) →ₗ[ℂ] ℂ := f
    have hFtr (a b) : F (a*b) = F (b*a) := htr a b
    let g : CARStage n →ₗ[ℂ] ℂ := f.comp (carStep n).toLinearMap
    have hg1 : g 1 = 1 := by
      change f (carStep n 1) = 1
      rw [map_one,h1]
    have hgtr (a b : CARStage n) : g (a*b) = g (b*a) := by
      change f (carStep n (a*b)) = f (carStep n (b*a))
      rw [map_mul (carStep n),map_mul (carStep n),htr]
    have hi := ih g hg1 hgtr
    have hc := trace_matrix_corner F hFtr (carStagePeak n)
    change F (matrixSingle false false (carStagePeak n)) = _
    change F (matrixScalarHom (CARStage n) (carStagePeak n)) = _ at hi
    calc
      F (matrixSingle false false (carStagePeak n)) =
          (2:ℂ)⁻¹ * F (matrixScalarHom (CARStage n) (carStagePeak n)) := by
        rw [hc]
        ring
      _ = (2:ℂ)⁻¹^(n+1) := by rw [hi,pow_succ]; ring

variable {B : Type*} [CStarAlgebra B]

theorem carPeak_ambientTrace (φ : CAR →⋆ₐ[ℂ] B) (τ : B →ₗ[ℂ] ℂ)
    (h1 : τ 1 = 1) (htr : ∀ a b, τ (a*b) = τ (b*a)) (n : ℕ) :
    τ (φ (carPeak n)) = (2:ℂ)⁻¹^n := by
  apply carStage_normalizedTrace_peak n
    (τ.comp (φ.comp (carInclude n)).toLinearMap)
  · change τ ((φ.comp (carInclude n)) 1) = 1
    rw [map_one,h1]
  · intro a b
    change τ ((φ.comp (carInclude n)) (a*b)) = τ ((φ.comp (carInclude n)) (b*a))
    rw [map_mul (φ.comp (carInclude n)),map_mul (φ.comp (carInclude n)),htr]

end

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

include hφ hp hg hgs hu he in

theorem homogeneousCARPeak_peaks : Peaks (fun n => φ (γ (ψ (carPeak n)))) g := by
  have hsmall := (hp.restrict φ hφ).1
  exact (hsmall.mapEquiv γ (isState_restrict φ g hgs) he).extend φ
    (hu _ hg) g hgs rfl

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.constructionIndex_orderBot _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
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

open Filter Topology

open Filter Topology
section

theorem cauchySeq_of_tail_geometric_steps {X : Type*} [PseudoMetricSpace X]
    (x : ℕ → X) (k : ℕ)
    (h : ∀ n, k ≤ n → dist (x n) (x (n+1)) ≤ (1/2:ℝ)^n) : CauchySeq x := by
  rw [← cauchySeq_shift k]
  apply cauchySeq_of_le_geometric (1/2) ((1/2)^k) (by norm_num)
  intro n
  have hh := h (n+k) (Nat.le_add_left k n)
  simpa only [pow_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,mul_comm] using hh

end

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pure_state_finite_excision (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : A, 0 ≤ x ∧ ‖x‖ = 1 ∧ f x = 1 ∧
      ∀ a ∈ F, ‖x * (a - f a • (1:A)) * x‖ < ε := by
  let g := positiveOfSquares f hf.1.2
  let π := g.gnsNonUnitalStarAlgHom
  let ξ := gnsVector g
  have hg : g 1 = 1 := ((isState_iff f).mp hf.1).1
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one g hg
  have hπ : IsIrreducible π := pure_gns_irreducible f hf.1 hf
  have hcoeff (b : A) : ⟪ξ,π b ξ⟫_ℂ = f b := gnsVector_coefficient g b
  have hs : ∀ᶠ e : ExcisionIndex (vectorNullAlgebra π ξ) in atTop,
      ∀ a ∈ F, ‖pureExcisionNet π ξ e * (a - f a • (1:A)) *
        pureExcisionNet π ξ e‖ < ε := by
    apply (F.eventually_all).mpr
    intro a _
    have hh := (pureExcisionNet_excision π hπ ξ hξ a).norm
    simpa only [hcoeff,norm_zero] using (tendsto_order.mp hh).2 ε (by simpa using hε)
  obtain ⟨e,he⟩ := hs.exists
  let x := pureExcisionNet π ξ e
  have hx : f x = 1 := by
    rw [← hcoeff,pureExcisionNet_fixes π (irreducible_map_one π hπ)]
    simp only [inner_self_eq_norm_sq_to_K,hξ]
    norm_num
  refine ⟨x,pureExcisionNet_nonneg π ξ e,le_antisymm (pureExcisionNet_norm π ξ e) ?_,hx,he⟩
  have hh := f.le_opNorm x
  rw [hf.1.1,hx,norm_one,one_mul] at hh
  exact hh

omit [PartialOrder A] [StarOrderedRing A] in

theorem compressed_vector_coefficient_bound
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : A) (hx : IsSelfAdjoint x) (ζ : H) (hζ : ‖ζ‖ ≤ 1)
    (hy : 0 < ‖π x ζ‖) (a : A) (c : ℂ) :
    ‖⟪(‖π x ζ‖:ℂ)⁻¹ • π x ζ, π a ((‖π x ζ‖:ℂ)⁻¹ • π x ζ)⟫_ℂ - c‖ ≤
      ‖π x ζ‖⁻¹^2 * ‖x*(a-c • (1:A))*x‖ := by
  let y := π x ζ
  let η := (‖y‖:ℂ)⁻¹ • y
  have hη : ‖η‖ = 1 := by
    simp only [η,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg y)]
    exact inv_mul_cancel₀ (show ‖y‖ ≠ 0 from hy.ne')
  have he : ⟪η,π a η⟫_ℂ - c = ⟪η,π (a-c • (1:A)) η⟫_ℂ := by
    simp only [map_sub,map_smul,sub_apply,smul_apply,hone,one_apply_eq_self,
      inner_sub_right,inner_smul_right,inner_self_eq_norm_sq_to_K,hη]
    norm_num
  have hcompress : ⟪y,π (a-c • (1:A)) y⟫_ℂ = ⟪ζ,π (x*(a-c • (1:A))*x) ζ⟫_ℂ := by
    simp only [y,map_mul,mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_right (π x),← ContinuousLinearMap.star_eq_adjoint,
      ← map_star,hx.star_eq]
  have hb : ‖⟪ζ,π (x*(a-c • (1:A))*x) ζ⟫_ℂ‖ ≤ ‖x*(a-c • (1:A))*x‖ := by
    exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.le_opNorm _ ζ) (norm_nonneg ζ)).trans (by
        have hn := NonUnitalStarAlgHom.norm_apply_le π (x*(a-c • (1:A))*x)
        calc
          ‖ζ‖ * (‖π (x*(a-c • (1:A))*x)‖ * ‖ζ‖) ≤
            1 * (‖x*(a-c • (1:A))*x‖ * 1) := by gcongr
          _ = _ := by ring))
  change ‖⟪η,π a η⟫_ℂ - c‖ ≤ _
  rw [he]
  simp only [η,map_smul,inner_smul_left,inner_smul_right,norm_mul,RCLike.norm_conj,
    norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg y),hcompress]
  calc
    ‖y‖⁻¹ * (‖y‖⁻¹ * ‖⟪ζ,π (x*(a-c • (1:A))*x) ζ⟫_ℂ‖) ≤
      ‖y‖⁻¹ * (‖y‖⁻¹ * ‖x*(a-c • (1:A))*x‖) := by gcongr
    _ = _ := by ring

theorem faithful_vector_pure_approximation
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (hi : Function.Injective π)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : H, ‖η‖ = 1 ∧ ∀ a ∈ F, ‖⟪η,π a η⟫_ℂ - f a‖ < ε := by
  obtain ⟨x,hx,hxn,hfx,hsmall⟩ := pure_state_finite_excision f hf F (ε/4) (by positivity)
  have hnorm : ‖π x‖ = 1 := by
    rw [(NonUnitalStarAlgHom.isometry π hi).norm_map_of_map_zero (map_zero π),hxn]
  obtain ⟨ζ,hζ,hζx⟩ := (π x).exists_lt_apply_of_lt_opNorm (r := 1/2) (by rw [hnorm]; norm_num)
  let η := (‖π x ζ‖:ℂ)⁻¹ • π x ζ
  have hy : 0 < ‖π x ζ‖ := lt_trans (by norm_num) hζx
  have hη : ‖η‖ = 1 := by
    simp only [η,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hy.ne']
  refine ⟨η,hη,fun a ha => ?_⟩
  have hb := compressed_vector_coefficient_bound π hone x (IsSelfAdjoint.of_nonneg hx)
    ζ hζ.le hy a (f a)
  change ‖⟪η,π a η⟫_ℂ - f a‖ ≤ _ at hb
  have hinv : ‖π x ζ‖⁻¹ ≤ 2 := by
    have hh : (1/2:ℝ)⁻¹ = 2 := by norm_num
    rw [← hh]
    exact (inv_le_inv₀ hy (show 0 < (1/2:ℝ) by norm_num)).mpr hζx.le
  calc
    _ ≤ ‖π x ζ‖⁻¹^2 * ‖x*(a-f a • (1:A))*x‖ := hb
    _ ≤ 4 * ‖x*(a-f a • (1:A))*x‖ := by
      gcongr
      nlinarith [inv_nonneg.mpr hy.le]
    _ < 4*(ε/4) := by gcongr; exact hsmall a ha
    _ = ε := by ring

theorem simple_pure_inner_orbit_finite
    (hA : IsSimpleCStar A) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary A, ∀ a ∈ F, ‖⟪ξ,π (star (u:A)*a*(u:A)) ξ⟫_ℂ - f a‖ < ε := by
  obtain ⟨η,hη,he⟩ := faithful_vector_pure_approximation π (irreducible_map_one π hπ)
    (simple_nonzeroStarHom_injective hA π hπ.1) f hf F ε hε
  obtain ⟨u,hu⟩ := irreducible_unitary_vector π hπ ξ η (hξ.trans hη.symm)
  refine ⟨u,fun a ha => ?_⟩
  simpa only [map_mul,map_star,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,hu] using he a ha

end

open Filter Topology
open scoped InnerProductSpace

open Topology

open Topology
section
attribute [local instance] generatedFamily_isClosed
universe u
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (base : Set A) (v : Ordinal.{u} → A) (S : Set Ordinal.{u})

attribute [local instance] OAI.NaimarkZFC.retainedOrdinalAlgebra_order
attribute [local instance] OAI.NaimarkZFC.retainedOrdinalAlgebra_starOrder
omit [PartialOrder A] [StarOrderedRing A] in

theorem retainedOrdinal_pureUEP (L : Ordinal.{u})
    (hbase : IsSimpleCStar (retainedOrdinalAlgebra base v S 0))
    (hnext : ∀ j < L, BridgeSuccessor
      (retainedOrdinalInclusion base v S (show j ≤ j+1 by exact le_self_add))) :
    PureUEP (retainedOrdinalInclusion base v S (show 0 ≤ L by exact bot_le)) := by
  apply bridge_ordinal_pureUEP (fun j => retainedOrdinalAlgebra base v S j)
    (fun h => retainedOrdinalInclusion base v S h) L hbase hnext
    (fun h => retainedOrdinalInclusion_injective base v S h)
    (fun j _ hj => retainedOrdinalInclusion_continuous base v S j hj)
    (retainedOrdinalInclusion_refl base v S)
    (fun h h' => retainedOrdinalInclusion_comp base v S h h') L le_rfl 0 bot_le

end

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Stages
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.constructionIndex_orderBot
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

lemma reference_peaks : Peaks (fun n => X.base (carPeak n)) X.reference :=
  carPeak_peaks.extend X.base (X.baseUEP carVector carVector_isPure) X.reference
    X.reference_spec.1.1 X.reference_spec.2

instance instCategory : CategoryTheory.Category TracialStage where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp f := by ext a; rfl
  comp_id f := by ext a; rfl
  assoc f g h := by ext a; rfl

end TracialStage
end

open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace

open scoped InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpaceH : CompleteSpace H]

theorem difference_projection_bound {ι : Type*} [Fintype ι] (b w : ι → H)
    (hb : Orthonormal ℂ b) (ho : ∀ i j, ⟪b i,w j⟫_ℂ = 0)
    (v : H) (δ : ℝ) (hδ : 0 ≤ δ)
    (hv : ∀ i, ‖⟪b i-w i,v⟫_ℂ‖ ≤ δ) :
    let D := Submodule.span ℂ (Set.range fun i => b i-w i)
    letI : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    ‖D.starProjection v‖ ≤ Fintype.card ι * δ := by
  classical
  dsimp only
  let D := Submodule.span ℂ (Set.range fun i => b i-w i)
  let : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let q := D.starProjection v
  have hq := difference_span_coefficients b w hb ho (D.starProjection_apply_mem v)
  have hcoef (i : ι) : ‖⟪b i,q⟫_ℂ‖ ≤ ‖q‖ := by
    simpa only [hb.norm_eq_one i,one_mul] using norm_inner_le_norm (b i) q
  have hn : ‖⟪q,v⟫_ℂ‖ ≤ ‖q‖ * (Fintype.card ι * δ) := by
    calc
      ‖⟪q,v⟫_ℂ‖ = ‖∑ i, starRingEnd ℂ (⟪b i,q⟫_ℂ) * ⟪b i-w i,v⟫_ℂ‖ := by
        conv_lhs => rw [show q = ∑ i, ⟪b i,q⟫_ℂ • (b i-w i) from hq]
        simp only [sum_inner,inner_smul_left]
      _ ≤ ∑ i, ‖starRingEnd ℂ (⟪b i,q⟫_ℂ) * ⟪b i-w i,v⟫_ℂ‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, ‖q‖ * δ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul,RCLike.norm_conj]
        exact mul_le_mul (hcoef i) (hv i) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by simp [mul_left_comm,mul_comm,mul_assoc]
  have he : ‖q‖^2 = (⟪q,v⟫_ℂ).re := by
    exact (D.re_inner_starProjection_eq_normSq v).symm
  have hre : (⟪q,v⟫_ℂ).re ≤ ‖⟪q,v⟫_ℂ‖ := Complex.re_le_norm _
  change ‖q‖ ≤ _
  have hC : 0 ≤ (Fintype.card ι : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  by_cases hzero : ‖q‖ = 0
  · simpa only [hzero] using hC
  · have hpos : 0 < ‖q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    apply (mul_le_mul_iff_right₀ hpos).mp
    nlinarith only [he,hn,hre]

theorem gram_sum_projection_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x y : ι → H) (b : κ → H) (c : κ → ι → ℂ)
    (hb : Orthonormal ℂ b) (hc : ∀ j, ∑ i, c j i • x i = b j)
    (ho : ∀ i j, ⟪x i,y j⟫_ℂ = 0)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ) (i : ι) :
    let w := fun j => ∑ l, c j l • y l
    let D := Submodule.span ℂ (Set.range fun j => b j-w j)
    letI : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    ‖D.starProjection (x i+y i)‖ ≤ Fintype.card κ * (δ * ∑ j, ∑ l, ‖c j l‖) := by
  classical
  dsimp only
  let w := fun j => ∑ l, c j l • y l
  have hobw (j k) : ⟪b j,w k⟫_ℂ = 0 := by
    rw [← hc j]
    exact gram_cross_zero x y ho (c j) (c k)
  apply difference_projection_bound b w hb hobw _ _ (by positivity)
  intro j
  have hbi : ⟪b j,y i⟫_ℂ = 0 := by
    rw [← hc j]
    simp only [sum_inner,inner_smul_left,ho,mul_zero,Finset.sum_const_zero]
  have hwi : ⟪w j,x i⟫_ℂ = 0 := by
    rw [inner_eq_zero_symm]
    simp only [w,inner_sum,inner_smul_right,ho,mul_zero,Finset.sum_const_zero]
  have he : ⟪b j-w j,x i+y i⟫_ℂ = ⟪b j,x i⟫_ℂ-⟪w j,y i⟫_ℂ := by
    rw [inner_add_right,inner_sub_left,inner_sub_left,hbi,hwi]
    abel
  rw [he,← hc j]
  have hbase := gram_combination_error x y δ hδ hgram (c j) (Pi.single i 1)
  have hbase' : ‖⟪∑ l, c j l • x l,x i⟫_ℂ - ⟪w j,y i⟫_ℂ‖ ≤ δ * ∑ l, ‖c j l‖ := by
    simpa only [Pi.single_apply,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',
      Finset.mem_univ,ite_true, if_true,apply_ite,norm_one,norm_zero,mul_one] using hbase
  apply hbase'.trans
  apply mul_le_mul_of_nonneg_left _ hδ
  exact Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (Finset.mem_univ j)

theorem gram_difference_projection_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (x y : ι → H) (b : κ → H) (c : κ → ι → ℂ) (d : ι → κ → ℂ)
    (hc : ∀ j, ∑ i, c j i • x i = b j) (hd : ∀ i, ∑ j, d i j • b j = x i)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hgram : ∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ) (i : ι) :
    let w := fun j => ∑ l, c j l • y l
    let D := Submodule.span ℂ (Set.range fun j => b j-w j)
    letI : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    ‖D.starProjection (x i-y i)-(x i-y i)‖ ≤
      2 * Real.sqrt δ * (∑ l, ‖gramResidual c d i l‖) := by
  classical
  dsimp only
  let w := fun j => ∑ l, c j l • y l
  let D := Submodule.span ℂ (Set.range fun j => b j-w j)
  let : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let r := ∑ l, gramResidual c d i l • y l
  have he : ∑ l, gramResidual c d i l • x l = 0 := by
    rw [gramResidual_apply]
    simp only [hc,hd,sub_self]
  have hr := gram_zero_combination_bound x y δ hδ hgram (gramResidual c d i) he
  have hm : x i-y i+r ∈ D := by
    have heq : x i-y i+r = ∑ j, d i j • (b j-w j) := by
      rw [show r = y i-∑ j, d i j • w j from gramResidual_apply y c d i]
      simp only [smul_sub,Finset.sum_sub_distrib,hd]
      abel
    rw [heq]
    exact D.sum_mem (fun j _ => D.smul_mem _ (Submodule.subset_span (Set.mem_range_self j)))
  have hp : D.starProjection (x i-y i+r) = x i-y i+r :=
    Submodule.starProjection_eq_self_iff.mpr hm
  have heq : D.starProjection (x i-y i)-(x i-y i) = r-D.starProjection r := by
    rw [map_add] at hp
    exact sub_eq_sub_iff_add_eq_add.mpr (hp.trans (add_comm _ _))
  rw [heq]
  have hrp : ‖D.starProjection r‖ ≤ ‖r‖ := by
    exact (D.starProjection.le_opNorm r).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right D.starProjection_norm_le (norm_nonneg r))
  calc
    ‖r-D.starProjection r‖ ≤ ‖r‖+‖D.starProjection r‖ := norm_sub_le _ _
    _ ≤ 2*‖r‖ := by linarith
    _ ≤ 2 * (Real.sqrt δ * (∑ l, ‖gramResidual c d i l‖)) :=
      mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by ring

theorem approximate_gram_projection {ι : Type*} [Fintype ι] (x : ι → H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ι → H,
      (∀ i j, ⟪x i,y j⟫_ℂ = 0) →
      (∀ i j, ‖⟪x i,x j⟫_ℂ-⟪y i,y j⟫_ℂ‖ ≤ δ) →
      ∃ P : H →L[ℂ] H, IsStarProjection P ∧
        (∀ v, P v ∈ Submodule.span ℂ (Set.range x ∪ Set.range y)) ∧
        (∀ i, ‖P (x i-y i)-(x i-y i)‖ < ε) ∧
        (∀ i, ‖P (x i+y i)‖ < ε) := by
  classical
  obtain ⟨m,b,c,d,hb,hc,hd⟩ := finite_orthonormal_coordinates x
  let C : ℝ := 1 + m * (∑ j, ∑ l, ‖c j l‖)
  let E : ℝ := 1 + ∑ i, ∑ l, ‖gramResidual c d i l‖
  have hC : 0 < C := by dsimp [C]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  let δ : ℝ := min (ε/(2*C)) ((ε/(4*E))^2)
  have hδ : 0 < δ := lt_min (by positivity) (sq_pos_of_pos (by positivity))
  have hδC : δ*C ≤ ε/2 := by
    have hh := min_le_left (ε/(2*C)) ((ε/(4*E))^2)
    change δ ≤ ε/(2*C) at hh
    have hh' := (le_div_iff₀ (by positivity : 0 < 2*C)).mp hh
    nlinarith only [hh']
  have hδE : Real.sqrt δ * E ≤ ε/4 := by
    have hh : δ ≤ (ε/(4*E))^2 := min_le_right _ _
    have hs : Real.sqrt δ ≤ ε/(4*E) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rwa [Real.sq_sqrt hδ.le]
    have hh' := (le_div_iff₀ (by positivity : 0 < 4*E)).mp hs
    nlinarith only [hh']
  refine ⟨δ,hδ,fun y ho hgram => ?_⟩
  let w := fun j => ∑ l, c j l • y l
  let D := Submodule.span ℂ (Set.range fun j => b j-w j)
  let : FiniteDimensional ℂ D := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  let M := Submodule.span ℂ (Set.range x ∪ Set.range y)
  have hDM : D ≤ M := by
    apply Submodule.span_le.mpr
    rintro v ⟨j,rfl⟩
    apply M.sub_mem
    · rw [← hc j]
      exact M.sum_mem (fun i _ => M.smul_mem _ (Submodule.subset_span (Or.inl (Set.mem_range_self i))))
    · exact M.sum_mem (fun i _ => M.smul_mem _ (Submodule.subset_span (Or.inr (Set.mem_range_self i))))
  refine ⟨D.starProjection,isStarProjection_starProjection,
    fun v => hDM (D.starProjection_apply_mem v),?_,?_⟩
  · intro i
    have hi := gram_difference_projection_bound x y b c d hc hd δ hδ.le hgram i
    have hsum : (∑ l, ‖gramResidual c d i l‖) ≤ E := by
      have hh : (∑ l, ‖gramResidual c d i l‖) ≤ ∑ j, ∑ l, ‖gramResidual c d j l‖ :=
        Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg (gramResidual c d j l)))
          (Finset.mem_univ i)
      dsimp only [E]
      linarith
    calc
      _ ≤ 2 * Real.sqrt δ * (∑ l, ‖gramResidual c d i l‖) := hi
      _ ≤ 2 * Real.sqrt δ * E := by gcongr
      _ ≤ ε/2 := by nlinarith only [hδE]
      _ < ε := by linarith
  · intro i
    have hi := gram_sum_projection_bound x y b c hb hc ho δ hδ.le hgram i
    have hm : (Fintype.card (Fin m) : ℝ) * (δ * ∑ j, ∑ l, ‖c j l‖) ≤ δ*C := by
      simp only [Fintype.card_fin]
      dsimp only [C]
      nlinarith only [hδ.le]
    exact (hi.trans (hm.trans hδC)).trans_lt (by linarith)

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
namespace KOS
variable {A : Type*} [CStarAlgebra A]

theorem resolvent_commutator (a : A) (ha : IsSelfAdjoint a) (b : A) :
    b * saResolvent a (-Complex.I) - saResolvent a (-Complex.I) * b =
      saResolvent a (-Complex.I) * (a*b-b*a) * saResolvent a (-Complex.I) := by
  let R := saResolvent a (-Complex.I)
  obtain ⟨hl,hr⟩ := saResolvent_inverse a ha (-Complex.I) (by simp)
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hl hr
  have he : (a+Complex.I • (1:A))*b-b*(a+Complex.I • (1:A)) = a*b-b*a := by
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    abel
  change b*R-R*b = R*(a*b-b*a)*R
  calc
    b*R-R*b = (R*(a+Complex.I • (1:A)))*b*R-R*b*((a+Complex.I • (1:A))*R) := by
      rw [hr,hl,one_mul,mul_one]
    _ = R*((a+Complex.I • (1:A))*b-b*(a+Complex.I • (1:A)))*R := by noncomm_ring
    _ = R*(a*b-b*a)*R := by rw [he]

lemma resolvent_commutator_norm (a : A) (ha : IsSelfAdjoint a) (b : A) :
    ‖b * saResolvent a (-Complex.I) - saResolvent a (-Complex.I) * b‖ ≤ ‖b*a-a*b‖ := by
  have hR : ‖saResolvent a (-Complex.I)‖ ≤ 1 := by
    simpa using saResolvent_norm_le a ha (-Complex.I) (by simp)
  rw [resolvent_commutator a ha b]
  calc
    _ ≤ ‖saResolvent a (-Complex.I)‖ * ‖a*b-b*a‖ * ‖saResolvent a (-Complex.I)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖a*b-b*a‖ * 1 := by gcongr
    _ = ‖b*a-a*b‖ := by simp only [one_mul,mul_one,norm_sub_rev]

lemma saCayley_affine_resolvent (a : A) (ha : IsSelfAdjoint a) :
    saCayley a = 1 - (2*Complex.I) • saResolvent a (-Complex.I) := by
  have hr := (saResolvent_inverse a ha (-Complex.I) (by simp)).2
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hr
  rw [saCayley_eq a ha]
  calc
    _ = saResolvent a (-Complex.I) * (a+Complex.I • (1:A)) -
        (2*Complex.I) • saResolvent a (-Complex.I) := by
      simp only [mul_sub,mul_add,mul_smul_comm,mul_one]
      module
    _ = _ := by rw [hr]

theorem saCayley_commutator_norm (a : A) (ha : IsSelfAdjoint a) (b : A) :
    ‖b*saCayley a-saCayley a*b‖ ≤ 2*‖b*a-a*b‖ := by
  rw [saCayley_affine_resolvent a ha]
  have he : b*(1-(2*Complex.I) • saResolvent a (-Complex.I)) -
      (1-(2*Complex.I) • saResolvent a (-Complex.I))*b =
      -(2*Complex.I) • (b*saResolvent a (-Complex.I)-saResolvent a (-Complex.I)*b) := by
    simp only [mul_sub,sub_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc]
    module
  rw [he,norm_smul]
  have hn : ‖-(2*Complex.I)‖ = (2:ℝ) := by simp
  rw [hn]
  exact mul_le_mul_of_nonneg_left (resolvent_commutator_norm a ha b) (by norm_num)

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]

lemma projectionSwitch_unitary (a : A) (ha : IsSelfAdjoint a) :
    projectionSwitch a ∈ unitary A := by
  apply Unitary.smul_mem_of_mem _ (saCayley_unitary _ ((ha.add ha).sub (IsSelfAdjoint.one A)))
  simp [Unitary.mem_iff]

lemma projectionSwitch_eq (a : A) (ha : IsSelfAdjoint a) :
    projectionSwitch a = (-Complex.I) • (1:A) -
      (2:ℂ) • saResolvent (a+a-1) (-Complex.I) := by
  rw [projectionSwitch,saCayley_affine_resolvent _ ((ha.add ha).sub (IsSelfAdjoint.one A)),smul_sub,smul_smul]
  congr 1
  congr 1
  calc
    _ = -(2*(Complex.I*Complex.I)) := by ring
    _ = _ := by norm_num

lemma projectionSwitch_sub_one (a : A) (ha : IsSelfAdjoint a) :
    projectionSwitch a - 1 = (-(1+Complex.I)) •
      (saResolvent (a+a-1) (-Complex.I) * (a+a)) := by
  let R := saResolvent (a+a-1) (-Complex.I)
  have hr := (saResolvent_inverse (a+a-1) ((ha.add ha).sub (IsSelfAdjoint.one A)) (-Complex.I) (by simp)).2
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hr
  have hR : R*(a+a) = 1 + (1-Complex.I) • R := by
    calc
      R*(a+a) = R*(a+a-1+Complex.I • (1:A)) + (1-Complex.I) • R := by
        simp only [mul_add,mul_sub,mul_smul_comm,mul_one]
        module
      _ = _ := by rw [hr]
  rw [projectionSwitch_eq a ha]
  change (-Complex.I) • (1:A) - (2:ℂ) • R - 1 = -(1+Complex.I) • (R*(a+a))
  rw [hR,smul_add,smul_smul]
  have hc : -(1+Complex.I)*(1-Complex.I) = (-2:ℂ) := by
    calc
      _ = -(1-Complex.I^2) := by ring
      _ = _ := by norm_num
  rw [hc]
  module

lemma projectionSwitch_add_one (a : A) (ha : IsSelfAdjoint a) :
    projectionSwitch a + 1 = (1-Complex.I) •
      (saResolvent (a+a-1) (-Complex.I) * ((a-1)+(a-1))) := by
  let R := saResolvent (a+a-1) (-Complex.I)
  have hr := (saResolvent_inverse (a+a-1) ((ha.add ha).sub (IsSelfAdjoint.one A)) (-Complex.I) (by simp)).2
  rw [Algebra.algebraMap_eq_smul_one,neg_smul,sub_neg_eq_add] at hr
  have hR : R*((a-1)+(a-1)) = 1 - (1+Complex.I) • R := by
    calc
      R*((a-1)+(a-1)) = R*(a+a-1+Complex.I • (1:A)) - (1+Complex.I) • R := by
        simp only [mul_add,mul_sub,mul_smul_comm,mul_one]
        module
      _ = _ := by rw [hr]
  rw [projectionSwitch_eq a ha]
  change (-Complex.I) • (1:A) - (2:ℂ) • R + 1 = (1-Complex.I) • (R*((a-1)+(a-1)))
  rw [hR,smul_sub,smul_smul]
  have hc : (1-Complex.I)*(1+Complex.I) = (2:ℂ) := by
    calc
      _ = 1-Complex.I^2 := by ring
      _ = _ := by norm_num
  rw [hc]
  module

lemma projectionSwitch_commutator_norm (a : A) (ha : IsSelfAdjoint a) (b : A) :
    ‖b*projectionSwitch a-projectionSwitch a*b‖ ≤ 4*‖b*a-a*b‖ := by
  rw [projectionSwitch,mul_smul_comm,smul_mul_assoc,← smul_sub,norm_smul]
  simp only [norm_neg,Complex.norm_I,one_mul]
  apply (saCayley_commutator_norm _ ((ha.add ha).sub (IsSelfAdjoint.one A)) b).trans
  have he : b*(a+a-1)-(a+a-1)*b = (b*a-a*b)+(b*a-a*b) := by noncomm_ring
  rw [he]
  have hn := norm_add_le (b*a-a*b) (b*a-a*b)
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projectionSwitch_fixed_error (a : A) (ha : IsSelfAdjoint a)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    ‖π (projectionSwitch a) v-v‖ ≤ 4*‖π a v‖ := by
  have hR : ‖π (saResolvent (a+a-1) (-Complex.I))‖ ≤ 1 := by
    exact (NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _).trans (by
      simpa using saResolvent_norm_le _ ((ha.add ha).sub (IsSelfAdjoint.one A)) (-Complex.I) (by simp))
  have hc : ‖(-(1+Complex.I):ℂ)‖ ≤ 2 := by
    simpa only [norm_neg,norm_one,Complex.norm_I,one_add_one_eq_two] using norm_add_le (1:ℂ) Complex.I
  have he : π (projectionSwitch a) v-v = π (projectionSwitch a-1) v := by
    simp only [map_sub,map_one,sub_apply,one_apply_eq_self]
  rw [he,projectionSwitch_sub_one a ha,map_smul,map_mul,smul_apply,mul_apply_eq_comp,
    map_add,add_apply,norm_smul]
  calc
    _ ≤ 2 * (‖π (saResolvent (a+a-1) (-Complex.I))‖ * ‖π a v+π a v‖) :=
      mul_le_mul hc ((π (saResolvent (a+a-1) (-Complex.I))).le_opNorm _) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * (1 * (‖π a v‖+‖π a v‖)) := by gcongr; exact norm_add_le _ _
    _ = _ := by ring

lemma projectionSwitch_negated_error (a : A) (ha : IsSelfAdjoint a)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    ‖π (projectionSwitch a) v+v‖ ≤ 4*‖π a v-v‖ := by
  have hR : ‖π (saResolvent (a+a-1) (-Complex.I))‖ ≤ 1 := by
    exact (NonUnitalStarAlgHom.norm_apply_le π.toNonUnitalStarAlgHom _).trans (by
      simpa using saResolvent_norm_le _ ((ha.add ha).sub (IsSelfAdjoint.one A)) (-Complex.I) (by simp))
  have hc : ‖(1-Complex.I:ℂ)‖ ≤ 2 := by
    simpa only [norm_one,Complex.norm_I,one_add_one_eq_two] using norm_sub_le (1:ℂ) Complex.I
  have he : π (projectionSwitch a) v+v = π (projectionSwitch a+1) v := by
    simp only [map_add,map_one,add_apply,one_apply_eq_self]
  rw [he,projectionSwitch_add_one a ha,map_smul,map_mul,smul_apply,mul_apply_eq_comp,
    map_add,add_apply,map_sub,map_one,sub_apply,one_apply_eq_self,norm_smul]
  calc
    _ ≤ 2 * (‖π (saResolvent (a+a-1) (-Complex.I))‖ * ‖(π a v-v)+(π a v-v)‖) :=
      mul_le_mul hc ((π (saResolvent (a+a-1) (-Complex.I))).le_opNorm _) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * (1 * (‖π a v-v‖+‖π a v-v‖)) := by gcongr; exact norm_add_le _ _
    _ = _ := by ring

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projectionSwitch_vector_error (a : A) (ha : IsSelfAdjoint a)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) :
    ‖π (projectionSwitch a) ξ-η‖ ≤
      2*(‖π a (ξ-η)-(ξ-η)‖+‖π a (ξ+η)‖) := by
  have hd := projectionSwitch_negated_error a ha π (ξ-η)
  have hs := projectionSwitch_fixed_error a ha π (ξ+η)
  have he : (2:ℂ) • (π (projectionSwitch a) ξ-η) =
      (π (projectionSwitch a) (ξ-η)+(ξ-η)) +
      (π (projectionSwitch a) (ξ+η)-(ξ+η)) := by
    simp only [map_sub,map_add]
    module
  have hn := norm_add_le (π (projectionSwitch a) (ξ-η)+(ξ-η))
    (π (projectionSwitch a) (ξ+η)-(ξ+η))
  rw [← he,norm_smul,Complex.norm_ofNat] at hn
  linarith

theorem corrected_projectionSwitch
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (a : A) (ha : IsSelfAdjoint a) (r : ℝ)
    (herr : 2*(‖π a (ξ-η)-(ξ-η)‖+‖π a (ξ+η)‖) ≤ r) (hr : r ≤ 1) :
    ∃ u : unitary A, π u ξ = η ∧ ∀ b : A,
      ‖b*(u:A)-(u:A)*b‖ ≤ 192*‖b‖*r+4*‖b*a-a*b‖ := by
  let ρ := irreducibleUnitalRepresentation π hπ
  let w : unitary A := ⟨projectionSwitch a,projectionSwitch_unitary a ha⟩
  have hw : ρ (w:A) ∈ unitary (H →L[ℂ] H) := by
    rw [Unitary.mem_iff]
    constructor
    · rw [← map_star,← map_mul,(Unitary.mem_iff.mp w.property).1,map_one]
    · rw [← map_star,← map_mul,(Unitary.mem_iff.mp w.property).2,map_one]
  have hwn : ‖π (w:A) ξ‖ = 1 :=
    ((ρ (w:A)).norm_map_of_mem_unitary hw ξ).trans hξ
  have hwe : ‖π (w:A) ξ-η‖ ≤ r :=
    (projectionSwitch_vector_error a ha ρ ξ η).trans herr
  obtain ⟨v,hv,hvn⟩ := irreducible_near_unitary_vector π hπ
    (π (w:A) ξ) η hwn hη (hwe.trans hr)
  refine ⟨v*w,?_,fun b => ?_⟩
  · change π ((v:A)*(w:A)) ξ = η
    rw [map_mul,mul_apply_eq_comp]
    exact hv
  · change ‖b*((v:A)*(w:A))-((v:A)*(w:A))*b‖ ≤ _
    refine (unitary_commutator_product v w b).trans ?_
    have hn := projectionSwitch_commutator_norm a ha b
    change ‖b*(w:A)-(w:A)*b‖ ≤ _ at hn
    have hvr : ‖(v:A)-1‖ ≤ 96*r := hvn.trans (by gcongr)
    nlinarith [norm_nonneg b]

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma near_congruence_operator (ξ η : H) (s t : ℝ) (hξ : ‖ξ‖ = 1)
    (hs : ⟪ξ,η⟫_ℂ = (s:ℂ)) (ht : ‖η-ξ‖ ≤ t) (ht' : t ≤ 1/2) :
    ∃ D : H →L[ℂ] H, ‖D‖ ≤ 6*t ∧
      (1+D) η = (Real.sqrt s : ℂ) • ξ ∧
      star (1+D) ξ = ((Real.sqrt s)⁻¹ : ℝ) • ξ := by
  have ht0 : 0 ≤ t := (norm_nonneg _).trans ht
  have hss : |s-1| ≤ t := by
    have hi := norm_inner_le_norm (𝕜 := ℂ) ξ (η-ξ)
    rw [inner_sub_right,hs,inner_self_eq_norm_sq_to_K,hξ] at hi
    norm_num at hi
    have hn : ‖(s:ℂ)-1‖ = |s-1| := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [hn] at hi
    exact hi.trans ht
  have hslo : 1/2 ≤ s := by have := neg_le_of_abs_le hss; linarith
  have hsp : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have hrp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hsp
  have hrsq : (Real.sqrt s)^2 = s := Real.sq_sqrt hsp.le
  have hrlo : 1/2 ≤ Real.sqrt s := by nlinarith [Real.sqrt_nonneg s]
  have hrerr : |Real.sqrt s - 1| ≤ t := by
    apply abs_le.mpr
    obtain ⟨hl,hu⟩ := abs_le.mp hss
    constructor <;> nlinarith [Real.sqrt_nonneg s]
  have hci : |(Real.sqrt s)⁻¹-1| ≤ 2*t := by
    have he : (Real.sqrt s)⁻¹-1 = (1-Real.sqrt s)/Real.sqrt s := by field_simp
    rw [he,abs_div,abs_sub_comm,abs_of_pos hrp]
    apply (div_le_iff₀ hrp).mpr
    exact hrerr.trans (by nlinarith)
  have hsi : s⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hsp).mpr
    linarith
  let w : H := η-(s:ℂ) • ξ
  have hw : ⟪ξ,w⟫_ℂ = 0 := by
    simp only [w,inner_sub_right,inner_smul_right,hs,inner_self_eq_norm_sq_to_K,hξ]
    norm_num
  have hwn : ‖w‖ ≤ 2*t := by
    have he : w = (η-ξ)+(1-(s:ℂ)) • ξ := by dsimp [w]; module
    have hn : ‖1-(s:ℂ)‖ = |s-1| := by
      rw [norm_sub_rev,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [he]
    calc
      _ ≤ ‖η-ξ‖+‖(1-(s:ℂ)) • ξ‖ := norm_add_le _ _
      _ = ‖η-ξ‖+|s-1| := by rw [norm_smul,hn,hξ,mul_one]
      _ ≤ 2*t := by linarith
  let D : H →L[ℂ] H := ((Real.sqrt s)⁻¹-1) • InnerProductSpace.rankOne ℂ ξ ξ -
    s⁻¹ • InnerProductSpace.rankOne ℂ w ξ
  refine ⟨D,?_,?_,?_⟩
  · calc
      ‖D‖ ≤ ‖((Real.sqrt s)⁻¹-1) • InnerProductSpace.rankOne ℂ ξ ξ‖ +
          ‖s⁻¹ • InnerProductSpace.rankOne ℂ w ξ‖ := norm_sub_le _ _
      _ = |(Real.sqrt s)⁻¹-1| + s⁻¹*‖w‖ := by
        rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
          InnerProductSpace.norm_rankOne,InnerProductSpace.norm_rankOne,hξ,
          abs_of_pos (inv_pos.mpr hsp)]
        ring
      _ ≤ 6*t := by nlinarith [mul_le_mul hsi hwn (norm_nonneg w) (by norm_num : (0:ℝ)≤2)]
  · simp only [D,add_apply,one_apply_eq_self,sub_apply,smul_apply,
      InnerProductSpace.rankOne_apply,hs,Complex.coe_smul,smul_smul]
    rw [inv_mul_cancel₀ hsp.ne',one_smul]
    have hmul : (Real.sqrt s)⁻¹*s = Real.sqrt s := by
      calc
        _ = (Real.sqrt s)⁻¹*((Real.sqrt s)^2) := congrArg ((Real.sqrt s)⁻¹ * ·) hrsq.symm
        _ = _ := by rw [pow_two,← mul_assoc,inv_mul_cancel₀ hrp.ne',one_mul]
    have he : ((Real.sqrt s)⁻¹-1)*s = Real.sqrt s-s := by
      calc
        _ = (Real.sqrt s)⁻¹*s-s := by ring
        _ = _ := by rw [hmul]
    rw [he]
    dsimp [w]
    module
  · have hw' : ⟪w,ξ⟫_ℂ = 0 := inner_eq_zero_symm.mp hw
    simp only [D,star_add,star_one,star_sub,star_smul,star_trivial,
      ContinuousLinearMap.star_eq_adjoint,InnerProductSpace.adjoint_rankOne,
      add_apply,one_apply_eq_self,sub_apply,smul_apply,InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K,hξ,hw']
    norm_num only [one_pow,Complex.ofReal_one,one_smul,zero_smul,smul_zero,sub_zero]
    module

variable {A : Type*} [CStarAlgebra A]

lemma irreducible_near_congruence
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (P : A) (hP : IsSelfAdjoint P) (ξ : H) (hξ : ‖ξ‖ = 1)
    (t : ℝ) (ht : ‖π P ξ-ξ‖ ≤ t) (ht' : t ≤ 1/2) :
    ∃ b : A, ‖b-1‖ ≤ 48*t ∧ π (b*P*star b) ξ = ξ := by
  let s : ℝ := (⟪ξ,π P ξ⟫_ℂ).re
  have hs : ⟪ξ,π P ξ⟫_ℂ = (s:ℂ) := by
    apply Complex.ext
    · rfl
    change (⟪ξ,π P ξ⟫_ℂ).im = 0
    have hp := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hP.map π)).im_inner_self_apply ξ
    exact hp
  obtain ⟨D,hD,hDη,hDξ⟩ := near_congruence_operator ξ (π P ξ) s t hξ hs ht ht'
  let M := Submodule.span ℂ ({ξ,π P ξ} : Set H)
  have : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  obtain ⟨a,ha,hact⟩ := irreducible_adjoint_transitivity π hπ M D
  have hξM : ξ ∈ M := Submodule.subset_span (by simp)
  have hηM : π P ξ ∈ M := Submodule.subset_span (by simp)
  have hA : π (1+a) (π P ξ) = (Real.sqrt s : ℂ) • ξ := by
    rw [map_add,add_apply,irreducible_map_one π hπ,one_apply_eq_self,(hact _ hηM).1]
    exact hDη
  have hA' : π (star (1+a)) ξ = ((Real.sqrt s)⁻¹ : ℝ) • ξ := by
    rw [star_add,star_one,map_add,add_apply,irreducible_map_one π hπ,
      one_apply_eq_self,(hact _ hξM).2]
    simpa only [star_add,star_one,add_apply,one_apply_eq_self] using hDξ
  have hsp : 0 < s := by
    have hi := norm_inner_le_norm (𝕜 := ℂ) ξ (π P ξ-ξ)
    rw [inner_sub_right,hs,inner_self_eq_norm_sq_to_K,hξ] at hi
    norm_num at hi
    have hn : ‖(s:ℂ)-1‖ = |s-1| := by
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    rw [hn] at hi
    have hl := neg_le_of_abs_le (hi.trans ht)
    linarith
  refine ⟨1+a,by simpa using ha.trans (by linarith : 8*‖D‖ ≤ 48*t),?_⟩
  rw [map_mul,map_mul,mul_apply_eq_comp,mul_apply_eq_comp,hA',← Complex.coe_smul,
    map_smul,map_smul,hA,smul_smul,← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hsp).ne',Complex.ofReal_one,one_smul]

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [fintypeι : Fintype ι]

lemma row_defect_zero (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (x : ι → A) (v : H) (h : π (rowAverage x 1) v = v) :
    vectorFunctional π v (rowDefectTest x) = 0 := by
  rw [rowDefectTest,vectorFunctional_square]
  simp only [map_sub,sub_apply,hone,one_apply_eq_self,h,sub_self,norm_zero,
    Complex.ofReal_zero,zero_pow (by norm_num : 2 ≠ 0)]

end KOS

open scoped InnerProductSpace
namespace KOS
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma upperCutoff_positive_form (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (s : ℝ) :
    0 ≤ cfc (upperCutoff s) T * (T-s • (1:H →L[ℂ] H)) * cfc (upperCutoff s) T := by
  let f := upperCutoff s
  have hid : cfc (fun t : ℝ => t-s) T = T-s • (1:H →L[ℂ] H) := by
    rw [cfc_sub _ _ T,cfc_id' ℝ T hT,cfc_const s T hT]
    rfl
  have hf : Continuous f := continuous_upperCutoff s
  rw [← hid,← cfc_mul f (fun t : ℝ => t-s) T (continuous_upperCutoff s).continuousOn (by fun_prop),
    ← cfc_mul (fun t : ℝ => f t*(t-s)) f T (hf.mul (continuous_id.sub continuous_const)).continuousOn hf.continuousOn]
  apply cfc_nonneg
  intro t _
  dsimp [f,upperCutoff]
  by_cases h : 0 ≤ t-s
  · rw [max_eq_left h]
    positivity
  · rw [max_eq_right (le_of_not_ge h)]
    simp

lemma upperCutoff_range_lower (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (s : ℝ)
    (v : H) (hv : v ∈ (cfc (upperCutoff s) T).range) :
    s*‖v‖^2 ≤ (⟪v,T v⟫_ℂ).re := by
  obtain ⟨w,rfl⟩ := hv
  let P := cfc (upperCutoff s) T
  have hP : IsSelfAdjoint P := cfc_predicate (upperCutoff s) T
  have hp := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (upperCutoff_positive_form T hT s)).re_inner_nonneg_right w
  have he : ⟪w,(P*(T-s • (1:H →L[ℂ] H))*P) w⟫_ℂ =
      ⟪P w,T (P w)⟫_ℂ-(s:ℂ)*⟪P w,P w⟫_ℂ := by
    rw [mul_apply_eq_comp,mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    rw [← ContinuousLinearMap.star_eq_adjoint,hP.star_eq]
    simp only [sub_apply,smul_apply,one_apply_eq_self,inner_sub_right]
    rw [← Complex.coe_smul,inner_smul_right]
  change 0 ≤ (⟪w,(P*(T-s • (1:H →L[ℂ] H))*P) w⟫_ℂ).re at hp
  rw [he,Complex.sub_re,inner_self_eq_norm_sq_to_K] at hp
  have her : (⟪P w,P w⟫_ℂ).re = ‖P w‖^2 := by
    simpa using (norm_sq_eq_re_inner (𝕜 := ℂ) (P w)).symm
  have hp' := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (upperCutoff_positive_form T hT s)).re_inner_nonneg_right w
  change 0 ≤ (⟪w,(P*(T-s • (1:H →L[ℂ] H))*P) w⟫_ℂ).re at hp'
  rw [he,Complex.sub_re,Complex.mul_re,her] at hp'
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hp'
  change s*‖P w‖^2 ≤ (⟪P w,T (P w)⟫_ℂ).re
  nlinarith

theorem upperCutoff_finiteDimensional_range
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (k s : ℝ) (hks : k < s)
    (hbound : ∀ v ∈ Mᗮ, ‖T v‖ ≤ k*‖v‖) :
    FiniteDimensional ℂ (cfc (upperCutoff s) T).range := by
  let P := cfc (upperCutoff s) T
  let D := P.range
  let F : D →ₗ[ℂ] M := M.orthogonalProjectionOnto.toLinearMap.comp D.subtype
  apply FiniteDimensional.of_injective F
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0

  have hv0 : M.orthogonalProjectionOnto (v:H) = 0 := hv
  have hvo : (v:H) ∈ Mᗮ := (Submodule.orthogonalProjectionOnto_eq_zero_iff).mp hv0
  have hl := upperCutoff_range_lower T hT s (v:H) v.property
  have hu := (Complex.re_le_norm ⟪(v:H),T (v:H)⟫_ℂ).trans (norm_inner_le_norm (v:H) (T (v:H)))
  have hb := hbound (v:H) hvo
  have hz : ‖(v:H)‖ = 0 := by
    by_contra hn
    have hp := lt_of_le_of_ne (norm_nonneg (v:H)) (Ne.symm hn)
    have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (v:H))
    nlinarith [mul_pos (sub_pos.mpr hks) (sq_pos_of_pos hp)]
  apply Subtype.ext
  exact norm_eq_zero.mp hz

end KOS

open scoped InnerProductSpace CStarAlgebra
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

theorem no_compacts_large_vector
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hno : ∀ a : A, IsCompactOperator (π a) → π a = 0)
    (a : A) (ha : 0 ≤ a) (han : ‖π a‖ = 1)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (k : ℝ) (hk : k < 1) :
    ∃ v : H, ‖v‖ = 1 ∧ v ∈ Mᗮ ∧ k < ‖π a v‖ := by
  classical
  by_contra! hn
  have hb : ∀ v ∈ Mᗮ, ‖π a v‖ ≤ k*‖v‖ := by
    intro v hv
    by_cases hz : v = 0
    · simp only [hz,map_zero,norm_zero,mul_zero,le_refl]
    · have hp := norm_pos_iff.mpr hz
      let w := (‖v‖⁻¹:ℂ) • v
      have hwn : ‖w‖ = 1 := norm_smul_inv_norm hz
      have hwM : w ∈ Mᗮ := Mᗮ.smul_mem _ hv
      have he := hn w hwn hwM
      change ‖π a ((‖v‖⁻¹:ℂ) • v)‖ ≤ k at he
      rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_norm] at he
      simpa only [mul_comm] using (inv_mul_le_iff₀ hp).mp he
  let s : ℝ := (k+1)/2
  have hks : k < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hpa : 0 ≤ π a := map_nonneg π ha
  let : FiniteDimensional ℂ (cfc (upperCutoff s) (π a)).range :=
    upperCutoff_finiteDimensional_range (π a) (IsSelfAdjoint.of_nonneg hpa) M k s hks hb
  have hc : IsCompactOperator (π (cfc (upperCutoff s) a)) := by
    rw [π.map_cfc (upperCutoff s) a (continuous_upperCutoff s).continuousOn]
    exact isCompactOperator_of_finiteDimensional_range _
  have hz : cfc (upperCutoff s) (π a) = 0 := by
    rw [← π.map_cfc (upperCutoff s) a (continuous_upperCutoff s).continuousOn]
    exact hno _ hc
  have hneq : π a ≠ 0 := by intro he; simp [he] at han
  let : Nontrivial (H →L[ℂ] H) := nontrivial_of_ne _ _ hneq
  have hspec : (1:ℝ) ∈ spectrum ℝ (π a) := by
    rw [← han]
    exact CStarAlgebra.norm_mem_spectrum_of_nonneg hpa
  have he := eqOn_of_cfc_eq_cfc (hz.trans (cfc_const_zero ℝ (π a)).symm)
    (continuous_upperCutoff s).continuousOn continuous_const.continuousOn (IsSelfAdjoint.of_nonneg hpa)
  have he1 := he hspec
  change max (1-s) 0 = 0 at he1
  rw [max_eq_left (sub_nonneg.mpr hs1.le)] at he1
  linarith

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pure_vector_approximation_orthogonal
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hi : Function.Injective π)
    (hno : ∀ a : A, IsCompactOperator (π a) → π a = 0)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : H, ‖η‖ = 1 ∧ η ∈ Mᗮ ∧
      ∀ a ∈ F, ‖⟪η,π a η⟫_ℂ-f a‖ < ε := by
  obtain ⟨x,hx,hxn,_,hsmall⟩ := pure_state_finite_excision f hf F (ε/4) (by positivity)
  have hxsa : IsSelfAdjoint x := IsSelfAdjoint.of_nonneg hx
  have hpxsa : IsSelfAdjoint (π x) := hxsa.map π
  have hnorm : ‖π x‖ = 1 := by
    rw [(NonUnitalStarAlgHom.isometry π hi).norm_map_of_map_zero (map_zero π),hxn]
  let N := M.map (π x).toLinearMap
  let : FiniteDimensional ℂ N := inferInstanceAs (FiniteDimensional ℂ (M.map (π x).toLinearMap))
  obtain ⟨ζ,hζ,hζN,hζx⟩ := no_compacts_large_vector π hno x hx hnorm N (1/2) (by norm_num)
  let η := (‖π x ζ‖:ℂ)⁻¹ • π x ζ
  have hy : 0 < ‖π x ζ‖ := lt_trans (by norm_num) hζx
  have hη : ‖η‖ = 1 := by
    simp only [η,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀ hy.ne']
  have hyM : π x ζ ∈ Mᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,
      hpxsa.star_eq]
    exact N.inner_right_of_mem_orthogonal (Submodule.mem_map.mpr ⟨v,hv,rfl⟩) hζN
  refine ⟨η,hη,Mᗮ.smul_mem _ hyM,fun a ha => ?_⟩
  have hb := compressed_vector_coefficient_bound π.toNonUnitalStarAlgHom (map_one π)
    x hxsa ζ hζ.le hy a (f a)
  change ‖⟪η,π a η⟫_ℂ-f a‖ ≤ _ at hb
  have hinv : ‖π x ζ‖⁻¹ ≤ 2 := by
    have hh : (1/2:ℝ)⁻¹ = 2 := by norm_num
    rw [← hh]
    exact (inv_le_inv₀ hy (show 0 < (1/2:ℝ) by norm_num)).mpr hζx.le
  calc
    _ ≤ ‖π x ζ‖⁻¹^2 * ‖x*(a-f a • (1:A))*x‖ := hb
    _ ≤ 4 * ‖x*(a-f a • (1:A))*x‖ := by
      gcongr
      nlinarith [inv_nonneg.mpr hy.le]
    _ < 4*(ε/4) := by gcongr; exact hsmall a ha
    _ = ε := by ring

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

theorem third_vector_two_frames
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (hi : Function.Injective π)
    (hno : ∀ a : A, IsCompactOperator (π a) → π a = 0)
    (x : ι → A) (ξ η : H) (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ ζ : H, ‖ζ‖ = 1 ∧
      (∀ i j, ⟪π (star (x i)) ξ,π (star (x j)) ζ⟫_ℂ = 0) ∧
      (∀ i j, ⟪π (star (x i)) η,π (star (x j)) ζ⟫_ℂ = 0) ∧
      ∀ a ∈ F, ‖⟪ζ,π a ζ⟫_ℂ - f a‖ < ε := by
  classical
  let Q₁ : Finset H := Finset.univ.image (fun ij : ι × ι => π (x ij.2*star (x ij.1)) ξ)
  let Q₂ : Finset H := Finset.univ.image (fun ij : ι × ι => π (x ij.2*star (x ij.1)) η)
  let M : Submodule ℂ H := Submodule.span ℂ ((Q₁ ∪ Q₂ : Finset H) : Set H)
  let : FiniteDimensional ℂ M := inferInstanceAs
    (FiniteDimensional ℂ (Submodule.span ℂ ((Q₁ ∪ Q₂ : Finset H) : Set H)))
  obtain ⟨ζ,hζ,hζM,htest⟩ := pure_vector_approximation_orthogonal
    (irreducibleUnitalRepresentation π hπ) hi hno f hf M F ε hε
  have horth (v : H) (hv : ∀ i j, π (x j*star (x i)) v ∈ M) :
      ∀ i j, ⟪π (star (x i)) v,π (star (x j)) ζ⟫_ℂ = 0 := by
    intro i j
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,
      ← map_star,star_star,← mul_apply_eq_comp,← map_mul]
    exact M.inner_right_of_mem_orthogonal (hv i j) hζM
  refine ⟨ζ,hζ,horth ξ ?_,horth η ?_,htest⟩
  · intro i j
    apply Submodule.subset_span
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)
  · intro i j
    apply Submodule.subset_span
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)

end KOS

open scoped InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Homogeneity
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Filter Topology
open scoped InnerProductSpace
namespace KOS

section

variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

theorem inner_fitting (hA : IsSimpleCStar A) (f g : A →L[ℂ] ℂ)
    (hf : IsPureState f) (hg : IsPureState g)
    (F : Finset A) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : unitary A,
      Close F ε (restrictState (Unitary.conjStarAlgAut ℂ A u).symm.toStarAlgHom f) g := by
  let P := positiveOfSquares f hf.1.2
  let π := P.gnsNonUnitalStarAlgHom
  let ξ := gnsVector P
  obtain ⟨u,hu⟩ := simple_pure_inner_orbit_finite hA π
    (pure_gns_irreducible f hf.1 hf) ξ
    (gnsVector_norm_eq_one P ((isState_iff f).mp hf.1).1) g hg F ε hε
  refine ⟨u,fun a ha => ?_⟩
  rw [dist_eq_norm]
  change ‖f (star (u:A)*a*(u:A)) - g a‖ < ε
  change ‖P (star (u:A)*a*(u:A)) - g a‖ < ε
  rw [← gnsVector_coefficient P]
  exact hu a ha

theorem localControl_of_sameClassControl (hA : IsSimpleCStar A)
    (h : SameClassControl (A := A)) : LocalControl (A := A) := by
  classical
  intro f hf F ε hε
  obtain ⟨G,δ,hδ,hG⟩ := h f hf F ε hε
  refine ⟨G,δ/3,by positivity,?_⟩
  intro g hg hfg K η hη
  obtain ⟨u,hu⟩ := inner_fitting hA f g hf hg (G ∪ K)
    (min η (δ/3)) (lt_min hη (by positivity))
  let e := (Unitary.conjStarAlgAut ℂ A u).symm
  let p := restrictState e.toStarAlgHom f
  have hp : IsPureState p := isPureState_restrict_equiv e f hf
  have heq : PureStateEquivalent f hf p hp :=
    pureState_equivalent_of_conjugate f p hf hp u (fun _ => rfl)
  have hfp : Close G δ f p := by
    intro a ha
    have h₁ := hfg a ha
    have h₂ := (hu a (Finset.mem_union_left K ha)).trans_le (min_le_right _ _)
    have ht := dist_triangle (f a) (g a) (p a)
    rw [dist_comm (g a) (p a)] at ht
    linarith
  obtain ⟨θ,hθ,hpθ⟩ := hG p hp heq hfp
  refine ⟨θ,hθ,?_⟩
  rw [hpθ]
  intro a ha
  exact (hu a (Finset.mem_union_right G ha)).trans_le (min_le_left _ _)

end

section
open Filter Topology
variable {A : Type*} [cStarAlgebraA : CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

def data (h : LocalControl (A := A)) (q : ℕ → A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (α : A ≃⋆ₐ[ℂ] A) (n : ℕ) :
    ControlData (restrictState α.toStarAlgHom f) (orbitTests q α n) ((1/2:ℝ)^n) :=
  Classical.choose (exists_controlData h _ (isPureState_restrict_equiv α f hf)
    (orbitTests q α n) ((1/2:ℝ)^n) (pow_pos (by norm_num) _) (tests q n)
    ((1/2:ℝ)^n) (pow_pos (by norm_num) _))

theorem data_tests (h : LocalControl (A := A)) (q : ℕ → A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (α : A ≃⋆ₐ[ℂ] A) (n : ℕ) :
    tests q n ⊆ (data h q f hf α n).tests :=
  (Classical.choose_spec (exists_controlData h _ (isPureState_restrict_equiv α f hf)
    (orbitTests q α n) ((1/2:ℝ)^n) (pow_pos (by norm_num) _) (tests q n)
    ((1/2:ℝ)^n) (pow_pos (by norm_num) _))).1

theorem data_radius (h : LocalControl (A := A)) (q : ℕ → A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (α : A ≃⋆ₐ[ℂ] A) (n : ℕ) :
    (data h q f hf α n).radius ≤ (1/2:ℝ)^n :=
  (Classical.choose_spec (exists_controlData h _ (isPureState_restrict_equiv α f hf)
    (orbitTests q α n) ((1/2:ℝ)^n) (pow_pos (by norm_num) _) (tests q n)
    ((1/2:ℝ)^n) (pow_pos (by norm_num) _))).2

variable (h : LocalControl (A := A)) (q : ℕ → A)
  (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)

structure Stage (n : ℕ) where
  left : A ≃⋆ₐ[ℂ] A
  right : A ≃⋆ₐ[ℂ] A
  close : Close (data h q f hf left n).tests (data h q f hf left n).radius
    (restrictState left.toStarAlgHom f) (restrictState right.toStarAlgHom g)

def Step {n : ℕ} (s : Stage h q f g hf n) (t : Stage h q f g hf (n+1)) : Prop :=
  ∀ k ≤ n,
    dist (s.left (q k)) (t.left (q k)) ≤ (1/2:ℝ)^n ∧
    dist (s.left.symm (q k)) (t.left.symm (q k)) ≤ (1/2:ℝ)^n ∧
    dist (s.right (q k)) (t.right (q k)) ≤ (1/2:ℝ)^n ∧
    dist (s.right.symm (q k)) (t.right.symm (q k)) ≤ (1/2:ℝ)^n

include hg in

theorem exists_next {n : ℕ} (s : Stage h q f g hf n) :
    ∃ t : Stage h q f g hf (n+1), Step h q f g hf s t := by
  let R := data h q g hg s.right n
  obtain ⟨θ,hθ,hmatch⟩ := (data h q f hf s.left n).correct _
    (isPureState_restrict_equiv s.right g hg) s.close R.tests R.radius R.positive
  let α := θ.trans s.left
  have hmatch' : Close R.tests R.radius
      (restrictState s.right.toStarAlgHom g) (restrictState α.toStarAlgHom f) := by
    simpa only [α,restrict_trans] using hmatch.symm
  let L := data h q f hf α (n+1)
  obtain ⟨ψ,hψ,hmatch₂⟩ := R.correct _ (isPureState_restrict_equiv α f hf)
    hmatch' L.tests L.radius L.positive
  let β := ψ.trans s.right
  have hnew : Close L.tests L.radius
      (restrictState α.toStarAlgHom f) (restrictState β.toStarAlgHom g) := by
    simpa only [β,restrict_trans] using hmatch₂.symm
  refine ⟨⟨α,β,hnew⟩,fun k hk => ?_⟩
  have h₁ := step_control q s.left θ n _ hθ hk
  have h₂ := step_control q s.right ψ n _ hψ hk
  exact ⟨h₁.1.le,h₁.2.le,h₂.1.le,h₂.2.le⟩

include hg in

theorem exists_initial (hA : IsSimpleCStar A) : Nonempty (Stage h q f g hf 0) := by
  let α : A ≃⋆ₐ[ℂ] A := StarAlgEquiv.refl ℂ A
  let L := data h q f hf α 0
  obtain ⟨u,hu⟩ := inner_fitting hA g (restrictState α.toStarAlgHom f) hg
    (isPureState_restrict_equiv α f hf) L.tests L.radius L.positive
  exact ⟨⟨α,(Unitary.conjStarAlgAut ℂ A u).symm,hu.symm⟩⟩

end

section
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_controlled_pair (h : LocalControl (A := A)) (hA : IsSimpleCStar A)
    (q : ℕ → A) (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ α β : ℕ → A ≃⋆ₐ[ℂ] A, ∀ n k, k ≤ n →
      dist (α n (q k)) (α (n+1) (q k)) ≤ (1/2:ℝ)^n ∧
      dist ((α n).symm (q k)) ((α (n+1)).symm (q k)) ≤ (1/2:ℝ)^n ∧
      dist (β n (q k)) (β (n+1) (q k)) ≤ (1/2:ℝ)^n ∧
      dist ((β n).symm (q k)) ((β (n+1)).symm (q k)) ≤ (1/2:ℝ)^n ∧
      dist (f (α n (q k))) (g (β n (q k))) ≤ (1/2:ℝ)^n := by
  let s₀ := Classical.choice (exists_initial h q f g hf hg hA)
  let next := fun (n : ℕ) (s : Stage h q f g hf n) =>
    Classical.choose (exists_next h q f g hf hg s)
  let s : (n : ℕ) → Stage h q f g hf n := fun n => Nat.rec s₀ next n
  refine ⟨fun n => (s n).left,fun n => (s n).right,fun n k hk => ?_⟩
  have hstep : Step h q f g hf (s n) (s (n+1)) :=
    Classical.choose_spec (exists_next h q f g hf hg (s n))
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hstep k hk
  refine ⟨h₁,h₂,h₃,h₄,?_⟩
  exact ((s n).close _ (data_tests h q f hf _ n (mem_tests q hk))).le.trans
    (data_radius h q f hf _ n)

theorem cauchy_of_geometric_tests (q : ℕ → A) (hq : DenseRange q)
    (α : ℕ → A ≃⋆ₐ[ℂ] A)
    (h : ∀ n k, k ≤ n → dist (α n (q k)) (α (n+1) (q k)) ≤ (1/2:ℝ)^n)
    (a : A) : CauchySeq (fun n => α n a) := by
  apply isometry_cauchy_on_dense (fun n a => α n a)
    (fun n => StarAlgEquiv.isometry (α n)) (Set.range q) hq _ a
  rintro b ⟨k,rfl⟩
  exact cauchySeq_of_tail_geometric_steps _ k (fun n hn => h n k hn)

theorem homogeneity_of_localControl [TopologicalSpace.SeparableSpace A]
    (h : LocalControl (A := A)) (hA : IsSimpleCStar A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a := by
  obtain ⟨q,hq⟩ := TopologicalSpace.exists_dense_seq A
  obtain ⟨α,β,H⟩ := exists_controlled_pair h hA q f g hf hg
  have hα := cauchy_of_geometric_tests q hq α (fun n k hk => (H n k hk).1)
  have hαi := cauchy_of_geometric_tests q hq (fun n => (α n).symm)
    (fun n k hk => (H n k hk).2.1)
  have hβ := cauchy_of_geometric_tests q hq β (fun n k hk => (H n k hk).2.2.1)
  have hβi := cauchy_of_geometric_tests q hq (fun n => (β n).symm)
    (fun n k hk => (H n k hk).2.2.2.1)
  let alphaLimit := autLimitEquiv α hα hαi
  let betaLimit := autLimitEquiv β hβ hβi
  have hvalues (k : ℕ) : f (alphaLimit (q k)) = g (betaLimit (q k)) := by
    have hz : Tendsto (fun n => dist (f (α n (q k))) (g (β n (q k))))
        atTop (𝓝 0) := by
      exact squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg))
        (eventually_atTop.mpr ⟨k,fun n hn => (H n k hn).2.2.2.2⟩)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have h₁ : Tendsto (fun n => f (α n (q k))) atTop (𝓝 (f (alphaLimit (q k)))) :=
      f.continuous.tendsto _ |>.comp (tendsto_autPointwiseLimit α hα (q k))
    have h₂ : Tendsto (fun n => g (β n (q k))) atTop (𝓝 (g (betaLimit (q k)))) :=
      g.continuous.tendsto _ |>.comp (tendsto_autPointwiseLimit β hβ (q k))
    exact dist_eq_zero.mp (tendsto_nhds_unique (h₁.dist h₂) hz)
  have he : (fun a => f (alphaLimit a)) = fun a => g (betaLimit a) := by
    apply hq.equalizer (f.continuous.comp (StarAlgEquiv.isometry alphaLimit).continuous)
      (g.continuous.comp (StarAlgEquiv.isometry betaLimit).continuous)
    funext k
    exact hvalues k
  refine ⟨betaLimit.symm.trans alphaLimit,fun a => ?_⟩
  have hh := congrFun he (betaLimit.symm a)
  simpa only [StarAlgEquiv.trans_apply,betaLimit.apply_symm_apply] using hh

theorem homogeneity_of_sameClassControl [TopologicalSpace.SeparableSpace A]
    (h : SameClassControl (A := A)) (hA : IsSimpleCStar A)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    ∃ γ : A ≃⋆ₐ[ℂ] A, ∀ a, f (γ a) = g a :=
  homogeneity_of_localControl (localControl_of_sameClassControl hA h) hA f g hf hg

end

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra ComplexOrder
namespace TracialStage

variable (X : TracialStage)
  {B : Type}
  [CStarAlgebra B]
  [partialOrderB : PartialOrder B]
  [starOrderedRingB : StarOrderedRing B]
  [topologicalSpaceSeparableSpaceB : TopologicalSpace.SeparableSpace B]
  (hB : IsSimpleCStar B)
  (ψ : CAR →⋆ₐ[ℂ] B)
  (φ : B →⋆ₐ[ℂ] X)
  (hφ : Function.Injective φ)
  (hbase : ∀ a, φ (ψ a) = X.base a)
  (hU : PureUEP φ)
  (f : X →L[ℂ] ℂ)
  (hf : IsPureState f)
  (hfr : IsPureState (restrictState φ f))

include hbase in
omit partialOrderB starOrderedRingB topologicalSpaceSeparableSpaceB in
lemma core_car_injective [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] : Function.Injective ψ := by
  intro a b h
  apply X.base_injective
  rw [← hbase a,← hbase b,h]

include hbase in
lemma core_infinite : ¬ FiniteDimensional ℂ B := by
  intro h
  exact carInfiniteDimensional (Module.Finite.of_injective ψ.toLinearMap
    (core_car_injective X ψ φ hbase))

include hbase in
omit partialOrderB starOrderedRingB topologicalSpaceSeparableSpaceB in
lemma core_reference_peaks [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B] : Peaks (fun n => φ (ψ (carPeak n))) X.reference := by
  simpa only [hbase] using X.reference_peaks

end TracialStage

open Topology

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

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
section
universe u v
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma subalgebraSubtype_pureUEP_of_top
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    (hST : S ≤ T) (hT : T = ⊤) (h : PureUEP (StarSubalgebra.inclusion hST)) :
    PureUEP S.subtype := by
  let e : T ≃⋆ₐ[ℂ] A := StarAlgEquiv.ofBijective T.subtype
    ⟨Subtype.val_injective,fun a => ⟨⟨a,by rw [hT]; trivial⟩,rfl⟩⟩
  have he : e.toStarAlgHom.comp (StarSubalgebra.inclusion hST) = S.subtype := by ext a; rfl
  rw [← he]
  exact h.postcomp_equiv e

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

theorem nearCentralRows : NearCentralRows (A:=A) := by
  classical
  intro f hf F c hc
  let B : ℝ := ∑ z ∈ F, ‖z‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let t : ℝ := min (1/48) (c/(1+1152*B))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hc (by positivity))
  have ht48 : t ≤ 1/48 := min_le_left _ _
  have htc : t*(1+1152*B) ≤ c :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let π := pureGNS f hf
  let ξ := gnsVector (positiveOfSquares f hf.1.2)
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one _ ((isState_iff f).mp hf.1).1
  obtain ⟨n,x,hx,hfix,hcentral⟩ := approximate_matrix_rows π (pure_gns_irreducible f hf.1 hf) ξ hξ F t ht
  obtain ⟨b,hb,hbfix⟩ := irreducible_near_congruence π
    (pure_gns_irreducible f hf.1 hf) (rowAverage x 1)
    (rowAverage_selfAdjoint x 1 (IsSelfAdjoint.one A)) ξ hξ t hfix (by linarith)
  refine ⟨n,fun i => b*x i,?_,?_⟩
  · simpa only [rowAverage_congruence] using hbfix
  · intro z hz a ha ha1
    rw [rowAverage_congruence]
    have hay : ‖rowAverage x a‖ ≤ 4 := by
      have han : ‖a‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg a ha).mpr ha1
      exact (hx a).trans (by linarith)
    have hzB : ‖z‖ ≤ B := Finset.single_le_sum (fun z _ => norm_nonneg z) hz
    exact (commutator_congruence_norm_four z b (rowAverage x a) (48*t) t hb
      (by linarith) hay (hcentral z hz a ha ha1)).trans (by
        nlinarith [mul_le_mul_of_nonneg_right hzB ht.le])

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

lemma base_isClosed : IsClosed (Set.range X.base) :=
  (NonUnitalStarAlgHom.isometry X.base X.base_injective).isClosedEmbedding.isClosed_range

lemma generatedFamily_zero (z : Ordinal.{0} → X) :
    generatedFamily (Set.range X.base) z (Set.Iio 0) = X.base.range := by
  rw [generatedFamily,show Set.Iio (0:Ordinal.{0}) = ∅ by ext k; simp,
    Set.image_empty,Set.union_empty]
  change (StarAlgebra.adjoin ℂ (X.base.range : Set X)).topologicalClosure = _
  rw [StarAlgebra.adjoin_eq]
  apply SetLike.coe_injective
  exact X.base_isClosed.closure_eq

lemma base_simple (z : Ordinal.{0} → X) :
    IsSimpleCStar (generatedFamily (Set.range X.base) z (Set.Iio 0)) := by
  let e : CAR ≃⋆ₐ[ℂ] generatedFamily (Set.range X.base) z (Set.Iio 0) :=
    StarAlgEquiv.ofBijective (X.base.codRestrict _ (fun a =>
      generatedFamily_contains_base (Set.range X.base) z (Set.Iio 0) ⟨a,rfl⟩))
      ⟨fun a b h => X.base_injective (congrArg Subtype.val h),by
        rintro ⟨a,ha⟩
        rw [X.generatedFamily_zero] at ha
        obtain ⟨b,hb⟩ := ha
        exact ⟨b,Subtype.ext hb⟩⟩
  exact carSimple.of_equiv e

lemma base_separable : TopologicalSpace.IsSeparable (Set.range X.base) :=
  TopologicalSpace.isSeparable_range
    (NonUnitalStarAlgHom.isometry X.base X.base_injective).continuous
end TracialStage

end

section
open CategoryTheory
attribute [local instance] generatedFamily_isClosed

namespace ChronologicalStage

namespace Hom
variable {X Y Z : ChronologicalStage}

def id (X : ChronologicalStage) : Hom X X where
  embedding := TracialStage.Hom.id X.stage
  height_le := le_rfl
  generator _ _ := rfl
  active _ _ := Iff.rfl
  dependency _ _ := rfl
  peak _ _ _ _ := rfl

end Hom

instance instCategory : Category ChronologicalStage where
  Hom := Hom
  id := Hom.id
  comp f g := g.comp f
  id_comp f := by ext a; rfl
  comp_id f := by ext a; rfl
  assoc f g h := by ext a; rfl

end ChronologicalStage
end

namespace PeakingPairData
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A S T R U : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra S] [PartialOrder S] [StarOrderedRing S]
  [CStarAlgebra T] [partialOrderT : PartialOrder T] [starOrderedRingT : StarOrderedRing T]
  [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]
  [CStarAlgebra U] [PartialOrder U] [StarOrderedRing U]

omit partialOrderT starOrderedRingT in
lemma hnnAmbient_of_data [PartialOrder T] [StarOrderedRing T] (G : PeakingPairData A)
    (b : S →⋆ₐ[ℂ] A) (t : T →⋆ₐ[ℂ] A) (z : Bool → A)
    (D : PeakingPairData S)
    (hp : ∀ i n, b (D.peak i n) = G.peak i n)
    (ht : ∀ a, D.trace a = G.trace (b a))
    (e : D.HNNAlgebra ≃⋆ₐ[ℂ] T)
    (heb : ∀ a, t (e (D.hnnBase a)) = b a)
    (hew : ∀ i, t (e (D.hnnLetter i)) = z i)
    (het : ∀ a, G.trace (t (e a)) = D.hnnTrace a) :
    G.HNNAmbientPresentation b t z :=
  ⟨D,hp,ht,e,heb,hew,het⟩

variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma exists_reparam_pair (D : PeakingPairData S) (e : S ≃⋆ₐ[ℂ] R) :
    ∃ D' : PeakingPairData R,
      (∀ i n, e.symm (D'.peak i n) = D.peak i n) ∧
      (∀ a, D.trace (e.symm a) = D'.trace a) := by
  exact ⟨D.pullback e.symm.toStarAlgHom e.symm.injective
    (fun i n => e (D.peak i n)) (fun _ _ => e.symm_apply_apply _),
    (fun _ _ => e.symm_apply_apply _),fun _ => rfl⟩

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

include hp in
lemma states_restrict_of_peaks (i : Bool) : restrictState φ (Q.state i) = P.state i := by
  apply (P.peaks i).2.2.2.2 _ (isState_restrict φ _ (Q.peaks i).2.2.1)
  intro n
  change Q.state i (φ (P.peak i n)) = 1
  rw [hp]
  exact (Q.peaks i).2.2.2.1 n

end PeakingPairData
end

open Topology
section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

namespace TracialStage.Hom
variable {X Y : TracialStage} (φ : TracialStage.Hom X Y)

lemma image_base : φ.map '' Set.range X.base = Set.range Y.base := by
  rw [← Set.range_comp]
  congr 1
  funext a
  exact φ.base_map a

lemma generatedFamily_map (z : Ordinal.{0} → X) (S : Set Ordinal.{0}) :
    (generatedFamily (Set.range X.base) z S).map φ.map =
      generatedFamily (Set.range Y.base) (φ.map ∘ z) S := by
  rw [NaimarkZFC.generatedFamily_map _ _ _ φ.map φ.injective,φ.image_base]

lemma mapped_mem (z : Ordinal.{0} → X) (S : Set Ordinal.{0})
    {a : X} (ha : a ∈ generatedFamily (Set.range X.base) z S) :
    φ.map a ∈ generatedFamily (Set.range Y.base) (φ.map ∘ z) S := by
  rw [← φ.generatedFamily_map]
  exact ⟨a,ha,rfl⟩
end TracialStage.Hom

end

open Topology
section
attribute [local instance] generatedFamily_isClosed
namespace ChronologicalData
variable {X Y : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalData X δ)
  (φ : TracialStage.Hom X Y)

attribute [local instance] OAI.NaimarkZFC.instDecidableEqOrdinal_solutions
lemma image_generated_range :
    generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio δ) = φ.map.range := by
  rw [← φ.generatedFamily_map,D.generated]
  ext a
  constructor
  · rintro ⟨x,_,rfl⟩; exact ⟨x,rfl⟩
  · rintro ⟨x,rfl⟩; exact ⟨x,trivial,rfl⟩

lemma image_mem (a : X) :
    φ.map a ∈ generatedFamily (Set.range Y.base) (φ.map ∘ D.generator) (Set.Iio δ) := by
  rw [D.image_generated_range φ]
  exact ⟨a,rfl⟩

lemma updated_generated (z : Y)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range φ.map ∪ Set.range (starPair z)) : Set Y)) :
    generatedFamily (Set.range Y.base) (Function.update (φ.map ∘ D.generator) δ z)
      (Set.Iio (δ+1)) = ⊤ := by
  let T := generatedFamily (Set.range Y.base)
    (Function.update (φ.map ∘ D.generator) δ z) (Set.Iio (δ+1))
  have hz : z ∈ T := by
    have h := generatedFamily_contains (Set.range Y.base)
      (Function.update (φ.map ∘ D.generator) δ z) (show δ ∈ Set.Iio (δ+1) from lt_add_one δ)
    simpa only [Function.update_self] using h
  have hr : Set.range φ.map ⊆ (T : Set Y) := by
    rintro _ ⟨a,rfl⟩
    have h := D.image_mem φ a
    apply (StarSubalgebra.topologicalClosure_mono ?_) h
    apply StarAlgebra.adjoin_mono
    apply Set.union_subset_union Set.Subset.rfl
    rintro _ ⟨k,hk,rfl⟩
    exact ⟨k,(show k < δ+1 from hk.trans (lt_add_one δ)),Function.update_of_ne hk.ne _ _⟩
  have hg : StarAlgebra.adjoin ℂ (Set.range φ.map ∪ Set.range (starPair z)) ≤ T := by
    apply StarAlgebra.adjoin_le
    rintro a (ha|⟨b,rfl⟩)
    · exact hr ha
    · cases b
      · exact hz
      · exact star_mem hz
  apply top_unique
  intro a _
  exact (show IsClosed (T : Set Y) from inferInstance).closure_subset_iff.mpr hg (hd a)

end ChronologicalData
end

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

include hS hsupport in
lemma inserted_peak_mem (i : Bool) (n : ℕ) :
    Q.peak i n ∈ generatedFamily (Set.range X.base) D.generator (Set.Iio δ) :=
  generatedFamily_mono _ _ hS (hsupport i n)

end ChronologicalHistory
end

section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

@[simp] lemma fullImageEquiv_apply (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (S : StarSubalgebra ℂ B) (hS : S = φ.range) (a : A) :
    (fullImageEquiv φ hφ S hS a : B) = φ a := rfl

@[simp] lemma fullTopEquiv_apply (T : StarSubalgebra ℂ B) (hT : T = ⊤) (b : B) :
    (fullTopEquiv T hT b : B) = b := rfl

end

open Topology
namespace PeakingPairData
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
attribute [local irreducible] HNNAlgebra hnnCStar hnnOrder
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma hnnLetter_starPair (Q : PeakingPairData A) :
    Q.hnnLetter = starPair (Q.hnnLetter false) := by
  funext i
  cases i
  · rfl
  · exact (Q.hnnLetter_star false).symm

end PeakingPairData

open Topology

section
attribute [local instance] generatedFamily_isClosed
namespace ChronologicalStage
variable (X : ChronologicalStage)
def inactiveSuccessor : ChronologicalStage :=
  ⟨X.stage,X.height+1,X.history.advanceInactive⟩

end ChronologicalStage
end

section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

namespace ChronologicalStage
variable (X : ChronologicalStage)

def coreBase (S : Set Ordinal.{0}) : CAR →⋆ₐ[ℂ] X.history.algebra S :=
  X.stage.base.codRestrict _ (fun a => generatedFamily_contains_base _ _ _ ⟨a,rfl⟩)

end ChronologicalStage
end

open CategoryTheory
namespace TracialStage

variable {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
  (D : J ⥤ TracialStage)

def bond (i j : J) (h : i ≤ j) : D.obj i →⋆ₐ[ℂ] D.obj j :=
  (D.map (homOfLE h)).map

instance bond_directed : DirectedSystem (fun i => D.obj i) (bond D · · ·) where
  map_self i a := by
    change (D.map (𝟙 i)).map a = a
    rw [D.map_id]
    rfl
  map_map k j i hij hjk a := by
    change (D.map (homOfLE hjk)).map ((D.map (homOfLE hij)).map a) =
      (D.map (homOfLE (hij.trans hjk))).map a
    have h := D.map_comp (homOfLE hij) (homOfLE hjk)
    exact congrArg (fun f : Hom (D.obj i) (D.obj k) => f.map a) h.symm

instance bond_isometric : IsometricStarSystem (fun i => D.obj i) (bond D) where
  isometry _ _ h := NonUnitalStarAlgHom.isometry (D.map (homOfLE h)).map.toNonUnitalStarAlgHom
    (D.map (homOfLE h)).injective

abbrev LimitCarrier := CStarDirectLimit (fun i => D.obj i) (bond D)

def limitIncl (i : J) : D.obj i →⋆ₐ[ℂ] LimitCarrier D :=
  cstarDirectLimitInclude (fun i => D.obj i) (bond D) i

lemma limitIncl_injective (i : J) : Function.Injective (limitIncl D i) :=
  (cstarDirectLimitInclude_isometry (fun i => D.obj i) (bond D) i).injective

@[simp] lemma limitIncl_compatible (i j : J) (h : i ≤ j) (a : D.obj i) :
    limitIncl D j ((D.map (homOfLE h)).map a) = limitIncl D i a :=
  cstarDirectLimitInclude_compatible (fun i => D.obj i) (bond D) i j h a

lemma limitIncl_base_eq (i j : J) (a : CAR) :
    limitIncl D i ((D.obj i).base a) = limitIncl D j ((D.obj j).base a) := by
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  rw [← limitIncl_compatible D i k hik,← limitIncl_compatible D j k hjk]
  rw [(D.map (homOfLE hik)).base_map,(D.map (homOfLE hjk)).base_map]

def limitTrace : LimitCarrier D →L[ℂ] ℂ :=
  cstarDirectLimitState (fun i => D.obj i) (bond D) (fun i => (D.obj i).trace)
    (fun i => (D.obj i).traceState) (fun _ _ h a => (D.map (homOfLE h)).trace_map a)

lemma limitTrace_state : IsState (limitTrace D) :=
  cstarDirectLimitState_isState _ _ _ _ _

lemma limitTrace_tracial (a b : LimitCarrier D) :
    limitTrace D (a*b) = limitTrace D (b*a) :=
  cstarDirectLimitState_tracial _ _ _ _ _ (fun i => (D.obj i).tracial) a b

@[simp] lemma limitTrace_stage (i : J) (a : D.obj i) :
    limitTrace D (limitIncl D i a) = (D.obj i).trace a :=
  cstarDirectLimitState_stage (fun i => D.obj i) (bond D)
    (fun i => (D.obj i).trace) (fun i => (D.obj i).traceState)
    (fun _ _ h a => (D.map (homOfLE h)).trace_map a) i a

lemma limitIncl_uep (i : J) : PureUEP (limitIncl D i) :=
  cstarDirectLimit_pureUEP (fun i => D.obj i) (bond D) (fun _ _ h => (D.map (homOfLE h)).uep) i

def directLimit : TracialStage where
  carrier := LimitCarrier D
  cstar := inferInstance
  order := CStarAlgebra.spectralOrder _
  starOrder := CStarAlgebra.spectralOrderedRing _
  simple := cstarDirectLimit_simple _ _ (fun i => (D.obj i).simple)
  trace := limitTrace D
  traceState := limitTrace_state D
  tracial := limitTrace_tracial D
  base := (limitIncl D (Classical.arbitrary J)).comp (D.obj (Classical.arbitrary J)).base
  base_injective := (limitIncl_injective D _).comp (D.obj _).base_injective
  baseUEP := (D.obj _).baseUEP.comp (limitIncl_uep D _)

def directLimitHom (i : J) : Hom (D.obj i) (directLimit D) where
  map := limitIncl D i
  injective := limitIncl_injective D i
  trace_map := limitTrace_stage D i
  base_map a := limitIncl_base_eq D i (Classical.arbitrary J) a
  uep := limitIncl_uep D i

@[simp] lemma directLimitHom_compatible (i j : J) (h : i ≤ j) :
    Hom.comp (directLimitHom D j) (D.map (homOfLE h)) = directLimitHom D i := by
  ext a
  exact limitIncl_compatible D i j h a

end TracialStage

open CategoryTheory

open CategoryTheory Topology

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable {J : Type} [LinearOrder J] (S : Set J)
  (F : ∀ j : S, Set.Iic (j : J) ⥤ ChronologicalStage)
  (hF : ∀ (i j : S) (h : i ≤ j), restrictionLE (F j) h = F i)

include hF in
lemma prefix_congr_obj (i j : S) (k : J) (hi : k ≤ i) (hj : k ≤ j) :
    (F i).obj ⟨k,hi⟩ = (F j).obj ⟨k,hj⟩ := by
  rcases le_total i j with hij | hji
  · have hh := Functor.congr_obj (hF i j hij) ⟨k,hi⟩
    exact hh.symm
  · exact (Functor.congr_obj (hF j i hji) ⟨k,hj⟩)

def prefixMap (i j : S) (h : i ≤ j) :
    (F i).obj ⟨i,le_rfl⟩ ⟶ (F j).obj ⟨j,le_rfl⟩ :=
  eqToHom (prefix_congr_obj S F hF i j i le_rfl h) ≫ (F j).map (homOfLE h)

@[simp] lemma prefixMap_refl (i : S) : prefixMap S F hF i i le_rfl = 𝟙 _ := by
  simp [prefixMap]

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable (J : Type) [LinearOrder J]

variable [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]

abbrev SuccessorRule := ∀ (j : J) (_ : ¬ IsMax j) (D : Set.Iic j ⥤ ChronologicalStage),
  Σ X : ChronologicalStage, (D.obj ⟨j,le_rfl⟩ ⟶ X)

end ChronologicalStage

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


