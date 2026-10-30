-- Prove2me | Definitions.Def_OAIQ115N029
-- name    : OAIQ115N029
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:43:22.368861+00:00
-- url     : https://prove2.me/theorems/86e35398-32a4-44a6-9bae-19e957c4a537
-- title:
--   Definitions bundle OAIQ115N029 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 3 definitions and 11 theorems. The definitions and types are `OAI.NaimarkZFC.PeakingPairData.hnnLetter`, `OAI.NaimarkZFC.PeakingPairData.modelTrace`, `OAI.NaimarkZFC.PeakingPairData.turnCenterCLM`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundle `OAIQ115N017` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N021` and `OAIQ115N022`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N017

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
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

theorem matrixCornerExpectation_one (hfix : ∀ a, E (φ a) = a) :
    matrixCornerExpectation φ E 1 = 1 := by
  rw [← map_one (matrixCornerBase φ)]
  exact matrixCornerExpectation_base φ E hfix 1

theorem matrixCornerExpectation_norm (hbound : ∀ x, ‖E x‖ ≤ ‖x‖) (x : MatrixHNNCorner φ) :
    ‖matrixCornerExpectation φ E x‖ ≤ ‖x‖ :=
  (CStarMatrix.norm_entry_le_norm (M := E (x:C)) (i := false) (j := false)).trans (hbound x)

theorem matrixCornerExpectation_star (hstar : ∀ x, E (star x) = star (E x))
    (x : MatrixHNNCorner φ) :
    matrixCornerExpectation φ E (star x) = star (matrixCornerExpectation φ E x) := by
  change (E (star (x:C))) false false = star (E (x:C) false false)
  rw [hstar]
  rfl

theorem matrixCornerExpectation_state (hfix : ∀ a, E (φ a) = a)
    (hbound : ∀ x, ‖E x‖ ≤ ‖x‖) (hstar : ∀ x, E (star x) = star (E x))
    (f : A →L[ℂ] ℂ) (hf : IsState f) :
    IsState (f.comp (matrixCornerExpectation φ E)) := by
  apply isState_of_unital_contractive_hermitian
  · change f (matrixCornerExpectation φ E 1) = 1
    rw [matrixCornerExpectation_one φ E hfix,((isState_iff f).mp hf).1]
  · intro a
    exact (state_norm_apply_le f hf _).trans (matrixCornerExpectation_norm φ E hbound a)
  · intro a
    change f (matrixCornerExpectation φ E (star a)) = star (f (matrixCornerExpectation φ E a))
    rw [matrixCornerExpectation_star φ E hstar,state_map_star f hf]

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem expectCorner_state (f : A →L[ℂ] ℂ) (hf : IsState f) :
    IsState (f.comp B.expectCorner) :=
  matrixCornerExpectation_state B.embedBase B.modelExpectation
    (atomicExpectation_factor B.atoms B.amalgam false)
    (atomicExpectation_norm_le B.atoms B.amalgam false)
    (atomicExpectation_star B.atoms B.amalgam false) f hf

end PeakingPairData

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

abbrev modelTrace : B.Model →L[ℂ] ℂ := atomicTrace B.atoms B.amalgam

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

def hnnLetter : Bool → B.HNNAlgebra := B.cornerLetter

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
attribute [local instance 2000] hnnCStar 
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

theorem hnn_unique (hs : B.Separated) (hA : IsSimpleCStar A)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) : StateExtensionUnique B.hnnBase f :=
  B.corner_unique hs hA f hf

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem simple_extension_of_uep_expectation (hA : IsSimpleCStar A)
    (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ) (E : C →L[ℂ] A)
    (hfix : ∀ a, E (φ a) = a)
    (hpos : ∀ c, 0 ≤ c → 0 ≤ E c)
    (hfaith : ∀ c, E (star c*c) = 0 → c = 0)
    (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp E))
    (hu : ∀ f : A →L[ℂ] ℂ, IsPureState f → StateExtensionUnique φ f) :
    IsSimpleCStar C := by
  let : Nontrivial A := hA.1
  let : Nontrivial C := Function.Injective.nontrivial hφ
  refine ⟨inferInstance,fun J hc => ?_⟩
  by_cases hJ : J = ⊤
  · exact Or.inr hJ
  left
  obtain ⟨f,hf,hkill⟩ := exists_state_killing_ideal J hc hJ
  let F : C →ₚ[ℂ] ℂ := positiveOfSquares f hf.2
  let π := F.gnsStarAlgHom
  have hn : ‖gnsVector F‖ = 1 := gnsVector_norm_eq_one F ((isState_iff f).mp hf).1
  have hπ : (π.comp φ).toNonUnitalStarAlgHom ≠ 0 := by
    intro hz
    have hh := congrArg (fun ψ : A →⋆ₙₐ[ℂ] (F.GNS →L[ℂ] F.GNS) =>
      ψ 1 (gnsVector F)) hz
    have hh' : gnsVector F = 0 := by
      change π (φ 1) (gnsVector F) = 0 at hh
      simpa only [map_one,one_apply_eq_self] using hh
    rw [hh',norm_zero] at hn
    exact zero_ne_one hn
  have hinj : Function.Injective (π.comp φ) :=
    simple_nonzeroStarHom_injective hA (π.comp φ).toNonUnitalStarAlgHom hπ
  have hπJ : ∀ a ∈ J, π a = 0 := gns_kills_ideal F J hkill
  have hEJ : ∀ a ∈ J, E (star a*a) = 0 := by
    intro a ha
    apply positive_eq_zero_of_pure_states _ (hpos _ (star_mul_self_nonneg a))
    intro g hg
    obtain ⟨G,hG,hGr⟩ := exists_state_extension_of_injective (π.comp φ) hinj g hg.1
    let k := restrictState π G
    have hk : IsState k := isState_restrict π G hG
    have hkr : restrictState φ k = g := hGr
    have hEr : restrictState φ (g.comp E) = g := by
      ext b
      exact congrArg g (hfix b)
    have he : g.comp E = k := hu g hg _ _ (hstate g hg.1) hk hEr hkr
    have hh := congrArg (fun z : C →L[ℂ] ℂ => z (star a*a)) he
    change g (E (star a*a)) = G (π (star a*a)) at hh
    rw [map_mul π,hπJ a ha,mul_zero,map_zero] at hh
    exact hh
  apply le_antisymm _ bot_le
  intro a ha
  have hz := hfaith a (hEJ a ha)
  rw [hz]
  exact TwoSidedIdeal.zero_mem _

end

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem simple_extension_of_uep_square_expectation (hA : IsSimpleCStar A)
    (φ : A →⋆ₐ[ℂ] C) (hφ : Function.Injective φ) (E : C →L[ℂ] A)
    (hfix : ∀ a, E (φ a) = a)
    (hpos : ∀ c, 0 ≤ E (star c*c))
    (hfaith : ∀ c, E (star c*c) = 0 → c = 0)
    (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp E))
    (hu : ∀ f : A →L[ℂ] ℂ, IsPureState f → StateExtensionUnique φ f) :
    IsSimpleCStar C := by
  apply simple_extension_of_uep_expectation hA φ hφ E hfix ?_ hfaith hstate hu
  intro c hc
  obtain ⟨x,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hc
  exact hpos x
end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem corner_simple (hs : B.Separated) (hA : IsSimpleCStar A) : IsSimpleCStar B.Corner :=
  simple_extension_of_uep_square_expectation hA B.cornerBase B.cornerBase_injective B.expectCorner
    B.expectCorner_base B.expectCorner_square_nonneg B.expectCorner_faithful B.expectCorner_state
    (B.corner_unique hs hA)

end PeakingPairData

open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem hnn_simple (hs : B.Separated) (hA : IsSimpleCStar A) : IsSimpleCStar B.HNNAlgebra :=
  B.corner_simple hs hA

end PeakingPairData
end

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

omit [PartialOrder A] [StarOrderedRing A] in
include hp in
theorem pulled_peaks (i : Bool) : Peaks (fun n => φ (p i n)) (D.state i) := by
  simpa only [hp] using D.peaks i

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

def turnCenterCLM (i : Bool) : A →L[ℂ] A :=
  ContinuousLinearMap.id ℂ A - (starAlgHomCLM (B.diagonal (!i))).comp
    ((B.input false).expectation (!i))

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


