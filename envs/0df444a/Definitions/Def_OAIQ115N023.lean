-- Prove2me | Definitions.Def_OAIQ115N023
-- name    : OAIQ115N023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:44:29.249672+00:00
-- url     : https://prove2.me/theorems/c946b4fa-1b19-4e86-b63a-648c398e3006
-- title:
--   Definitions bundle OAIQ115N023 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 55 declarations of OpenAI's Lean: 5 definitions, 1 inductive type or structure, 1 instance and 48 theorems. The definitions and types are `OAI.NaimarkZFC.KOS.ControlData`, `OAI.NaimarkZFC.KOS.LocalControl`, `OAI.NaimarkZFC.KOS.NearCentralRows`, `OAI.NaimarkZFC.KOS.SameClassControl`, `OAI.NaimarkZFC.TracialStage.reference`, `OAI.NaimarkZFC.hnnBaseTailSpan`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean), [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Homogeneity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Homogeneity.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N017`, `OAIQ115N018`, `OAIQ115N019` and `OAIQ115N020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N025`, `OAIQ115N026` and `OAIQ115N027`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N017
import Definitions.Def_OAIQ115N018
import Definitions.Def_OAIQ115N019
import Definitions.Def_OAIQ115N020

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

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (e : A) (he : IsStarProjection e)

theorem cornerLiftState_isPureState (g : CStarCorner e he →L[ℂ] ℂ) (hg : IsPureState g) :
    IsPureState (cornerLiftState e he g) := by
  rw [IsPureState,mem_extremePoints]
  refine ⟨cornerLiftState_isState e he g hg.1,?_⟩
  intro f hf h hh hseg
  obtain ⟨a,b,ha,hb,hab,heq⟩ := hseg
  have hcomp : cornerCompression e he e = 1 := by
    apply Subtype.ext
    change e*e*e=e
    rw [he.isIdempotentElem.eq,he.isIdempotentElem.eq]
  have hface := state_projection_face f h hf hh e he a b ha hb hab (by
    rw [heq]
    change g (cornerCompression e he e) = 1
    rw [hcomp,((isState_iff g).mp hg.1).1])
  have heqr : a • cornerRestrictState e he f + b • cornerRestrictState e he h = g := by
    ext x
    have hh := congrArg (fun k : A →L[ℂ] ℂ => k (x:A)) heq
    simpa only [map_add,smul_apply, add_apply,cornerRestrictState_apply,
      cornerLiftState_apply,cornerCompression_corner] using hh
  have hbase := (mem_extremePoints.mp hg).2 _
    (cornerRestrictState_isState e he f hf hface.1) _
    (cornerRestrictState_isState e he h hh hface.2) ⟨a,b,ha,hb,hab,heqr⟩
  constructor
  · rw [← cornerLift_restrict e he f hf hface.1,hbase.1]
  · rw [← cornerLift_restrict e he h hh hface.2,hbase.2]

end

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
section
variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

variable [PartialOrder A] [StarOrderedRing A]

theorem cornerLift_equivalence (f g : CStarCorner e he →L[ℂ] ℂ)
    (hf : IsPureState f) (hg : IsPureState g)
    (hu : UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg)) :
    UnitarilyEquivalent
      (pureGNS (cornerLiftState e he f) (cornerLiftState_isPureState e he f hf))
      (pureGNS (cornerLiftState e he g) (cornerLiftState_isPureState e he g hg)) := by
  obtain ⟨u,hu⟩ := pureState_equivalent_conjugate f g hf hg hu
  apply pureState_equivalent_of_conjugate _ _
    (cornerLiftState_isPureState e he f hf) (cornerLiftState_isPureState e he g hg)
    (cornerUnitary e he u)
  intro a
  change g (cornerCompression e he a) = f (cornerCompression e he _)
  rw [cornerCompression_conjugate]
  exact congrArg (fun k : CStarCorner e he →L[ℂ] ℂ => k (cornerCompression e he a)) hu

end

open scoped CStarAlgebra ComplexOrder InnerProductSpace
section
universe u v
variable {A : Type u} {C : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem corner_extensions_inequivalent_of_matrix_no_common
    (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C) (f g : A →L[ℂ] ℂ)
    (hno : ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      ∀ (π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)), IsIrreducible π →
      ∀ ξ η : H, ‖ξ‖ = 1 → ‖η‖ = 1 →
      (∀ a, ⟪ξ,π (φ a) ξ⟫_ℂ = matrixState f false a) →
      (∀ a, ⟪η,π (φ a) η⟫_ℂ = matrixState g false a) → False)
    (F G : MatrixHNNCorner φ →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState (matrixCornerBase φ) F = f)
    (hrG : restrictState (matrixCornerBase φ) G = g) :
    ¬ UnitarilyEquivalent (pureGNS F hF) (pureGNS G hG) := by
  intro h
  let e := matrixCornerProjection φ
  let he := matrixCornerProjection_isProjection φ
  have hr (K : MatrixHNNCorner φ →L[ℂ] ℂ) (k : A →L[ℂ] ℂ)
      (hk : restrictState (matrixCornerBase φ) K = k) :
      restrictState φ (cornerLiftState e he K) = matrixState k false := by
    ext M
    change K (cornerCompression e he (φ M)) = k (M false false)
    rw [matrixCorner_compression]
    exact congrArg (fun t : A →L[ℂ] ℂ => t (M false false)) hk
  exact pure_extensions_inequivalent_of_no_common φ (matrixState f false) (matrixState g false)
    hno _ _ (cornerLiftState_isPureState e he F hF) (cornerLiftState_isPureState e he G hG)
    (hr F f hrF) (hr G g hrG) (cornerLift_equivalence e he F G hF hG h)

end

open scoped CStarAlgebra ComplexOrder InnerProductSpace
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
attribute [local instance 2000] hnnCStar hnnOrder hnnStarOrder
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

theorem hnnUnitary_conjugates (n : ℕ) :
    (B.hnnUnitary:B.HNNAlgebra)*B.hnnBase (B.peak false n)*star (B.hnnUnitary:B.HNNAlgebra) =
      B.hnnBase (B.peak true n) := B.stable_conjugates_peak n

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
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] C)
  (E : C →L[ℂ] CStarMatrix Bool Bool A)

theorem matrixCornerExpectation_left
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a) (a : A) (x : MatrixHNNCorner φ) :
    matrixCornerExpectation φ E (matrixCornerBase φ a*x) = a*matrixCornerExpectation φ E x := by
  change E (φ (matrixSingle false false a)*(x:C)) false false = _
  rw [hleft,matrixCornerExpectation_supported φ E hleft hright x,matrixSingle_mul,
    matrixSingle_apply,ite_eq_left ⟨rfl,rfl⟩]

theorem matrixCornerExpectation_right
    (hleft : ∀ a x, E (φ a*x) = a*E x)
    (hright : ∀ x a, E (x*φ a) = E x*a) (x : MatrixHNNCorner φ) (a : A) :
    matrixCornerExpectation φ E (x*matrixCornerBase φ a) = matrixCornerExpectation φ E x*a := by
  change E ((x:C)*φ (matrixSingle false false a)) false false = _
  rw [hright,matrixCornerExpectation_supported φ E hleft hright x,matrixSingle_mul,
    matrixSingle_apply,ite_eq_left ⟨rfl,rfl⟩]

end

open scoped CStarAlgebra ComplexOrder

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem PureUEP.of_dense_cover {ι : Type*} (D : ι → Type*)
    [∀ i, CStarAlgebra (D i)]
    (φ : A →⋆ₐ[ℂ] C) (incl : ∀ i, A →⋆ₐ[ℂ] D i) (into : ∀ i, D i →⋆ₐ[ℂ] C)
    (hcomp : ∀ i, (into i).comp (incl i) = φ)
    (hU : ∀ i, PureUEP (incl i))
    (hd : Dense (⋃ i, Set.range (into i))) : PureUEP φ := by
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  let (i : ι) : PartialOrder (D i) := CStarAlgebra.spectralOrder (D i)
  let (i : ι) : StarOrderedRing (D i) := CStarAlgebra.spectralOrderedRing (D i)
  intro f hf F G hF hG hrF hrG
  apply ContinuousLinearMap.ext
  intro x
  apply closure_minimal (t := {z | F z = G z}) ?_
    (isClosed_eq F.continuous G.continuous) (hd x)
  intro x hx
  obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hx
  have hri (H : C →L[ℂ] ℂ) (hH : restrictState φ H = f) :
      restrictState (incl i) (restrictState (into i) H) = f := by
    rw [restrictState_comp,hcomp,hH]
  have hi := hU i f hf (restrictState (into i) F) (restrictState (into i) G)
    (isState_restrict _ _ hF) (isState_restrict _ _ hG) (hri F hrF) (hri G hrG)
  exact congrArg (fun u : D i →L[ℂ] ℂ => u a) hi

end

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

section
namespace HNNWord
variable {A B C : Type*}

theorem join_reduced [Mul B] (L : Bool → B → Prop) (w z : HNNWord B) (b : B)
    (hw : w.Reduced L) (hz : z.Reduced L) (hb : ∀ i, L i (w.lastCoefficient*b)) :
    (w.join b z).Reduced L := by
  induction w with
  | single i a => exact ⟨Or.inr (hb i),hz⟩
  | cons i a w ih =>
    exact ⟨by simpa only [first_join] using hw.1, ih hw.2 hb⟩

theorem eval_join [Monoid B] [Monoid C] (ψ : B →* C) (v : Bool → C)
    (w z : HNNWord B) (b : B) :
    (w.join b z).eval ψ v = w.eval ψ v * ψ b * z.eval ψ v := by
  induction w with
  | single i a => simp only [join,eval,map_mul,mul_assoc]
  | cons i a w ih => simp only [join,eval,ih,mul_assoc]
end HNNWord

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (v : Bool → C)
  (K : Bool → A → Prop) (L : Bool → B → Prop)

def hnnBaseTailSpan : Submodule ℂ C := Submodule.span ℂ
  {x | ∃ (w : HNNWord B) (b : B), w.Reduced L ∧
    w.lastCoefficient ∈ Set.range φ ∧ x = ψ b*w.eval ψ v}

theorem hnnBaseTailSpan_contains_word
    (hKL : ∀ i a, K i a → L i (φ a)) (w : HNNWord A) (a : A) (hw : w.Reduced K) :
    (ψ.comp φ) a*w.eval (ψ.comp φ) v ∈ hnnBaseTailSpan φ ψ v L := by
  have he : (w.mapCoefficients φ).eval ψ v = w.eval (ψ.comp φ) v :=
    w.eval_mapCoefficients φ ψ v
  exact Submodule.subset_span ⟨w.mapCoefficients φ,φ a,
    w.mapCoefficients_reduced φ K L hKL hw,
    ⟨w.lastCoefficient,w.last_mapCoefficients φ |>.symm⟩,by rw [he]; rfl⟩

theorem hnnBaseTailSpan_mul_center_word
    (hKL : ∀ i a, K i a → L i (φ a))
    (b : B) (hb : ∀ i a c, L i (φ a*b*φ c))
    (z : HNNWord A) (a : A) (hz : z.Reduced K)
    {x : C} (hx : x ∈ hnnBaseTailSpan φ ψ v L) :
    x*ψ b*((ψ.comp φ) a*z.eval (ψ.comp φ) v) ∈ hnnBaseTailSpan φ ψ v L := by
  have hze : (z.mapCoefficients φ).eval ψ v = z.eval (ψ.comp φ) v :=
    z.eval_mapCoefficients φ ψ v
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,c,hw,⟨d,hd⟩,rfl⟩ := hx
    have hjoin := w.join_reduced L (z.mapCoefficients φ) (b*φ a) hw
      (z.mapCoefficients_reduced φ K L hKL hz) (fun i => by
        rw [← hd,← mul_assoc]; exact hb i d a)
    apply Submodule.subset_span
    refine ⟨w.join (b*φ a) (z.mapCoefficients φ),c,hjoin,?_,?_⟩
    · rw [HNNWord.last_join,HNNWord.last_mapCoefficients]
      exact ⟨z.lastCoefficient,rfl⟩
    · have heval : (w.join (b*φ a) (z.mapCoefficients φ)).eval ψ v =
          w.eval ψ v * ψ (b*φ a) * (z.mapCoefficients φ).eval ψ v :=
        w.eval_join ψ.toMonoidHom v (z.mapCoefficients φ) (b*φ a)
      rw [heval,hze]
      simp only [map_mul,StarAlgHom.comp_apply,mul_assoc]
  | zero => simpa only [zero_mul] using (hnnBaseTailSpan φ ψ v L).zero_mem
  | add x y hx hy ix iy =>
    simpa only [add_mul] using (hnnBaseTailSpan φ ψ v L).add_mem ix iy
  | smul c x hx ix =>
    simpa only [smul_mul_assoc] using (hnnBaseTailSpan φ ψ v L).smul_mem c ix

end

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
attribute [-instance] _root_.OAI.NaimarkZFC.carIsometricSystem _root_.OAI.NaimarkZFC.carOrder _root_.OAI.NaimarkZFC.carStarOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder OnePoint
namespace PeakingPairData
variable {A C : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (B : PeakingPairData A) (D : PeakingPairData C) (ι : A →⋆ₐ[ℂ] C)
  (hp : ∀ i n, ι (B.peak i n) = D.peak i n) (F : C →L[ℂ] A)
  (hfix : ∀ a, F (ι a) = a)
  (hstate : ∀ f : A →L[ℂ] ℂ, IsState f → IsState (f.comp F))
  (hleft : ∀ a x, F (ι a*x) = a*F x) (hright : ∀ x a, F (x*ι a) = F x*a)
  (ht : ∀ x, B.trace (F x) = D.trace x)

include hp hfix hstate hleft hright ht in

theorem expectation_composite (i : Bool) (x : C) :
    (D.input false).expectation i x = (B.input false).expectation i (F x) := by
  ext z
  induction z using OnePoint.rec with
  | infty =>
    rw [D.expectation_infty,B.expectation_infty]
    exact B.state_composite D ι hp F hfix hstate i x
  | coe n =>
    rw [D.expectation_nat,B.expectation_nat,← B.atom_natural D ι hp i n,
      ← ht,← ht,hright,hleft,hfix]

include hp hfix hstate hleft hright ht in

theorem turnCentered_of_expectation_zero (x : C) (hx : F x = 0)
    (i : Bool) (a b : A) : D.turnCentered i (ι a*x*ι b) := by
  change (D.input false).expectation (!i) (ι a*x*ι b) = 0
  rw [B.expectation_composite D ι hp F hfix hstate hleft hright ht,hright,hleft,hx,mul_zero,zero_mul,map_zero]

end PeakingPairData

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (v : Bool → C)
  (K : Bool → A → Prop) (L : Bool → B → Prop)

theorem hnnReducedSpan_le_baseTailSpan (hKL : ∀ i a, K i a → L i (φ a)) :
    hnnReducedSpan (ψ.comp φ) v K ≤ hnnBaseTailSpan φ ψ v L := by
  apply Submodule.span_le.mpr
  rintro x ⟨w,a,hw,rfl⟩
  exact hnnBaseTailSpan_contains_word φ ψ v K L hKL w a hw

theorem hnnBaseTailSpan_mul_center_span
    (hKL : ∀ i a, K i a → L i (φ a))
    (b : B) (hb : ∀ i a c, L i (φ a*b*φ c))
    {x z : C} (hx : x ∈ hnnBaseTailSpan φ ψ v L)
    (hz : z ∈ hnnReducedSpan (ψ.comp φ) v K) :
    x*ψ b*z ∈ hnnBaseTailSpan φ ψ v L := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨w,a,hw,rfl⟩ := hz
    exact hnnBaseTailSpan_mul_center_word φ ψ v K L hKL b hb w a hw hx
  | zero => simpa only [mul_zero] using (hnnBaseTailSpan φ ψ v L).zero_mem
  | add z t hz ht iz it =>
    simpa only [mul_add] using (hnnBaseTailSpan φ ψ v L).add_mem iz it
  | smul c z hz iz =>
    simpa only [mul_smul_comm] using (hnnBaseTailSpan φ ψ v L).smul_mem c iz

theorem hnnBaseTailClosure_mul_center_closure
    (hKL : ∀ i a, K i a → L i (φ a))
    (b : B) (hb : ∀ i a c, L i (φ a*b*φ c))
    {x z : C} (hx : x ∈ closure (hnnBaseTailSpan φ ψ v L : Set C))
    (hz : z ∈ closure (hnnReducedSpan (ψ.comp φ) v K : Set C)) :
    x*ψ b*z ∈ closure (hnnBaseTailSpan φ ψ v L : Set C) := by
  have hfirst : ∀ y ∈ hnnBaseTailSpan φ ψ v L,
      y*ψ b*z ∈ closure (hnnBaseTailSpan φ ψ v L : Set C) := by
    intro y hy
    apply closure_minimal (s := (hnnReducedSpan (ψ.comp φ) v K : Set C))
      (t := (fun z => y*ψ b*z) ⁻¹' closure (hnnBaseTailSpan φ ψ v L : Set C)) _
      (isClosed_closure.preimage (continuous_const.mul continuous_id)) hz
    intro t ht
    exact subset_closure (hnnBaseTailSpan_mul_center_span φ ψ v K L hKL b hb hy ht)
  exact closure_minimal hfirst (isClosed_closure.preimage
    ((continuous_id.mul continuous_const).mul continuous_const)) hx

theorem hnnBaseTailClosure_expectation_zero (E : C →L[ℂ] B)
    (hred : ∀ (w : HNNWord B) (b : B), w.Reduced L → E (ψ b*w.eval ψ v) = 0)
    {x : C} (hx : x ∈ closure (hnnBaseTailSpan φ ψ v L : Set C)) : E x = 0 := by
  apply closure_minimal (s := (hnnBaseTailSpan φ ψ v L : Set C))
    (t := {z | E z = 0}) _ (isClosed_eq E.continuous continuous_const) hx
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨w,b,hw,_,rfl⟩ := hz; exact hred w b hw
  | zero => exact map_zero E
  | add a b ha hb ia ib =>
    change E (a+b) = 0
    rw [map_add,ia,ib,add_zero]
  | smul c a ha ia =>
    change E (c • a) = 0
    rw [map_smul,ia,smul_zero]

end

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (v : Bool → C)
  (K : Bool → A → Prop) (L : Bool → B → Prop)
  (hKL : ∀ i a, K i a → L i (φ a))
  (F : B →L[ℂ] A) (E : C →L[ℂ] B)
  (hcenter : ∀ b, F b = 0 → ∀ i a c, L i (φ a*b*φ c))
  (hred : ∀ (w : HNNWord B) (b : B), w.Reduced L → E (ψ b*w.eval ψ v) = 0)
  (hleft : ∀ b z, E (ψ b*z) = b*E z) (hright : ∀ z b, E (z*ψ b) = E z*b)

include hKL hcenter hred hright in
theorem hnn_alternating_tail_zero
    (r : List (Bool × C))
    (hr : ∀ p ∈ r, HNNCenteredBlock φ ψ v K F p.1 p.2)
    (hc : r.IsChain (fun p q => p.1 ≠ q.1))
    (hfirst : ∀ p ∈ r.head?, p.1 = false)
    {x : C} (hx : x ∈ closure (hnnBaseTailSpan φ ψ v L : Set C)) :
    E (x*wordValue r) = 0 := by
  induction r using List.twoStepInduction generalizing x with
  | nil =>
    rw [wordValue_nil,mul_one]
    exact hnnBaseTailClosure_expectation_zero φ ψ v L E hred hx
  | singleton p =>
    have hp := hfirst p (by simp)
    have hb := hr p (by simp)
    simp only [HNNCenteredBlock,hp,Bool.false_eq_true,ite_false, if_false] at hb
    obtain ⟨b,hb,hbp⟩ := hb
    simp only [wordValue_cons,wordValue_nil,mul_one,← hbp,hright,
      hnnBaseTailClosure_expectation_zero φ ψ v L E hred hx,zero_mul]
  | cons_cons p q r ih _ =>
    have hp := hfirst p (by simp)
    have hq : q.1 = true := by
      have h := hc.rel
      cases hqp : q.1 <;> simp_all
    have hb := hr p (by simp)
    simp only [HNNCenteredBlock,hp,Bool.false_eq_true,ite_false, if_false] at hb
    obtain ⟨b,hb,hbp⟩ := hb
    have hz := hr q (by simp)
    simp only [HNNCenteredBlock,hq,ite_true, if_true] at hz
    have hnew := hnnBaseTailClosure_mul_center_closure φ ψ v K L hKL b
      (hcenter b hb) hx hz
    have hfirst' : ∀ t ∈ r.head?, t.1 = false := by
      intro t ht
      have h := hc.tail.rel_head? ht
      cases htp : t.1 <;> simp_all
    have ih' := ih (fun t ht => hr t (by simp only [List.mem_cons]; exact Or.inr (Or.inr ht)))
      hc.tail.tail hfirst' hnew
    simpa only [wordValue_cons,← hbp,mul_assoc] using ih'

include hKL hcenter hred hleft hright in

theorem hnn_alternating_expectation_zero
    (hbase : ∀ b, E (ψ b) = b)
    (r : List (Bool × C)) (hne : r ≠ [])
    (hr : ∀ p ∈ r, HNNCenteredBlock φ ψ v K F p.1 p.2)
    (hc : r.IsChain (fun p q => p.1 ≠ q.1)) :
    F (E (wordValue r)) = 0 := by
  cases r with
  | nil => exact (hne rfl).elim
  | cons p r =>
    cases hp : p.1 with
    | true =>
      have hx := hr p (by simp)
      simp only [HNNCenteredBlock,hp,ite_true, if_true] at hx
      have hx' := closure_mono (hnnReducedSpan_le_baseTailSpan φ ψ v K L hKL) hx
      have hfirst : ∀ q ∈ r.head?, q.1 = false := by
        intro q hq
        have h := hc.rel_head? hq
        cases heq : q.1 <;> simp_all
      rw [wordValue_cons,hnn_alternating_tail_zero φ ψ v K L hKL F E hcenter hred hright r
        (fun q hq => hr q (by simp only [List.mem_cons]; exact Or.inr hq)) hc.tail hfirst hx',map_zero]
    | false =>
      have hb := hr p (by simp)
      simp only [HNNCenteredBlock,hp,Bool.false_eq_true,ite_false, if_false] at hb
      obtain ⟨b,hb,hbp⟩ := hb
      cases r with
      | nil => simpa only [wordValue_cons,wordValue_nil,mul_one,← hbp,hbase] using hb
      | cons q r =>
        have hq : q.1 = true := by
          have h := hc.rel
          cases heq : q.1 <;> simp_all
        have hx := hr q (by simp)
        simp only [HNNCenteredBlock,hq,ite_true, if_true] at hx
        have hx' := closure_mono (hnnReducedSpan_le_baseTailSpan φ ψ v K L hKL) hx
        have hfirst : ∀ t ∈ r.head?, t.1 = false := by
          intro t ht
          have h := hc.tail.rel_head? ht
          cases ht' : t.1 <;> simp_all
        have ht := hnn_alternating_tail_zero φ ψ v K L hKL F E hcenter hred hright r
          (fun t ht => hr t (by simp only [List.mem_cons]; exact Or.inr (Or.inr ht)))
          hc.tail.tail hfirst hx'
        rw [wordValue_cons,wordValue_cons,← hbp,hleft,ht,mul_zero,map_zero]

end

open Topology
section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (v : Bool → B) (w : Bool → C)
  (K : Bool → A → Prop) (F : B →⋆ₐ[ℂ] C)
  (hbase : ∀ a, F (φ a) = ψ a) (hletter : ∀ i, F (v i) = w i)

include hbase hletter in
theorem hnnReducedSpan_map {x : B} (hx : x ∈ hnnReducedSpan φ v K) :
    F x ∈ hnnReducedSpan ψ w K := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u,a,hu,rfl⟩ := hz
    rw [map_mul,hbase,HNNWord.eval_hom φ ψ v w F hbase hletter]
    exact Submodule.subset_span ⟨u,a,hu,rfl⟩
  | zero => simpa only [map_zero] using (hnnReducedSpan ψ w K).zero_mem
  | add x y hx hy ix iy => simpa only [map_add] using (hnnReducedSpan ψ w K).add_mem ix iy
  | smul c x hx ix => simpa only [map_smul] using (hnnReducedSpan ψ w K).smul_mem c ix

include hbase hletter in
theorem hnnReducedClosure_map {x : B} (hx : x ∈ closure (hnnReducedSpan φ v K : Set B)) :
    F x ∈ closure (hnnReducedSpan ψ w K : Set C) := by
  have hs : (hnnReducedSpan φ v K : Set B) ⊆
      F ⁻¹' closure (hnnReducedSpan ψ w K : Set C) :=
    fun z hz => subset_closure (hnnReducedSpan_map φ ψ v w K F hbase hletter hz)
  have hc : IsClosed (F ⁻¹' closure (hnnReducedSpan ψ w K : Set C)) :=
    isClosed_closure.preimage (starAlgHomCLM F).continuous
  exact closure_minimal hs hc hx

end

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

variable (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
  (jQ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra) (jB : B.HNNAlgebra →⋆ₐ[ℂ] E.HNNAlgebra)

theorem rightHNNFamily_base (ha : ∀ a, jB (B.hnnBase a) = E.hnnBase (Q.hnnBase a)) (i : Bool) :
    (rightHNNFamily B Q E jB i).toAlgHom.comp (pairHNNBase B Q i).toAlgHom =
      (E.hnnBase.comp Q.hnnBase).toAlgHom := by
  cases i
  · ext a; exact ha a
  · rfl

end PeakingPairData

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open UniformSpace
open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology
section
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]

theorem cstarDirectLimit_pureUEP
    (hU : ∀ i j h, PureUEP (f i j h)) (i : I) :
    PureUEP (cstarDirectLimitInclude A f i) := by
  apply PureUEP.of_dense_cover (fun j : {j : I // i ≤ j} => A j.val)
    (cstarDirectLimitInclude A f i) (fun j => f i j.val j.property)
    (fun j => cstarDirectLimitInclude A f j.val)
  · intro j
    ext a
    exact cstarDirectLimitInclude_compatible A f i j.val j.property a
  · intro j
    exact hU i j.val j.property
  · exact cstarDirectLimitInclude_tail_dense A f i

end

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

theorem carSimple : IsSimpleCStar CAR := by
  apply simple_of_dense_stage_ranges CARStage _ carInclude carInclude_isometry
    (cstarDirectLimitInclude_dense CARStage carBond)
  intro n
  refine ⟨inferInstance,fun J _ => ?_⟩
  exact eq_bot_or_eq_top J

instance carSeparable : TopologicalSpace.SeparableSpace CAR := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  rw [← (cstarDirectLimitInclude_dense CARStage carBond).closure_eq]
  apply TopologicalSpace.IsSeparable.closure
  apply TopologicalSpace.IsSeparable.iUnion
  intro n
  exact TopologicalSpace.isSeparable_range (carInclude_isometry n).continuous

theorem carInfiniteDimensional : ¬ Module.Finite ℂ CAR := by
  intro hf
  let := hf
  have hle (n : ℕ) : 4^n ≤ Module.finrank ℂ CAR := by
    rw [← carStage_finrank n]
    exact LinearMap.finrank_le_finrank_of_injective (f := (carInclude n).toLinearMap)
      (carInclude_isometry n).injective
  have hg := hle (Module.finrank ℂ CAR+1)
  have hp := Nat.lt_pow_self (n := Module.finrank ℂ CAR+1) (a := 4) (by norm_num)
  omega

open scoped ComplexOrder CStarAlgebra

theorem carTrace_isState : IsState carTrace := cstarDirectLimitState_isState _ _ _ _ _

theorem carVector_isState : IsState carVector := cstarDirectLimitState_isState _ _ _ _ _

open scoped ComplexOrder CStarAlgebra

theorem carStagePeak_projection (n : ℕ) : IsStarProjection (carStagePeak n) := by
  induction n with
  | zero => exact IsStarProjection.one ℂ
  | succ n ih => exact matrixSingle_projection false (carStagePeak n) ih

theorem carStagePeak_compress (n : ℕ) (a : CARStage n) :
    carStagePeak n*a*carStagePeak n = (carStageVector n).1 a • carStagePeak n := by
  induction n with
  | zero =>
    let z : ℂ := a
    change (1:ℂ)*z*1 = z • (1:ℂ)
    simp
  | succ n ih =>
    let M : CStarMatrix Bool Bool (CARStage n) := a
    change matrixSingle false false (carStagePeak n)*M*matrixSingle false false (carStagePeak n) = _
    rw [matrixSingle_compress,ih]
    exact matrixSingle_smul false false (carStagePeak n) ((carStageVector n).1 (M false false))

theorem carStagePeak_bond (n : ℕ) :
    carStep n (carStagePeak n) * carStagePeak (n+1) = carStagePeak (n+1) := by
  change Matrix.diagonal (fun _ : Bool => carStagePeak n) * Matrix.single false false (carStagePeak n) = _
  ext i j
  rw [Matrix.diagonal_mul]
  change carStagePeak n * (if false = i ∧ false = j then carStagePeak n else 0) =
    (if false = i ∧ false = j then carStagePeak n else 0)
  split_ifs
  · exact (carStagePeak_projection n).isIdempotentElem.eq
  · exact mul_zero _

theorem carPeak_projection (n : ℕ) : IsStarProjection (carPeak n) :=
  (carStagePeak_projection n).map (carInclude n)

theorem carPeak_antitone : Antitone carPeak := by
  apply antitone_nat_of_succ_le
  intro n
  apply ((carPeak_projection (n+1)).le_iff_mul_eq_right (carPeak_projection n)).mpr
  change carInclude n (carStagePeak n) * carInclude (n+1) (carStagePeak (n+1)) = _
  have hb := cstarDirectLimitInclude_compatible CARStage carBond n (n+1) (Nat.le_succ n) (carStagePeak n)
  rw [carBond_succ n n le_rfl, carBond_self, StarAlgHom.comp_apply] at hb
  change carInclude (n+1) (carStep n (carStagePeak n)) = carInclude n (carStagePeak n) at hb
  rw [← hb,← map_mul,carStagePeak_bond]
  rfl

theorem carPeak_unique (g : CAR →L[ℂ] ℂ) (hg : IsState g)
    (hp : ∀ n, g (carPeak n) = 1) : g = carVector := by
  ext x
  apply cstarDirectLimit_induction CARStage carBond (P := fun x => g x = carVector x)
    (isClosed_eq g.continuous carVector.continuous) _ x
  intro n a
  have he := state_compression g hg (carPeak n) ((carPeak_projection n).norm_le _)
    (carPeak_projection n).isSelfAdjoint (hp n) (carInclude n a)
  rw [carVector_stage]
  rw [← he]
  change g (carInclude n (carStagePeak n) * carInclude n a * carInclude n (carStagePeak n)) = _
  rw [← map_mul,← map_mul,carStagePeak_compress,map_smul,map_smul]
  change (carStageVector n).1 a • g (carPeak n) = _
  rw [hp n,smul_eq_mul,mul_one]

theorem carPeak_peaks : Peaks carPeak carVector :=
  ⟨carPeak_projection,carPeak_antitone,carVector_isState,carVector_peak,carPeak_unique⟩

theorem carVector_isPure : IsPureState carVector := carPeak_peaks.isPureState

open scoped ComplexOrder CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A]

theorem matrixScalar_eq_sum_single (a : A) : matrixScalarHom A a =
    matrixSingle false false a + matrixSingle true true a := by
  ext i j
  cases i <;> cases j <;> simp [matrixScalarHom,matrixSingle_apply,Matrix.diagonal]

theorem trace_matrix_corner (f : CStarMatrix Bool Bool A →ₗ[ℂ] ℂ)
    (htr : ∀ a b, f (a*b) = f (b*a)) (a : A) :
    f (matrixScalarHom A a) = 2 * f (matrixSingle false false a) := by
  rw [matrixScalar_eq_sum_single,map_add,← trace_two_corners f htr,two_mul]

end

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
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
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_state_excision_witness (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : A, 0 ≤ x ∧ ‖x‖ ≤ 1 ∧ f x = 1 ∧ ‖x*(a-f a • (1:A))*x‖ < ε := by
  let F := positiveOfSquares f hf.1.2
  let π := F.gnsNonUnitalStarAlgHom
  let ξ := gnsVector F
  have hπ : IsIrreducible π := pure_gns_irreducible f hf.1 hf
  have hξ : ‖ξ‖ = 1 := gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1
  have hexc := (pureExcisionNet_excision π hπ ξ hξ a).norm
  have hcoeff : ⟪ξ,π a ξ⟫_ℂ = f a := gnsVector_coefficient F a
  simp only [hcoeff,norm_zero] at hexc
  obtain ⟨i,hi⟩ := (hexc.eventually (gt_mem_nhds hε)).exists
  refine ⟨pureExcisionNet π ξ i,pureExcisionNet_nonneg π ξ i,
    pureExcisionNet_norm π ξ i,?_,hi⟩
  change F (pureExcisionNet π ξ i) = 1
  rw [← gnsVector_coefficient F]
  change ⟪ξ,π (pureExcisionNet π ξ i) ξ⟫_ℂ = 1
  rw [pureExcisionNet_fixes π (by change F.gnsStarAlgHom 1 = 1; exact map_one _) ξ i]
  rw [inner_self_eq_norm_sq_to_K, hξ]
  norm_num

end

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder
section
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_restrict_of_witnesses (f : A →L[ℂ] ℂ) (hf : IsState f)
    (C : StarSubalgebra ℂ A) [IsClosed (C : Set A)]
    [PartialOrder C] [StarOrderedRing C]
    (D : Set A) (hD : D ⊆ C) (hd : (C : Set A) ⊆ closure D)
    (hexc : ∀ a ∈ D, ∀ ε : ℝ, 0 < ε → ∃ x ∈ C,
      0 ≤ x ∧ ‖x‖ ≤ 1 ∧ f x = 1 ∧ ‖x*(a-f a • (1:A))*x‖ < ε) :
    IsPureState (restrictState C.subtype f) := by
  let D' : Set C := Subtype.val ⁻¹' D
  have hd' : Dense D' := by
    apply (IsInducing.subtypeVal.dense_iff).mpr
    intro a
    apply closure_mono (s := D) _ (hd a.property)
    intro z hz
    exact ⟨⟨z,hD hz⟩,hz,rfl⟩
  apply pure_of_dense_excision _ (isState_restrict C.subtype f hf) D' hd'
  intro a ha ε hε
  obtain ⟨x,hx,hxp,hxn,hxf,herr⟩ := hexc a ha ε hε
  refine ⟨⟨x,hx⟩,?_,hxn,hxf,herr⟩
  exact (faithfulStarHom_nonneg_iff C.subtype Subtype.val_injective ⟨x,hx⟩).mp hxp

theorem countable_pure_restriction
    (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    (B : Set ι → StarSubalgebra ℂ A) (hclosed : ∀ S, IsClosed (B S : Set A))
    (hmono : Monotone B)
    (hsep : ∀ S, S.Countable → TopologicalSpace.IsSeparable (B S : Set A))
    (hsupp : ∀ a : A, ∃ S, S.Countable ∧ a ∈ B S)
    (hlim : ∀ N : ℕ → Set ι, Monotone N →
      (B (⋃ n, N n) : Set A) ⊆ closure (⋃ n, (B (N n) : Set A)))
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set ι, S.Countable ∧ DependencyClosed I S ∧
      IsPureState (restrictState (B S).subtype f) := by
  classical
  have hw (a : A) (m : ℕ) := pure_state_excision_witness f hf a
    (1/((m:ℝ)+1)) (by positivity)
  choose w hwp hwn hwf hwe using hw
  obtain ⟨S,hSc,hSI,D,_,hD,hd,hwmem⟩ := countable_witness_closure I hI
    (fun S => (B S : Set A)) (fun _ _ h => hmono h) hsep hsupp hlim w
  refine ⟨S,hSc,hSI,?_⟩
  let : IsClosed (B S : Set A) := hclosed S
  let : PartialOrder (B S) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (B S) := CStarAlgebra.spectralOrderedRing _
  apply pure_restrict_of_witnesses f hf.1 (B S) D hD hd
  intro a ha ε hε
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hε
  exact ⟨w a m,hwmem a ha m,hwp a m,hwn a m,hwf a m,(hwe a m).trans hm⟩

end

section
attribute [local instance] generatedFamily_isClosed
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem generatedFamily_countable_pure_restriction
    (base : Set A) (v : ι → A) (hbase : TopologicalSpace.IsSeparable base)
    (hgen : generatedFamily base v Set.univ = ⊤)
    (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set ι, S.Countable ∧ DependencyClosed I S ∧
      IsPureState (restrictState (generatedFamily base v S).subtype f) := by
  apply countable_pure_restriction I hI (generatedFamily base v)
    (generatedFamily_isClosed base v) (generatedFamily_mono base v)
    (fun _ hS => generatedFamily_separable base v hbase hS) ?_
    (generatedFamily_iUnion base v) f hf
  intro a
  have ha : a ∈ generatedFamily base v Set.univ := by rw [hgen]; trivial
  obtain ⟨S,hS,_,haS⟩ := generatedFamily_countable_support base v Set.univ ha
  exact ⟨S,hS,haS⟩

end

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra InnerProductSpace
section
universe u v w
variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [PartialOrder A] [StarOrderedRing A]

theorem irreducible_vector_pure_equivalent
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ξ : H) (hξ : ‖ξ‖ = 1) :
    ∃ hf : IsPureState (vectorFunctional π ξ),
      UnitarilyEquivalent (pureGNS (vectorFunctional π ξ) hf) π := by
  have hs := irreducible_vector_state π hπ ξ hξ
  have hn : ξ ≠ 0 := by
    intro h
    have hz : (0:ℝ) = 1 := by simpa only [h,norm_zero] using hξ
    exact zero_ne_one hz
  have he := cyclic_representation_equivalent (positiveOfSquares (vectorFunctional π ξ) hs.2)
    π ξ (fun _ => rfl) (irreducible_vector_cyclic π hπ ξ hn)
  have hp := isPureState_of_gns_irreducible (vectorFunctional π ξ) hs
    (he.symm.isIrreducible hπ)
  exact ⟨hp,he⟩

end

open Filter Topology
open scoped CStarAlgebra

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

def reference : X →L[ℂ] ℂ :=
  ((X.baseUEP carVector carVector_isPure).exists_unique_pure X.base_injective carVector_isPure).choose

lemma reference_spec : IsPureState X.reference ∧ restrictState X.base X.reference = carVector :=
  ⟨((X.baseUEP carVector carVector_isPure).exists_unique_pure X.base_injective carVector_isPure).choose_spec.1,
    ((X.baseUEP carVector carVector_isPure).exists_unique_pure X.base_injective carVector_isPure).choose_spec.2.1⟩

end TracialStage
end

open scoped CStarAlgebra ComplexOrder

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
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem simple_infinite_no_compacts (hA : IsSimpleCStar A)
    (hinf : ¬ FiniteDimensional ℂ A)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (a : A) (ha : IsCompactOperator (π a)) : π a = 0 := by
  rcases hA.2 (compactPreimageIdeal π) (compactPreimageIdeal_isClosed π) with hb | ht
  · have ham : a ∈ compactPreimageIdeal π := (mem_compactPreimageIdeal π a).mpr ha
    rw [hb,TwoSidedIdeal.mem_bot] at ham
    rw [ham,map_zero]
  · have h1 : (1:A) ∈ compactPreimageIdeal π := by rw [ht]; exact TwoSidedIdeal.mem_top _
    rw [mem_compactPreimageIdeal] at h1
    rw [irreducible_map_one π hπ] at h1
    let : FiniteDimensional ℂ H := isCompactOperator_id_iff_finiteDimensional.mp h1
    exact False.elim (hinf (FiniteDimensional.of_injective (irreducibleUnitalRepresentation π hπ).toAlgHom.toLinearMap
      (simple_nonzeroStarHom_injective hA π hπ.1)))

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

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
namespace KOS

section

variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

def LocalControl : Prop :=
  ∀ (f : A →L[ℂ] ℂ), IsPureState f → ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (G : Finset A) (δ : ℝ), 0 < δ ∧
      ∀ (g : A →L[ℂ] ℂ), IsPureState g → Close G δ f g →
        ∀ (K : Finset A) (η : ℝ), 0 < η →
          ∃ θ : A ≃⋆ₐ[ℂ] A,
            (∀ a ∈ F, dist (θ a) a < ε) ∧
            Close K η (restrictState θ.toStarAlgHom f) g

def SameClassControl : Prop :=
  ∀ (f : A →L[ℂ] ℂ) (hf : IsPureState f), ∀ (F : Finset A) (ε : ℝ), 0 < ε →
    ∃ (G : Finset A) (δ : ℝ), 0 < δ ∧
      ∀ (g : A →L[ℂ] ℂ) (hg : IsPureState g),
        PureStateEquivalent f hf g hg → Close G δ f g →
          ∃ θ : A ≃⋆ₐ[ℂ] A,
            (∀ a ∈ F, dist (θ a) a < ε) ∧
            restrictState θ.toStarAlgHom f = g

end

section
open Filter Topology
variable {A : Type*} [cStarAlgebraA : CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

structure ControlData (f : A →L[ℂ] ℂ) (F : Finset A) (ε : ℝ) where
  tests : Finset A
  radius : ℝ
  positive : 0 < radius
  correct : ∀ (g : A →L[ℂ] ℂ), IsPureState g → Close tests radius f g →
    ∀ (K : Finset A) (η : ℝ), 0 < η →
      ∃ θ : A ≃⋆ₐ[ℂ] A,
        (∀ a ∈ F, dist (θ a) a < ε) ∧
        Close K η (restrictState θ.toStarAlgHom f) g

omit partialOrderA starOrderedRingA in
theorem exists_controlData [PartialOrder A] [StarOrderedRing A] (h : LocalControl (A := A))
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) (F : Finset A) (ε : ℝ) (hε : 0 < ε)
    (T : Finset A) (r : ℝ) (hr : 0 < r) :
    ∃ C : ControlData f F ε, T ⊆ C.tests ∧ C.radius ≤ r := by
  classical
  obtain ⟨G,δ,hδ,hC⟩ := h f hf F ε hε
  refine ⟨⟨G ∪ T,min δ r,lt_min hδ hr,?_⟩,Finset.subset_union_right, min_le_right _ _⟩
  intro g hg hgclose K η hη
  apply hC g hg _ K η hη
  intro a ha
  exact (hgclose a (Finset.mem_union_left T ha)).trans_le (min_le_left _ _)

end

end KOS

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]

def NearCentralRows : Prop :=
  ∀ (f : A →L[ℂ] ℂ) (hf : IsPureState f) (F : Finset A) (c : ℝ), 0 < c →
    ∃ (n : ℕ) (x : Fin n → A),
      pureGNS f hf (rowAverage x 1) (gnsVector (positiveOfSquares f hf.1.2)) =
        gnsVector (positiveOfSquares f hf.1.2) ∧
      ∀ b ∈ F, ∀ a : A, 0 ≤ a → a ≤ 1 →
        ‖b*rowAverage x a-rowAverage x a*b‖ ≤ c

end KOS

open scoped InnerProductSpace

open scoped CStarAlgebra ComplexOrder

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

namespace HNNWord
variable {A D I : Type*}

theorem lift_reduced (φ : D → A) (K : Bool → D → Prop) (L : Bool → A → Prop)
    (hreflect : ∀ i a, L i (φ a) → K i a) (w : HNNWord A)
    (hw : w.AllCoefficients (Set.range φ)) (hr : w.Reduced L) :
    ∃ u : HNNWord D, u.mapCoefficients φ = w ∧ u.Reduced K := by
  induction w with
  | single i a =>
    obtain ⟨b,rfl⟩ := hw
    exact ⟨.single i b,rfl,trivial⟩
  | cons i a w ih =>
    obtain ⟨b,rfl⟩ := hw.1
    obtain ⟨u,hu,hku⟩ := ih hw.2 hr.2
    refine ⟨.cons i b u,?_,?_,hku⟩
    · simp only [mapCoefficients,hu]
    · rcases hr.1 with hi | hi
      · left
        rw [← hu] at hi
        simpa only [first_mapCoefficients] using hi
      · exact Or.inr (hreflect i b hi)

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
section
universe u v
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma subalgebra_pureUEP_congr (S T S' T' : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    [IsClosed (S' : Set A)] [IsClosed (T' : Set A)]
    (hST : S ≤ T) (hST' : S' ≤ T') (hS : S = S') (hT : T = T')
    (h : PureUEP (StarSubalgebra.inclusion hST)) :
    PureUEP (StarSubalgebra.inclusion hST') := by
  subst S'
  subst T'
  exact h

lemma subalgebra_pureRestriction_congr (S T : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)] (hST : S = T)
    (f : A →L[ℂ] ℂ) (h : IsPureState (restrictState S.subtype f)) :
    IsPureState (restrictState T.subtype f) := by
  subst T
  exact h

end

open Cardinal Topology TopologicalSpace

open Cardinal Topology TopologicalSpace

end NaimarkZFC

end

end OAI
end


