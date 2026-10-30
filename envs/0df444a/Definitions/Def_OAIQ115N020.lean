-- Prove2me | Definitions.Def_OAIQ115N020
-- name    : OAIQ115N020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:23:38.779518+00:00
-- url     : https://prove2.me/theorems/e1f447f5-e194-4d53-bd94-b38295d6ec92
-- title:
--   Definitions bundle OAIQ115N020 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 2 instances and 13 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean), [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N014` and `OAIQ115N015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N022`, `OAIQ115N023` and `OAIQ115N024`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N014
import Definitions.Def_OAIQ115N015

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem stable_conjugates_peak (n : ℕ) :
    (B.stableUnitary:B.Corner)*B.cornerBase (B.peak false n)*star (B.stableUnitary:B.Corner) =
      B.cornerBase (B.peak true n) := by
  have hh := matrixStable_conjugates B.embedBase B.embedAux B.diagonal
    B.model_diagonal_agree (B.tail n)
  simpa only [stableUnitary,matrixStableUnitary,cornerBase,B.diagonal_tail] using hh

end PeakingPairData

open scoped CStarAlgebra Matrix

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

section
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A]
variable (e : A) (he : IsStarProjection e)

theorem cornerTrace_tracial (t : A →L[ℂ] ℂ) (c : ℝ)
    (htr : ∀ a b, t (a*b) = t (b*a)) (a b : CStarCorner e he) :
    cornerTrace e he t c (a*b) = cornerTrace e he t c (b*a) :=
  congrArg (c • ·) (htr a b)

end

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
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem Peaks.join_extensions {p q : ℕ → A} {f g : A →L[ℂ] ℂ}
    (hp : Peaks p f) (hq : Peaks q g) (φ : A →⋆ₐ[ℂ] C) (u : unitary C)
    (hconj : ∀ n, (u:C)*φ (p n)*star (u:C) = φ (q n))
    (hu : StateExtensionUnique φ g)
    (F G : C →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState φ F = f) (hrG : restrictState φ G = g) :
    UnitarilyEquivalent (pureGNS F hF) (pureGNS G hG) := by
  let H := restrictState (Unitary.conjStarAlgAut ℂ C u).symm.toStarAlgHom F
  have hH : IsState H := isState_restrict _ _ hF.1
  have hres : restrictState φ H = g := by
    apply hq.2.2.2.2 _ (isState_restrict φ H hH)
    intro n
    change F (star (u:C)*φ (q n)*(u:C)) = 1
    rw [← hconj]
    have hh : star (u:C)*((u:C)*φ (p n)*star (u:C))*(u:C) = φ (p n) := by
      calc
        _ = (star (u:C)*(u:C))*φ (p n)*(star (u:C)*(u:C)) := by simp only [mul_assoc]
        _ = _ := by rw [u.property.1,one_mul,mul_one]
    rw [hh]
    change restrictState φ F (p n) = 1
    rw [hrF]
    exact hp.2.2.2.1 n
  have he := hu H G hH hG.1 hres hrG
  apply pureState_equivalent_of_conjugate F G hF hG u
  intro a
  exact (congrArg (fun k : C →L[ℂ] ℂ => k a) he).symm

end

section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
theorem Peaks.join_named {p q : ℕ → A} {f g : A →L[ℂ] ℂ}
    (hp : Peaks p f) (hq : Peaks q g) (φ : A →⋆ₐ[ℂ] C) (u : unitary C)
    (hconj : ∀ n, (u:C)*φ (p n)*star (u:C) = φ (q n))
    (hu : StateExtensionUnique φ g)
    (F G : C →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState φ F = f) (hrG : restrictState φ G = g) :
    PureStateEquivalent F hF G hG :=
  hp.join_extensions hq φ u hconj hu F G hF hG hrF hrG
end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem equivalent_pure_coefficient_vector (φ : A →⋆ₐ[ℂ] C)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (he : UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (π : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hc : ∀ a, ⟪ξ,π (φ a) ξ⟫_ℂ = f a) :
    ∃ η : H, ‖η‖ = 1 ∧ ∀ a, ⟪η,π (φ a) η⟫_ℂ = g a := by
  obtain ⟨u,hu⟩ := pureState_equivalent_conjugate f g hf hg he
  let ψ := π.comp φ.toNonUnitalStarAlgHom
  let η := π (φ (u:A)) ξ
  have hn : (‖η‖ : ℂ)^2 = 1 := by
    calc
      _ = vectorFunctional ψ ξ (star (u:A)*(u:A)) :=
        (vectorFunctional_square ψ ξ (u:A)).symm
      _ = f (star (u:A)*(u:A)) := hc _
      _ = 1 := by rw [u.property.1,((isState_iff f).mp hf.1).1]
  refine ⟨η,?_,?_⟩
  · have hn' := congrArg Complex.re hn
    simp only [← Complex.ofReal_pow,Complex.ofReal_re,Complex.one_re] at hn'
    nlinarith [norm_nonneg η]
  · intro a
    change ⟪π (φ (u:A)) ξ,π (φ a) (π (φ (u:A)) ξ)⟫_ℂ = g a
    calc
      _ = ⟪ξ,π (φ (star (u:A)*a*(u:A))) ξ⟫_ℂ := by
        simp only [map_mul,map_star,mul_apply_eq_comp,
          ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = f (star (u:A)*a*(u:A)) := hc _
      _ = g a := (congrArg (fun k : A →L[ℂ] ℂ => k a) hu).symm

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder
section
variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

theorem cornerCompression_conjugate (u : unitary (CStarCorner e he)) (a : A) :
    cornerCompression e he (star (cornerUnitary e he u : A)*a*(cornerUnitary e he u : A)) =
      star (u:CStarCorner e he)*cornerCompression e he a*(u:CStarCorner e he) := by
  let x : CStarCorner e he := u
  have hs : star (x:A)*e = star (x:A) := (star x).property.2
  have hl : e*star (cornerUnitary e he u : A) = star (x:A) := by
    rw [cornerUnitary_apply]
    simp only [star_add,star_sub,star_one,he.isSelfAdjoint.star_eq,mul_add,mul_sub,
      mul_one,he.isIdempotentElem.eq,sub_self,add_zero]
    exact (star x).property.1
  have hr : (cornerUnitary e he u : A)*e = (x:A) := by
    rw [cornerUnitary_apply]
    simp only [add_mul,sub_mul,one_mul,he.isIdempotentElem.eq,sub_self,add_zero]
    exact x.property.2
  apply Subtype.ext
  change e*(star (cornerUnitary e he u : A)*a*(cornerUnitary e he u : A))*e =
    star (x:A)*(e*a*e)*(x:A)
  calc
    _ = (e*star (cornerUnitary e he u : A))*a*((cornerUnitary e he u : A)*e) := by
      simp only [mul_assoc]
    _ = star (x:A)*a*(x:A) := by rw [hl,hr]
    _ = _ := by
      symm
      calc
        _ = (star (x:A)*e)*a*(e*(x:A)) := by simp only [mul_assoc]
        _ = _ := by rw [hs,x.property.1]

end

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

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Extension
attribute [-instance] _root_.OAI.NaimarkZFC.carIsometricSystem
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

include hp hfix hstate in
theorem state_composite (i : Bool) (x : C) : D.state i x = B.state i (F x) := by
  have hh := (D.peaks i).2.2.2.2 ((B.state i).comp F) (hstate _ (B.peaks i).2.2.1) (fun n => by
    change B.state i (F (D.peak i n)) = 1
    rw [← hp,hfix]
    exact (B.peaks i).2.2.2.1 n)
  exact (congrArg (fun g : C →L[ℂ] ℂ => g x) hh).symm

end PeakingPairData

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
section
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]
  (τ : ∀ i, A i →L[ℂ] ℂ) (hτ : ∀ i, IsState (τ i))
  (hcompat : ∀ i j h a, τ j (f i j h a) = τ i a)

attribute [local instance] OAI.NaimarkZFC.directLimitNormTopology
theorem cstarDirectLimitState_isState : IsState (cstarDirectLimitState A f τ hτ hcompat) := by
  let : PartialOrder (CStarDirectLimit A f) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CStarDirectLimit A f) := CStarAlgebra.spectralOrderedRing _
  rw [isState_iff]
  constructor
  · let i : I := Classical.choice inferInstance
    rw [← map_one (cstarDirectLimitInclude A f i),cstarDirectLimitState_stage]
    let : PartialOrder (A i) := CStarAlgebra.spectralOrder _
    let : StarOrderedRing (A i) := CStarAlgebra.spectralOrderedRing _
    exact ((isState_iff (τ i)).mp (hτ i)).1
  · intro x
    refine cstarDirectLimit_induction A f (P := fun a =>
      ((cstarDirectLimitState A f τ hτ hcompat) (star a*a)).im = 0 ∧
      0 ≤ ((cstarDirectLimitState A f τ hτ hcompat) (star a*a)).re) ?_ ?_ x
    · have hc : Continuous (fun a : CStarDirectLimit A f =>
          cstarDirectLimitState A f τ hτ hcompat (star a*a)) := by fun_prop
      exact (isClosed_eq (Complex.continuous_im.comp hc) continuous_const).inter
        (isClosed_le continuous_const (Complex.continuous_re.comp hc))
    · intro i a
      rw [← map_star,← map_mul,cstarDirectLimitState_stage]
      exact (hτ i).2 a

theorem cstarDirectLimitState_tracial (htr : ∀ i a b, τ i (a*b) = τ i (b*a))
    (x y : CStarDirectLimit A f) :
    cstarDirectLimitState A f τ hτ hcompat (x*y) =
      cstarDirectLimitState A f τ hτ hcompat (y*x) := by
  induction x, y using Completion.induction_on₂
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · rename_i x y
    rw [← Completion.coe_mul,← Completion.coe_mul]
    simp only [cstarDirectLimitState, ContinuousLinearMap.fromCompletion_apply_coe]
    induction x, y using DirectLimit.induction₂ f with
    | ih i a b =>
      rw [DirectLimit.mul_def,DirectLimit.mul_def]
      exact htr i a b

end

open scoped CStarAlgebra ComplexOrder

open Topology
section
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]

theorem cstarDirectLimit_simple (hA : ∀ i, IsSimpleCStar (A i)) :
    IsSimpleCStar (CStarDirectLimit A f) := by
  let : PartialOrder (CStarDirectLimit A f) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (CStarDirectLimit A f) := CStarAlgebra.spectralOrderedRing _
  exact simple_of_dense_stage_ranges A hA (cstarDirectLimitInclude A f)
    (cstarDirectLimitInclude_isometry A f) (cstarDirectLimitInclude_dense A f)

theorem cstarDirectLimitInclude_tail_dense (i : I) :
    Dense (⋃ j : {j : I // i ≤ j}, Set.range (cstarDirectLimitInclude A f j.val)) := by
  apply (cstarDirectLimitInclude_dense A f).mono
  intro a ha
  obtain ⟨j,b,rfl⟩ := Set.mem_iUnion.mp ha
  obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
  apply Set.mem_iUnion.mpr
  exact ⟨⟨k,hik⟩,f j k hjk b,cstarDirectLimitInclude_compatible A f j k hjk b⟩

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

instance carOrder : PartialOrder CAR := CStarAlgebra.spectralOrder _
instance carStarOrder : StarOrderedRing CAR := CStarAlgebra.spectralOrderedRing _

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A]

theorem trace_two_corners (f : CStarMatrix Bool Bool A →ₗ[ℂ] ℂ)
    (htr : ∀ a b, f (a*b) = f (b*a)) (a : A) :
    f (matrixSingle false false a) = f (matrixSingle true true a) := by
  simpa only [matrixSingle_mul,mul_one,one_mul] using
    htr (matrixSingle false true a) (matrixSingle true false 1)

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
attribute [-instance] _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
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

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra

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
theorem retainedOrdinalSuccessor_identity (j : Ordinal.{u}) (hj : j ∈ S) :
    BridgeSuccessor (retainedOrdinalInclusion base v S
      (show j ≤ j+1 by exact le_self_add)) := by
  let φ := retainedOrdinalInclusion base v S (show j ≤ j+1 by exact le_self_add)
  have hs : Function.Surjective φ := by
    intro x
    have hx : (x:A) ∈ retainedOrdinalAlgebra base v S j := by
      rw [← retainedOrdinalSucc_eq_of_mem base v S j hj]
      exact x.property
    exact ⟨⟨x,hx⟩,rfl⟩
  exact BridgeSuccessor.identity (StarAlgEquiv.ofBijective φ
    ⟨retainedOrdinalInclusion_injective base v S _,hs⟩) (fun _ => rfl)

end

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

end NaimarkZFC

end

end OAI
end


