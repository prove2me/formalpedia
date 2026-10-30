-- Prove2me | Definitions.Def_OAIQ115N019
-- name    : OAIQ115N019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:36:44.469717+00:00
-- url     : https://prove2.me/theorems/390126f2-6eb4-4d06-8757-e4c587d4bc27
-- title:
--   Definitions bundle OAIQ115N019 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 5 definitions, 3 instances and 16 theorems. The definitions and types are `OAI.NaimarkZFC.PeakingPairData.hnnUnitary`, `OAI.NaimarkZFC.PeakingPairData.leftHNNFamily`, `OAI.NaimarkZFC.PeakingPairData.pairHNN`, `OAI.NaimarkZFC.PeakingPairData.pairHNNBase`, `OAI.NaimarkZFC.PeakingPairData.rightHNNFamily`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean), [`Naimark_Extension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Extension.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N014` and `OAIQ115N015` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N022` and `OAIQ115N023`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N014
import Definitions.Def_OAIQ115N015

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
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
section
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
    (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)

theorem matrixEntrySubalgebra_closed (S : StarSubalgebra ℂ (MatrixHNNCorner φ))
    (hS : IsClosed (S : Set (MatrixHNNCorner φ))) :
    IsClosed (matrixEntrySubalgebra φ S : Set Z) := by
  change IsClosed {z | ∀ i j, matrixCornerEntry φ i j z ∈ S}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j =>
    hS.preimage (matrixCornerEntry φ i j).continuous

theorem matrixCorner_generated_of_entries (T : Set Z)
    (hd : Dense (StarAlgebra.adjoin ℂ T : Set Z))
    (S : StarSubalgebra ℂ (MatrixHNNCorner φ))
    (hS : IsClosed (S : Set (MatrixHNNCorner φ)))
    (hentries : ∀ z ∈ T, ∀ i j, matrixCornerEntry φ i j z ∈ S) : S = ⊤ := by
  have hsub : StarAlgebra.adjoin ℂ T ≤ matrixEntrySubalgebra φ S := by
    exact StarAlgebra.adjoin_le (fun z hz => hentries z hz)
  have hall : ∀ z : Z, z ∈ matrixEntrySubalgebra φ S := by
    intro z
    apply (matrixEntrySubalgebra_closed φ S hS).closure_subset
    exact closure_mono hsub (hd z)
  apply eq_top_iff.mpr
  intro z _
  have h := hall (z:Z) false false
  simpa only [matrixCornerEntry_corner] using h

variable (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
    (diag : ∀ i : Bool, φ (matrixSingle i i (1 : A)) = ψ (matrixSingle i i (1 : D)))

include diag in

theorem matrixCornerEntry_letter_false (i j : Bool) :
    matrixCornerEntry φ i j (bridgeLetter ψ false) =
      if i = false ∧ j = true then star (matrixStable φ ψ diag) else 0 := by
  apply Subtype.ext
  change φ (matrixSingle false i 1) * ψ (matrixSingle false true 1) *
    φ (matrixSingle j false 1) = _
  have hs : ψ (matrixSingle false true (1:D)) =
      φ (matrixSingle false false 1) * ψ (matrixSingle false true 1) *
        φ (matrixSingle true true 1) := by
    rw [diag false,diag true,← map_mul,← map_mul,matrixSingle_mul,matrixSingle_mul,one_mul,one_mul]
  rw [hs]
  have hgroup : φ (matrixSingle false i 1) *
      (φ (matrixSingle false false 1) * ψ (matrixSingle false true 1) * φ (matrixSingle true true 1)) *
      φ (matrixSingle j false 1) =
    (φ (matrixSingle false i 1) * φ (matrixSingle false false 1)) * ψ (matrixSingle false true 1) *
      (φ (matrixSingle true true 1) * φ (matrixSingle j false 1)) := by simp only [mul_assoc]
  rw [hgroup,← map_mul,← map_mul]
  have hz₁ : matrixSingle false true (1:A) * matrixSingle false false 1 = 0 :=
    matrixSingle_mul_of_ne _ _ _ _ _ _ (by decide)
  have hz₂ : matrixSingle true true (1:A) * matrixSingle false false 1 = 0 :=
    matrixSingle_mul_of_ne _ _ _ _ _ _ (by decide)
  cases i <;> cases j <;> simp [hz₁,hz₂]
  change φ (matrixSingle false false 1) * ψ (matrixSingle false true 1) *
    φ (matrixSingle true false 1) = star (φ (matrixSingle false true 1) * ψ (matrixSingle true false 1))
  rw [diag false,← map_mul,matrixSingle_mul,one_mul]
  simp only [star_mul,← map_star,matrixSingle_star,star_one]

include diag in
theorem matrixCornerEntry_letter_true (i j : Bool) :
    matrixCornerEntry φ i j (bridgeLetter ψ true) =
      if j = false ∧ i = true then matrixStable φ ψ diag else 0 := by
  rw [show bridgeLetter ψ true = star (bridgeLetter ψ false) by
    simp, matrixCornerEntry_star,
    matrixCornerEntry_letter_false φ ψ diag j i]
  split_ifs <;> simp

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D]
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

include hd in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in

theorem matrixCorner_generators
    (hdense : Dense (Algebra.adjoin ℂ (Set.range φ ∪ Set.range ψ) : Set Z)) :
    Dense (StarAlgebra.adjoin ℂ
      (Set.range (matrixCornerBase φ) ∪ Set.range (matrixCornerLetter φ ψ diag)) :
        Set (MatrixHNNCorner φ)) := by
  let T := StarAlgebra.adjoin ℂ
    (Set.range (matrixCornerBase φ) ∪ Set.range (matrixCornerLetter φ ψ diag))
  let S := T.topologicalClosure
  have hbase (a : A) : matrixCornerBase φ a ∈ S :=
    T.le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨a,rfl⟩))
  have hletter (i : Bool) : matrixCornerLetter φ ψ diag i ∈ S :=
    T.le_topologicalClosure (StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨i,rfl⟩))
  rw [matrix_bridge_generators φ ψ δ hd] at hdense
  have hds : Dense (StarAlgebra.adjoin ℂ
      (Set.range φ ∪ Set.range (bridgeLetter ψ)) : Set Z) :=
    hdense.mono (Algebra.adjoin_le (StarAlgebra.subset_adjoin ℂ _))
  have htop : S = ⊤ := matrixCorner_generated_of_entries φ _ hds S
    T.isClosed_topologicalClosure (by
      rintro z (⟨M,rfl⟩ | ⟨k,rfl⟩) i j
      · rw [matrixCornerEntry_base]; exact hbase _
      · cases k
        · rw [matrixCornerEntry_letter_false φ ψ diag]
          split_ifs
          · exact hletter false
          · exact zero_mem S
        · rw [matrixCornerEntry_letter_true φ ψ diag]
          split_ifs
          · exact hletter true
          · exact zero_mem S)
  intro z
  change z ∈ S
  rw [htop]
  trivial

end

open scoped CStarAlgebra ComplexOrder
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B : PeakingPairData A)

theorem corner_generated :
    Dense (StarAlgebra.adjoin ℂ (Set.range B.cornerBase ∪ Set.range B.cornerLetter) : Set B.Corner) :=
  matrixCorner_generators B.embedBase B.embedAux _ B.diagonal B.model_diagonal_agree
    B.model_factors_dense

end PeakingPairData

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

section
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A]
variable (e : A) (he : IsStarProjection e)

theorem cornerTrace_isState (t : A →L[ℂ] ℂ) (ht : IsState t) (c : ℝ)
    (hc : 0 ≤ c) (hn : c • t e = 1) : IsState (cornerTrace e he t c) := by
  rw [isState_iff]
  refine ⟨hn, fun a => ?_⟩
  have ha := ht.2 (a : A)
  change (c • t (star (a : A)*(a : A))).im = 0 ∧ 0 ≤ (c • t (star (a : A)*(a : A))).re
  simp only [Complex.smul_im, Complex.smul_re, smul_eq_mul, ha.1, mul_zero]
  exact ⟨trivial, mul_nonneg hc ha.2⟩

theorem cornerTrace_faithful (t : A →L[ℂ] ℂ) (c : ℝ) (hc : c ≠ 0)
    (hf : ∀ a, t (star a*a)=0 → a=0) (a : CStarCorner e he)
    (ha : cornerTrace e he t c (star a*a)=0) : a=0 := by
  apply Subtype.ext
  apply hf
  exact (smul_eq_zero.mp ha).resolve_left hc

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
namespace PeakingPairData
attribute [local instance] matrixFamilyStarOrder modelPartialOrder modelStarOrderedRing
variable {A : Type} [instA : CStarAlgebra A] [orderA : PartialOrder A]
  [starOrderA : StarOrderedRing A] (B : PeakingPairData A)

instance hnnOrder : PartialOrder B.HNNAlgebra :=
  cornerPartialOrder (A := B.Model) (matrixCornerProjection B.embedBase)
    (matrixCornerProjection_isProjection B.embedBase)
instance hnnStarOrder : StarOrderedRing B.HNNAlgebra :=
  cornerStarOrderedRing (A := B.Model) (matrixCornerProjection B.embedBase)
    (matrixCornerProjection_isProjection B.embedBase)

end PeakingPairData

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (e : A) (he : IsStarProjection e)

omit [PartialOrder A] [StarOrderedRing A] in

theorem cornerRestrictState_isState (f : A →L[ℂ] ℂ) (hf : IsState f) (hfe : f e = 1) :
    IsState (cornerRestrictState e he f) := by
  rw [isState_iff]
  exact ⟨hfe,fun a => hf.2 (a:A)⟩

theorem cornerLift_restrict (f : A →L[ℂ] ℂ) (hf : IsState f) (hfe : f e = 1) :
    cornerLiftState e he (cornerRestrictState e he f) = f := by
  ext a
  exact state_compression f hf e (he.norm_le e) he.isSelfAdjoint hfe a

end

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C]
  {ι κ : Type*} [Preorder ι] [Preorder κ]
  [IsDirectedOrder ι] [IsDirectedOrder κ] [Nonempty ι] [Nonempty κ]

theorem bridge_cross_decay (φ : A →⋆ₐ[ℂ] C) (v : Bool → C) (K : A → Prop)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (x : ι → A) (y : κ → A) (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hy : ∀ j, 0 ≤ y j) (hyn : ∀ j, ‖y j‖ ≤ 1) (hym : Antitone y)
    (hexc : ∀ a, Tendsto (fun i => x i*(a-f a • (1:A))*x i) atTop (𝓝 0))
    (hey : ∀ a, Tendsto (fun j => y j*(a-g a • (1:A))*y j) atTop (𝓝 0))
    (hne : ¬ UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (hword : ∀ w : BridgeCore A, w.Centered K → ∀ a c : A,
      Tendsto (fun k : ι × κ => φ (x k.1)*φ a*w.eval φ v*φ c*φ (y k.2))
        atTop (𝓝 0)) :
    ∀ a ∈ bridgeWordSet φ v K,
      Tendsto (fun k : ι × κ => φ (x k.1)*a*φ (y k.2)) atTop (𝓝 0) := by
  let : (atTop : Filter (ι × κ)).NeBot := by
    rw [← prod_atTop_atTop_eq]
    infer_instance
  intro a ha
  rcases ha with (⟨a,rfl⟩ | ⟨w,a,c,hw,rfl⟩)
  · exact map_cross_decay φ _ _ a
      (state_cross_excision f g hf hg x y hx hxn hy hyn hym hexc hey hne a)
  · simpa only [mul_assoc] using hword w hw a c

end

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

def hnnUnitary : unitary B.HNNAlgebra := B.stableUnitary

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
section
variable {A C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem pure_lifts_equivalent (φ : A →⋆ₐ[ℂ] C)
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (he : UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (hu : StateExtensionUnique φ g)
    (F G : C →L[ℂ] ℂ) (hF : IsPureState F) (hG : IsPureState G)
    (hrF : restrictState φ F = f) (hrG : restrictState φ G = g) :
    UnitarilyEquivalent (pureGNS F hF) (pureGNS G hG) := by
  obtain ⟨u,huconj⟩ := pureState_equivalent_conjugate f g hf hg he
  let v : unitary C := ⟨φ (u:A),by
    constructor
    · rw [← map_star,← map_mul,u.property.1,map_one]
    · rw [← map_star,← map_mul,u.property.2,map_one]⟩
  let H := restrictState (Unitary.conjStarAlgAut ℂ C v).symm.toStarAlgHom F
  have hH : IsState H := isState_restrict _ _ hF.1
  have hrH : restrictState φ H = g := by
    ext a
    change F (star (φ (u:A))*φ a*φ (u:A)) = g a
    rw [← map_star,← map_mul,← map_mul]
    change restrictState φ F (star (u:A)*a*(u:A)) = g a
    rw [hrF]
    exact (congrArg (fun k : A →L[ℂ] ℂ => k a) huconj).symm
  have hh := hu H G hH hG.1 hrH hrG
  apply pureState_equivalent_of_conjugate F G hF hG v
  intro a
  exact (congrArg (fun k : C →L[ℂ] ℂ => k a) hh).symm

end

open Topology

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in

theorem pureExcisionNet_value
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1)
    (ξ : H) (hξ : ‖ξ‖ = 1) (i : ExcisionIndex (vectorNullAlgebra π ξ)) :
    ⟪ξ,π (pureExcisionNet π ξ i) ξ⟫_ℂ = 1 := by
  rw [pureExcisionNet_fixes π hone ξ i,inner_self_eq_norm_sq_to_K,hξ]
  norm_num

theorem inequivalent_pure_mixed_zero
    (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g)
    (hne : ¬ PureStateEquivalent f hf g hg)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hcξ : ∀ a, ⟪ξ,π a ξ⟫_ℂ = f a) (hcη : ∀ a, ⟪η,π a η⟫_ℂ = g a)
    (a : A) : ⟪ξ,π a η⟫_ℂ = 0 := by
  let F := positiveOfSquares f hf.1.2
  let G := positiveOfSquares g hg.1.2
  let ζ := gnsVector F
  let ν := gnsVector G
  let x := pureExcisionNet F.gnsNonUnitalStarAlgHom ζ
  let y := pureExcisionNet G.gnsNonUnitalStarAlgHom ν
  have hxv (i) : f (x i) = 1 :=
    (gnsVector_coefficient F _).symm.trans
      (pureExcisionNet_value _ (irreducible_map_one _ (pure_gns_irreducible f hf.1 hf)) ζ
        (gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1) i)
  have hyv (i) : g (y i) = 1 :=
    (gnsVector_coefficient G _).symm.trans
      (pureExcisionNet_value _ (irreducible_map_one _ (pure_gns_irreducible g hg.1 hg)) ν
        (gnsVector_norm_eq_one G ((isState_iff g).mp hg.1).1) i)
  let : (atTop : Filter (ExcisionIndex (vectorNullAlgebra F.gnsNonUnitalStarAlgHom ζ) ×
      ExcisionIndex (vectorNullAlgebra G.gnsNonUnitalStarAlgHom ν))).NeBot := by
    rw [← Filter.prod_atTop_atTop_eq]
    infer_instance
  apply mixed_zero_of_state_cross_decay f g (fun ij : ExcisionIndex (vectorNullAlgebra F.gnsNonUnitalStarAlgHom ζ) ×
      ExcisionIndex (vectorNullAlgebra G.gnsNonUnitalStarAlgHom ν) => x ij.1) (fun ij => y ij.2)
      (l := (atTop : Filter (ExcisionIndex (vectorNullAlgebra F.gnsNonUnitalStarAlgHom ζ) ×
        ExcisionIndex (vectorNullAlgebra G.gnsNonUnitalStarAlgHom ν))))
      (fun ij => IsSelfAdjoint.of_nonneg (pureExcisionNet_nonneg _ _ ij.1))
      (fun ij => pureExcisionNet_norm _ _ ij.1)
      (fun ij => pureExcisionNet_norm _ _ ij.2)
      (fun ij => hxv ij.1)
      (fun ij => hyv ij.2) π ξ η hξ hη hcξ hcη a
  exact pureExcisionNet_cross _ (pure_gns_irreducible f hf.1 hf) ζ
    (gnsVector_norm_eq_one F ((isState_iff f).mp hf.1).1)
    _ (pure_gns_irreducible g hg.1 hg) ν
    (gnsVector_norm_eq_one G ((isState_iff g).mp hg.1).1) hne a

end

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
namespace PeakingPairData
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (B Q : PeakingPairData A)

def pairHNN : Bool → Type := fun i => if i then Q.HNNAlgebra else B.HNNAlgebra
instance pairHNN_cstar (i : Bool) : CStarAlgebra (pairHNN B Q i) := by
  cases i <;> dsimp [pairHNN] <;> infer_instance

def pairHNNBase : ∀ i, A →⋆ₐ[ℂ] pairHNN B Q i
  | false => B.hnnBase
  | true => Q.hnnBase

variable (D : PeakingPairData B.HNNAlgebra) (E : PeakingPairData Q.HNNAlgebra)
  (jQ : Q.HNNAlgebra →⋆ₐ[ℂ] D.HNNAlgebra) (jB : B.HNNAlgebra →⋆ₐ[ℂ] E.HNNAlgebra)

def leftHNNFamily : ∀ i, pairHNN B Q i →⋆ₐ[ℂ] D.HNNAlgebra
  | false => D.hnnBase
  | true => jQ

def rightHNNFamily : ∀ i, pairHNN B Q i →⋆ₐ[ℂ] E.HNNAlgebra
  | false => jB
  | true => E.hnnBase

theorem leftHNNFamily_base (ha : ∀ a, jQ (Q.hnnBase a) = D.hnnBase (B.hnnBase a)) (i : Bool) :
    (leftHNNFamily B Q D jQ i).toAlgHom.comp (pairHNNBase B Q i).toAlgHom =
      (D.hnnBase.comp B.hnnBase).toAlgHom := by
  cases i
  · rfl
  · ext a; exact ha a

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

theorem carInclude_isometry (n : ℕ) : Isometry (carInclude n) :=
  cstarDirectLimitInclude_isometry CARStage carBond n

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end


