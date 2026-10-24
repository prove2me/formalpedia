-- Prove2me | Definitions.Def_OAIQWCMM000
-- name    : OAIQWCMM000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T22:11:35.219079+00:00
-- url     : https://prove2.me/theorems/8a433d2a-ec8a-4fff-9857-49b057fbde7c
-- title:
--   OpenAI uniform property Gamma split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that real rank zero of the uniform tracial ultrapower implies uniform property $\Gamma$ (`OAI.ComparatorModel.CurrentMain.main`, the paper's Theorem 1.1, answering Problem XXI of Schafhauser, Tikuisis and White). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/TracialSplitting` (OpenAI, *Tracial projection methods and uniform property Gamma*, OpenAI Math Release, September 23, 2026, result family 291, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. Among them are the uniform trace norms (`uniformTwoNorm`, `uniformHalvingError`, `traceOneNorm`), full projections (`IsFull`), bistochastic tests (`BistochasticTest`), projection rows and weighted block families (`ProjectionRow`, `WeightedBlockFamily`), and the packing data of the splitting argument.
--
--   The definitions of the published statement (`TracialState`, `IsNuclear`, `RealRankZero`, `traceTwoNorm`, `familyTwoNorm`, `UniformTracialCompletion`, `FamilyUltrapower`, `UniformPropertyGammaAt`, `Statement`, `MainClaim` and the rest) are not repeated: the bundle imports them from the published bundle `Def_UniformGamma`. It imports no other bundle of this split.
--
--   Modules (some only in part): `BistochasticTests`, `Challenge`, `CoefficientApproximation`, `CoefficientBounds`, `Completion`, `FaithfulRepresentations`, `FinitePacking`, `FullProjections`, `GNSRepresentations`, `KrausApproximation`, `MatrixCoefficients`, `MatrixNormalization`, `Model`, `NuclearTransfer`, `OrthogonalElements`, `OrthogonalPacking`, `PackingEstimates`, `PartitionCoupling`, `PreparedBlocks`, `ProjectionFrames`, `ProjectionRounding`, `ProjectionSampling`, `RowEstimates`, `ScalarCompression`, `SimpleIdeals`, `SpatialTensor`, `SpectralBlocks`, `SpectralCutoffs`, `SpectralLayers`, `StateExtension`, `TensorExtension`, `TensorNorms`, `TraceConvexity`, `TraceEstimates`, `TraceNormalization`, `VectorApproximation`, `WeightedFamilies`.
--
--   The theorems the definitions do not need are proved in the three solutions of this split. One proves the published intermediate statement `OAI.CurrentMain.nuclear_prepared_row_blocks` (the paper's Proposition 4.3), one proves `OAI.CurrentMain.finite_set_central_splitting` (Theorem 1.3) from it, and the third proves `OAI.ComparatorModel.CurrentMain.main` from that. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Tracial projection methods and uniform property Gamma, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 291; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Tracial-projection-methods-and-uniform-property-Gamma-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/TracialSplitting at commit adc7f12

import Mathlib
import Definitions.Def_UniformGamma

section
-- module Solutions.OAIQW_TracialSplitting.Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD uE uI uR uX

section

namespace Pureness

open scoped TensorProduct ComplexOrder

universe u v

def IsNuclear (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (B : Type v) [CStarAlgebra B], Subsingleton (CStarAlgebraNorm (A ⊗[ℂ] B))

end Pureness

namespace CurrentMain

section

open Pureness

open scoped ComplexOrder

def RealRankZero (D : Type uD) [CStarAlgebra D] : Prop :=
  ∀ a : D, IsSelfAdjoint a → ∀ ε : ℝ, 0 < ε →
    ∃ b : D, IsSelfAdjoint b ∧ (spectrum ℂ b).Finite ∧ ‖a - b‖ < ε

def traceTwoNorm {D : Type uD} [CStarAlgebra D] [PartialOrder D]
    (τ : TracialState D) (a : D) : ℝ :=
  Real.sqrt (τ.functional (star a * a)).re

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_eq_gns (τ : TracialState D) (a : D) :
    traceTwoNorm τ a = ‖τ.functional.toPreGNS a‖ := rfl

omit [StarOrderedRing D] in

lemma traceTwoNorm_nonneg (τ : TracialState D) (a : D) :
    0 ≤ traceTwoNorm τ a := Real.sqrt_nonneg _

omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_zero (τ : TracialState D) : traceTwoNorm τ 0 = 0 := by
  simp [traceTwoNorm]

omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_one (τ : TracialState D) : traceTwoNorm τ 1 = 1 := by
  simp [traceTwoNorm, τ.normalized]

lemma traceTwoNorm_add_le (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (a + b) ≤ traceTwoNorm τ a + traceTwoNorm τ b := by
  simpa only [traceTwoNorm_eq_gns, map_add] using
    norm_add_le (τ.functional.toPreGNS a) (τ.functional.toPreGNS b)

omit [StarOrderedRing D] in

@[simp] lemma traceTwoNorm_star (τ : TracialState D) (a : D) :
    traceTwoNorm τ (star a) = traceTwoNorm τ a := by
  simp only [traceTwoNorm, star_star, τ.tracial a (star a)]

lemma traceTwoNorm_mul_left (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (a * b) ≤ ‖a‖ * traceTwoNorm τ b := by
  let f := τ.functional
  have hop : ‖f.leftMulMapPreGNS a‖ ≤ ‖a‖ := by
    unfold PositiveLinearMap.leftMulMapPreGNS
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  calc
    traceTwoNorm τ (a * b) = ‖f.leftMulMapPreGNS a (f.toPreGNS b)‖ := rfl
    _ ≤ ‖f.leftMulMapPreGNS a‖ * ‖f.toPreGNS b‖ := (f.leftMulMapPreGNS a).le_opNorm _
    _ ≤ ‖a‖ * traceTwoNorm τ b := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

lemma traceTwoNorm_mul_right (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (b * a) ≤ ‖a‖ * traceTwoNorm τ b := by
  calc
    traceTwoNorm τ (b * a) = traceTwoNorm τ (star a * star b) := by
      rw [← star_mul, traceTwoNorm_star]
    _ ≤ ‖star a‖ * traceTwoNorm τ (star b) := traceTwoNorm_mul_left τ _ _
    _ = ‖a‖ * traceTwoNorm τ b := by rw [norm_star, traceTwoNorm_star]

lemma traceTwoNorm_le_norm (τ : TracialState D) (a : D) :
    traceTwoNorm τ a ≤ ‖a‖ := by
  simpa only [mul_one, traceTwoNorm_one] using traceTwoNorm_mul_left τ a 1

lemma trace_norm_le_twoNorm (τ : TracialState D) (a : D) :
    ‖τ.functional a‖ ≤ traceTwoNorm τ a := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (τ.functional.toPreGNS 1)
    (τ.functional.toPreGNS a)
  have hone : ‖τ.functional.toPreGNS 1‖ = 1 := traceTwoNorm_one τ
  simpa only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, hone,
    ← traceTwoNorm_eq_gns] using h

lemma trace_norm_le_norm (τ : TracialState D) (a : D) :
    ‖τ.functional a‖ ≤ ‖a‖ :=
  (trace_norm_le_twoNorm τ a).trans (traceTwoNorm_le_norm τ a)

end

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_neg (τ : Pureness.TracialState D) (a : D) :
    traceTwoNorm τ (-a) = traceTwoNorm τ a := by
  simp only [traceTwoNorm_eq_gns, map_neg, norm_neg]

end CurrentMain

namespace Pureness

open Filter

open scoped Topology NNReal ENNReal

namespace ClosedStarIdeal

variable {D : Type uD} [CStarAlgebra D] (J : ClosedStarIdeal D)

abbrev Quotient := J.ideal.ringCon.Quotient

def quotientMap : D →ₐ[ℂ] J.Quotient := J.ideal.ringCon.mkₐ ℂ

lemma quotientMap_surjective : Function.Surjective J.quotientMap :=
  J.ideal.ringCon.mkₐ_surjective (α := ℂ)

lemma rel_star (u v : D) (h : J.ideal.ringCon u v) :
    J.ideal.ringCon (star u) (star v) := by
  rw [TwoSidedIdeal.rel_iff] at h ⊢
  simpa only [star_sub] using J.star_mem h

instance quotientStar : Star (J.Quotient) where
  star := Quotient.map' star (J.rel_star)

lemma quotientMap_star (u : D) :
    J.quotientMap (star u) = star (J.quotientMap u) := rfl

instance quotientStarRing : StarRing (J.Quotient) where
  star_involutive x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← J.quotientMap_star,← J.quotientMap_star,star_star]
  star_mul x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_mul,← J.quotientMap_star,star_mul,map_mul,
      J.quotientMap_star,J.quotientMap_star]
  star_add x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_add,← J.quotientMap_star,star_add,map_add,
      J.quotientMap_star,J.quotientMap_star]

instance quotientStarModule : StarModule ℂ (J.Quotient) where
  star_smul c x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← _root_.map_smul,← J.quotientMap_star,star_smul,_root_.map_smul,J.quotientMap_star]

abbrev idealSubmodule : Submodule ℂ (D) :=
  (J.quotientMap).toLinearMap.ker

lemma idealSubmodule_coe :
    (J.idealSubmodule : Set (D)) =
      (J.ideal : Set (D)) := by
  ext u
  change J.quotientMap u = 0 ↔ u ∈ J.ideal
  change (J.ideal).ringCon.mk' u = (J.ideal).ringCon.mk' 0 ↔ _
  exact Quotient.eq

instance idealSubmodule_closed : IsClosed (J.idealSubmodule : Set (D)) := by
  rw [J.idealSubmodule_coe]
  exact J.isClosed

def quotientLinearEquiv :
    (D ⧸ J.idealSubmodule) ≃ₗ[ℂ] J.Quotient :=
  (J.quotientMap).toLinearMap.quotKerEquivOfSurjective (J.quotientMap_surjective)

lemma quotientLinearEquiv_mk (u : D) :
    J.quotientLinearEquiv (Submodule.Quotient.mk u) = J.quotientMap u := rfl

instance quotientNormedAddCommGroup : NormedAddCommGroup (J.Quotient) :=
  NormedAddCommGroup.induced _ _ (J.quotientLinearEquiv).symm
    (J.quotientLinearEquiv).symm.injective

instance quotientNormedSpace : NormedSpace ℂ (J.Quotient) :=
  NormedSpace.induced ℂ _ _ (J.quotientLinearEquiv).symm

def quotientNormEquiv : J.Quotient ≃ₗᵢ[ℂ]
    (D ⧸ J.idealSubmodule) where
  __ := (J.quotientLinearEquiv).symm
  norm_map' _ := rfl

lemma quotientMap_norm_le (u : D) :
    ‖J.quotientMap u‖ ≤ ‖u‖ := by
  change ‖(J.quotientLinearEquiv).symm (J.quotientMap u)‖ ≤ ‖u‖
  rw [← J.quotientLinearEquiv_mk, LinearEquiv.symm_apply_apply]
  exact Submodule.Quotient.norm_mk_le _ u

lemma quotient_norm_lt_rep (x : J.Quotient) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : D, J.quotientMap u = x ∧ ‖u‖ < ‖x‖+ε := by
  obtain ⟨u,hu,hun⟩ := Submodule.Quotient.norm_mk_lt ((J.quotientLinearEquiv).symm x) hε
  refine ⟨u,?_,hun⟩
  apply (J.quotientLinearEquiv).symm.injective
  rw [← J.quotientLinearEquiv_mk,LinearEquiv.symm_apply_apply,hu]

instance quotientCompleteSpace : CompleteSpace (J.Quotient) :=
  (J.quotientNormEquiv).toIsometryEquiv.completeSpace_iff.mpr inferInstance

lemma quotient_norm_mul_le (x y : J.Quotient) : ‖x*y‖ ≤ ‖x‖*‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc := ((Metric.nhds_basis_ball.prod_nhds Metric.nhds_basis_ball).tendsto_iff
    Metric.nhds_basis_ball).mp (continuous_mul.tendsto (‖x‖,‖y‖)) ε hε
  simp only [Set.mem_prod,Metric.mem_ball,and_imp,Prod.forall,Prod.exists] at hc
  obtain ⟨δ,η,⟨hδ,hη⟩,h⟩ := hc
  obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep x hδ
  obtain ⟨v,rfl,hv⟩ := J.quotient_norm_lt_rep y hη
  simp only [Real.dist_eq,abs_sub_lt_iff] at h
  specialize h ‖u‖ ‖v‖ ⟨by linarith,by linarith [J.quotientMap_norm_le u]⟩
    ⟨by linarith,by linarith [J.quotientMap_norm_le v]⟩
  calc
    _ = ‖J.quotientMap (u*v)‖ := by rw [map_mul]
    _ ≤ ‖u*v‖ := J.quotientMap_norm_le _
    _ ≤ ‖u‖*‖v‖ := norm_mul_le _ _
    _ ≤ _ := by linarith [h.2]

instance quotientNormedRing : NormedRing (J.Quotient) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := J.quotient_norm_mul_le

instance quotientNormedAlgebra : NormedAlgebra ℂ (J.Quotient) where
  norm_smul_le := norm_smul_le

lemma quotient_norm_star (x : J.Quotient) : ‖star x‖ = ‖x‖ := by
  have hle (y : J.Quotient) : ‖star y‖ ≤ ‖y‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨u,rfl,hu⟩ := J.quotient_norm_lt_rep y hε
    rw [← J.quotientMap_star]
    exact (J.quotientMap_norm_le (star u)).trans (by simpa only [norm_star] using hu.le)
  exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

instance quotientNormedStarGroup : NormedStarGroup (J.Quotient) where
  norm_star_le x := (J.quotient_norm_star x).le

end ClosedStarIdeal

end Pureness

namespace Pureness.ClosedStarIdeal

open Filter

open scoped Topology NNReal ENNReal

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (J : ClosedStarIdeal D)

def idealStarAlgebra : NonUnitalStarSubalgebra ℂ (D) where
  carrier := J.ideal
  zero_mem' := (J.ideal).zero_mem
  add_mem' := (J.ideal).add_mem
  mul_mem' {u v} _ hv := (J.ideal).mul_mem_left u v hv
  smul_mem' c u hu := by
    change c • u ∈ J.ideal
    rw [Algebra.smul_def]
    exact (J.ideal).mul_mem_left (algebraMap ℂ _ c) u hu
  star_mem' := J.star_mem

instance idealStarAlgebraCompleteSpace : CompleteSpace (J.idealStarAlgebra) :=
  (J.isClosed).completeSpace_coe

instance idealStarAlgebraCStar : NonUnitalCStarAlgebra (J.idealStarAlgebra) where
  norm_mul_self_le u := CStarRing.norm_mul_self_le u.1

instance idealPartialOrder : PartialOrder (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrder _

instance idealStarOrderedRing : StarOrderedRing (J.idealStarAlgebra) :=
  CStarAlgebra.spectralOrderedRing _

local instance instLESubtypeMemNonUnitalStarSubalgebraComplexIdealStarAlgebra : LE (J.idealStarAlgebra) := (J.idealPartialOrder).toLE

local instance instPreorderSubtypeMemNonUnitalStarSubalgebraComplexIdealStarAlgebra_rb5fe56_1 : Preorder (J.idealStarAlgebra) := (J.idealPartialOrder).toPreorder
lemma idealInclusion_nonneg {e : J.idealStarAlgebra} (he : 0 ≤ e) :
    0 ≤ (e : D) :=
  by
    have hs : star (CFC.sqrt e)*CFC.sqrt e = e := by
      rw [(CFC.sqrt_nonneg e).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self e he]
    have hs' := congrArg Subtype.val hs
    rw [← hs']
    exact star_mul_self_nonneg _

lemma norm_one_sub {e : D} (he : 0 ≤ e) (hn : ‖e‖ ≤ 1) :
    ‖1-e‖ ≤ 1 := by
  have he1 : e ≤ 1 := by
    simpa using (CStarAlgebra.norm_le_iff_le_algebraMap e (by norm_num : (0:ℝ) ≤ 1) he).mp hn
  rw [CStarAlgebra.norm_le_iff_le_algebraMap (1-e) (by norm_num : (0:ℝ) ≤ 1) (sub_nonneg.mpr he1)]
  simpa using sub_le_self (1 : D) he

lemma exists_ideal_contraction {w : D} (hw : w ∈ J.ideal)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, e ∈ J.ideal ∧ IsSelfAdjoint e ∧
      ‖1-e‖ ≤ 1 ∧ ‖w*(1-e)‖ < ε := by
  let W : J.idealStarAlgebra := ⟨w,hw⟩
  have hl := CStarAlgebra.increasingApproximateUnit (J.idealStarAlgebra)
  have ht := hl.tendsto_mul_left W
  have heps := (Metric.tendsto_nhds.mp ht) ε hε
  obtain ⟨e,hp,hn,hm⟩ := (hl.eventually_nonneg.and (hl.eventually_norm.and heps)).exists
  refine ⟨e.1,e.2,?_,norm_one_sub (J.idealInclusion_nonneg hp) hn,?_⟩
  · exact congrArg Subtype.val hp.isSelfAdjoint
  · change dist (W*e) W < ε at hm
    rw [dist_eq_norm] at hm
    change ‖w*e.1-w‖ < ε at hm
    simpa only [mul_sub,mul_one,← neg_sub (w*e.1) w,norm_neg] using hm

lemma quotient_norm_square_le (x : J.Quotient) :
    ‖x‖*‖x‖ ≤ ‖star x*x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
  obtain ⟨v,hv,hvn⟩ := J.quotient_norm_lt_rep
    (star (J.quotientMap u)*J.quotientMap u) (half_pos hε)
  let w := star u*u-v
  have hw : w ∈ J.ideal := by
    change (J.ideal).ringCon w 0
    apply Quotient.exact
    change J.quotientMap w = J.quotientMap 0
    simp only [w,map_sub,map_mul,J.quotientMap_star,hv,sub_self]
    exact (_root_.map_zero (J.quotientMap)).symm
  obtain ⟨e,he,hestar,hen,hwe⟩ := J.exists_ideal_contraction hw (half_pos hε)
  have heq : J.quotientMap e = 0 := Quotient.sound he
  have hmap : J.quotientMap (u*(1-e)) = J.quotientMap u := by
    simp [map_mul,map_sub,heq]
  have hun := J.quotientMap_norm_le (u*(1-e))
  rw [hmap] at hun
  have hidentity : star (u*(1-e))*(u*(1-e)) =
      (1-e)*v*(1-e)+(1-e)*(w*(1-e)) := by
    simp only [star_mul,star_sub,star_one,hestar.star_eq,w]
    noncomm_ring
  have hterm1 : ‖(1-e)*v*(1-e)‖ ≤ ‖v‖ := by
    calc
      _ ≤ ‖1-e‖*‖v‖*‖1-e‖ := (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖v‖*1 := by gcongr
      _ = ‖v‖ := by ring
  have hterm2 : ‖(1-e)*(w*(1-e))‖ < ε/2 := by
    calc
      _ ≤ ‖1-e‖*‖w*(1-e)‖ := norm_mul_le _ _
      _ ≤ 1*‖w*(1-e)‖ := by gcongr
      _ < ε/2 := by simpa using hwe
  calc
    _ ≤ ‖u*(1-e)‖*‖u*(1-e)‖ := mul_self_le_mul_self (norm_nonneg _) hun
    _ = ‖star (u*(1-e))*(u*(1-e))‖ := (CStarRing.norm_star_mul_self (x := u*(1-e))).symm
    _ ≤ ‖(1-e)*v*(1-e)‖+‖(1-e)*(w*(1-e))‖ := by rw [hidentity]; exact norm_add_le _ _
    _ ≤ ‖star (J.quotientMap u)*J.quotientMap u‖+ε := by linarith

instance quotientCStarAlgebra : CStarAlgebra (J.Quotient) where
  norm_mul_self_le := J.quotient_norm_square_le

end Pureness.ClosedStarIdeal

namespace CurrentMain

section

open Pureness

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def familyTwoNorm (a : D) : ℝ := ⨆ i, traceTwoNorm (τ i) a

omit [Nonempty I] in

lemma familyTwoNorm_bdd (a : D) : BddAbove (Set.range (fun i => traceTwoNorm (τ i) a)) :=
  ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact traceTwoNorm_le_norm (τ i) a⟩

omit [Nonempty I] in

lemma traceTwoNorm_le_family (i : I) (a : D) :
    traceTwoNorm (τ i) a ≤ familyTwoNorm τ a :=
  le_ciSup (familyTwoNorm_bdd τ a) i

lemma familyTwoNorm_nonneg (a : D) : 0 ≤ familyTwoNorm τ a := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (traceTwoNorm_nonneg (τ i) a).trans (traceTwoNorm_le_family τ i a)

lemma familyTwoNorm_le_norm (a : D) : familyTwoNorm τ a ≤ ‖a‖ :=
  ciSup_le (fun i => traceTwoNorm_le_norm (τ i) a)

@[simp] lemma familyTwoNorm_zero : familyTwoNorm τ 0 = 0 := by
  apply le_antisymm _ (familyTwoNorm_nonneg τ 0)
  simpa only [norm_zero] using familyTwoNorm_le_norm τ 0

lemma familyTwoNorm_add_le (a b : D) :
    familyTwoNorm τ (a + b) ≤ familyTwoNorm τ a + familyTwoNorm τ b := by
  apply ciSup_le
  intro i
  exact (traceTwoNorm_add_le (τ i) a b).trans
    (add_le_add (traceTwoNorm_le_family τ i a) (traceTwoNorm_le_family τ i b))

omit [Nonempty I] in

@[simp] lemma familyTwoNorm_neg (a : D) : familyTwoNorm τ (-a) = familyTwoNorm τ a := by
  simp only [familyTwoNorm, traceTwoNorm_neg]

omit [Nonempty I] in

lemma familyTwoNorm_sub_swap (a b : D) : familyTwoNorm τ (a - b) = familyTwoNorm τ (b - a) := by
  rw [← neg_sub b a, familyTwoNorm_neg]

lemma familyTwoNorm_sub_triangle (a b c : D) :
    familyTwoNorm τ (a - c) ≤ familyTwoNorm τ (a - b) + familyTwoNorm τ (b - c) := by
  convert familyTwoNorm_add_le τ (a - b) (b - c) using 1
  abel_nf

omit [StarOrderedRing D] [Nonempty I] in

@[simp] lemma familyTwoNorm_star (a : D) : familyTwoNorm τ (star a) = familyTwoNorm τ a := by
  simp only [familyTwoNorm, traceTwoNorm_star]

lemma familyTwoNorm_mul_left (a b : D) :
    familyTwoNorm τ (a * b) ≤ ‖a‖ * familyTwoNorm τ b := by
  apply ciSup_le
  intro i
  exact (traceTwoNorm_mul_left (τ i) a b).trans
    (mul_le_mul_of_nonneg_left (traceTwoNorm_le_family τ i b) (norm_nonneg _))

lemma familyTwoNorm_mul_right (a b : D) :
    familyTwoNorm τ (a * b) ≤ familyTwoNorm τ a * ‖b‖ := by
  apply ciSup_le
  intro i
  simpa only [mul_comm] using (traceTwoNorm_mul_right (τ i) b a).trans
    (mul_le_mul_of_nonneg_left (traceTwoNorm_le_family τ i a) (norm_nonneg _))

end

open Pureness Filter

open scoped Topology NNReal ENNReal

instance boundedFamilyProductCStar {X : Type uX} {D : Type uD} [CStarAlgebra D] [Nontrivial D] :
    CStarAlgebra (lp (fun _ : X => D) ∞) where

section UniformNull

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def IsFamilyNull (F : Filter X) (u : X → D) : Prop :=
  Tendsto (fun n => familyTwoNorm τ (u n)) F (𝓝 0)

lemma isFamilyNull_iff (F : Filter X) (u : X → D) :
    IsFamilyNull τ F u ↔ ∀ ε > 0, ∀ᶠ n in F, familyTwoNorm τ (u n) < ε := by
  simp only [IsFamilyNull, Metric.tendsto_nhds, Real.dist_eq, sub_zero,
    abs_of_nonneg (familyTwoNorm_nonneg τ _)]

lemma isFamilyNull_zero (F : Filter X) : IsFamilyNull τ F (fun _ => 0) := by
  simp only [IsFamilyNull, familyTwoNorm_zero]
  exact tendsto_const_nhds

lemma isFamilyNull_add {F : Filter X} {u v : X → D}
    (hu : IsFamilyNull τ F u) (hv : IsFamilyNull τ F v) :
    IsFamilyNull τ F (fun n => u n + v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _)
    (fun n => familyTwoNorm_add_le τ _ _)
  simpa only [add_zero] using hu.add hv

omit [Nonempty I] in

lemma isFamilyNull_neg {F : Filter X} {u : X → D}
    (hu : IsFamilyNull τ F u) : IsFamilyNull τ F (fun n => -u n) := by
  simpa only [IsFamilyNull, familyTwoNorm_neg] using hu

omit [StarOrderedRing D] [Nonempty I] in

lemma isFamilyNull_star {F : Filter X} {u : X → D}
    (hu : IsFamilyNull τ F u) : IsFamilyNull τ F (fun n => star (u n)) := by
  simpa only [IsFamilyNull, familyTwoNorm_star] using hu

lemma isFamilyNull_mul_left {F : Filter X} {u v : X → D}
    (hv : IsFamilyNull τ F v) {M : ℝ} (hu : ∀ n, ‖u n‖ ≤ M) :
    IsFamilyNull τ F (fun n => u n * v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _) (fun n =>
    (familyTwoNorm_mul_left τ _ _).trans
      (mul_le_mul_of_nonneg_right (hu n) (familyTwoNorm_nonneg τ _)))
  simpa only [mul_zero] using hv.const_mul M

lemma isFamilyNull_mul_right {F : Filter X} {u v : X → D}
    (hu : IsFamilyNull τ F u) {M : ℝ} (hv : ∀ n, ‖v n‖ ≤ M) :
    IsFamilyNull τ F (fun n => u n * v n) := by
  apply squeeze_zero (fun n => familyTwoNorm_nonneg τ _) (fun n =>
    (familyTwoNorm_mul_right τ _ _).trans
      (mul_le_mul_of_nonneg_left (hv n) (familyTwoNorm_nonneg τ _)))
  simpa only [zero_mul] using hu.mul_const M

lemma familyNull_isClosed (F : Filter X) :
    IsClosed {u : lp (fun _ : X => D) ∞ | IsFamilyNull τ F (fun n => u n)} := by
  apply isClosed_of_closure_subset
  intro u hu
  change IsFamilyNull τ F (fun n => u n)
  rw [isFamilyNull_iff]
  intro ε hε
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu (ε/2) (by linarith)
  have hnear (n : X) : familyTwoNorm τ (u n-v n) < ε/2 :=
    (familyTwoNorm_le_norm τ _).trans_lt
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) n).trans_lt
        (by simpa only [dist_eq_norm] using huv))
  have he := (isFamilyNull_iff τ F _).mp hv (ε/2) (by linarith)
  filter_upwards [he] with n hn
  have ht := familyTwoNorm_add_le τ (u n-v n) (v n)
  rw [sub_add_cancel] at ht
  linarith [hnear n]

variable [Nontrivial D]

def familyNullTwoSided (F : Filter X) : TwoSidedIdeal (lp (fun _ : X => D) ∞) :=
  TwoSidedIdeal.mk' {u | IsFamilyNull τ F (fun n => u n)}
    (isFamilyNull_zero τ F)
    (fun hu hv => isFamilyNull_add τ hu hv)
    (fun hu => isFamilyNull_neg τ hu)
    (fun {u _} hv => isFamilyNull_mul_left τ hv
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u))
    (fun {_ v} hu => isFamilyNull_mul_right τ hu
      (lp.norm_apply_le_norm ENNReal.top_ne_zero v))

lemma familyNull_mem (F : Filter X) (u : lp (fun _ : X => D) ∞) :
    u ∈ familyNullTwoSided τ F ↔ IsFamilyNull τ F (fun n => u n) := by
  unfold familyNullTwoSided
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u

lemma familyNull_star (F : Filter X) {u : lp (fun _ : X => D) ∞}
    (hu : u ∈ familyNullTwoSided τ F) : star u ∈ familyNullTwoSided τ F := by
  apply (familyNull_mem τ F (star u)).mpr
  exact isFamilyNull_star τ ((familyNull_mem τ F u).mp hu)

def familyNullIdeal (F : Filter X) : ClosedStarIdeal (lp (fun _ : X => D) ∞) where
  ideal := familyNullTwoSided τ F
  star_mem := familyNull_star τ F
  isClosed := by
    have he : (familyNullTwoSided τ F : Set (lp (fun _ : X => D) ∞)) = {u | IsFamilyNull τ F (fun n => u n)} :=
      Set.ext (familyNull_mem τ F)
    rw [he]
    exact familyNull_isClosed τ F

end UniformNull

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def IsFamilyCauchy (u : ℕ → D) : Prop :=
  IsFamilyNull τ (atTop : Filter (ℕ × ℕ)) (fun p => u p.1 - u p.2)

lemma isFamilyCauchy_const (a : D) : IsFamilyCauchy τ (fun _ => a) := by
  simpa only [IsFamilyCauchy, sub_self] using
    isFamilyNull_zero τ (atTop : Filter (ℕ × ℕ))

lemma isFamilyCauchy_add {u v : ℕ → D} (hu : IsFamilyCauchy τ u)
    (hv : IsFamilyCauchy τ v) : IsFamilyCauchy τ (fun n => u n+v n) := by
  simpa only [IsFamilyCauchy, add_sub_add_comm] using isFamilyNull_add τ hu hv

omit [StarOrderedRing D] [Nonempty I] in

lemma isFamilyCauchy_star {u : ℕ → D} (hu : IsFamilyCauchy τ u) :
    IsFamilyCauchy τ (fun n => star (u n)) := by
  simpa only [IsFamilyCauchy, star_sub] using isFamilyNull_star τ hu

lemma isFamilyCauchy_mul {u v : ℕ → D} (hu : IsFamilyCauchy τ u)
    (hv : IsFamilyCauchy τ v) {M N : ℝ} (hM : ∀ n, ‖u n‖ ≤ M)
    (hN : ∀ n, ‖v n‖ ≤ N) : IsFamilyCauchy τ (fun n => u n*v n) := by
  have h₁ := isFamilyNull_mul_left τ hv (fun p : ℕ × ℕ => hM p.1)
  have h₂ := isFamilyNull_mul_right τ hu (fun p : ℕ × ℕ => hN p.2)
  have he (p : ℕ × ℕ) : u p.1 * (v p.1-v p.2) + (u p.1-u p.2)*v p.2 =
      u p.1*v p.1-u p.2*v p.2 := by noncomm_ring
  simpa only [IsFamilyCauchy, he] using isFamilyNull_add τ h₁ h₂

variable [Nontrivial D]

def familyCauchyAlgebra : StarSubalgebra ℂ (lp (fun _ : ℕ => D) ∞) where
  carrier := {u | IsFamilyCauchy τ (fun n => u n)}
  zero_mem' := isFamilyCauchy_const τ 0
  one_mem' := isFamilyCauchy_const τ 1
  add_mem' hu hv := isFamilyCauchy_add τ hu hv
  mul_mem' {u v} hu hv := isFamilyCauchy_mul τ hu hv
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero v)
  algebraMap_mem' z := isFamilyCauchy_const τ (algebraMap ℂ D z)
  star_mem' hu := isFamilyCauchy_star τ hu

lemma familyCauchyAlgebra_isClosed : IsClosed
    (familyCauchyAlgebra τ : Set (lp (fun _ : ℕ => D) ∞)) := by
  apply isClosed_of_closure_subset
  intro u hu
  change IsFamilyCauchy τ (fun n => u n)
  rw [IsFamilyCauchy, isFamilyNull_iff]
  intro ε hε
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu (ε/3) (by linarith)
  have hnear (n : ℕ) : familyTwoNorm τ (u n-v n) < ε/3 :=
    (familyTwoNorm_le_norm τ _).trans_lt
      ((lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) n).trans_lt
        (by simpa only [dist_eq_norm] using huv))
  have he := (isFamilyNull_iff τ _ _).mp hv (ε/3) (by linarith)
  filter_upwards [he] with p hp
  have h₁ := familyTwoNorm_sub_triangle τ (u p.1) (v p.1) (u p.2)
  have h₂ := familyTwoNorm_sub_triangle τ (v p.1) (v p.2) (u p.2)
  rw [familyTwoNorm_sub_swap τ (v p.2) (u p.2)] at h₂
  linarith [hnear p.1, hnear p.2]

instance familyCauchy_complete : CompleteSpace (familyCauchyAlgebra τ) :=
  (familyCauchyAlgebra_isClosed τ).completeSpace_coe

instance familyCauchy_cstar : CStarAlgebra (familyCauchyAlgebra τ) where

def familyCauchyNullIdeal : ClosedStarIdeal (familyCauchyAlgebra τ) where
  ideal := TwoSidedIdeal.comap (familyCauchyAlgebra τ).val.toRingHom
    (familyNullIdeal τ atTop).ideal
  star_mem := by
    intro u hu
    apply (familyNullIdeal τ atTop).star_mem hu
  isClosed := by
    exact (familyNullIdeal τ atTop).isClosed.preimage
      (continuous_subtype_val : Continuous (fun u : familyCauchyAlgebra τ => u.1))

abbrev UniformTracialCompletion := (familyCauchyNullIdeal τ).Quotient

end CurrentMain

namespace Pureness.ClosedStarIdeal

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

instance quotientOrder (J : ClosedStarIdeal D) : PartialOrder J.Quotient :=
  CStarAlgebra.spectralOrder _

instance quotientStarOrdered (J : ClosedStarIdeal D) : StarOrderedRing J.Quotient :=
  CStarAlgebra.spectralOrderedRing _

variable (J : ClosedStarIdeal D)

variable (τ : TracialState D) (hτ : ∀ a ∈ J.ideal, τ.functional a = 0)

omit [StarOrderedRing D] in

include hτ in

lemma trace_congr (u v : D) (huv : J.ideal.ringCon u v) :
    τ.functional u = τ.functional v := by
  rw [TwoSidedIdeal.rel_iff] at huv
  have h := hτ (u-v) huv
  rw [map_sub, sub_eq_zero] at h
  exact h

def descendedValue : J.Quotient → ℂ := Quotient.lift τ.functional (J.trace_congr τ hτ)

omit [StarOrderedRing D] in

lemma descendedValue_map (u : D) : J.descendedValue τ hτ (J.quotientMap u) = τ.functional u := rfl

def descendedLinear : J.Quotient →ₗ[ℂ] ℂ where
  toFun := J.descendedValue τ hτ
  map_add' x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    rw [← map_add, J.descendedValue_map, J.descendedValue_map, J.descendedValue_map, map_add]
  map_smul' c x := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    rw [← map_smul, J.descendedValue_map, J.descendedValue_map, map_smul]
    rfl

lemma descendedLinear_square_nonneg (x : J.Quotient) :
    0 ≤ J.descendedLinear τ hτ (star x*x) := by
  obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
  change 0 ≤ J.descendedValue τ hτ (star (J.quotientMap u) * J.quotientMap u)
  rw [← J.quotientMap_star, ← map_mul, J.descendedValue_map]
  exact τ.functional.map_nonneg (star_mul_self_nonneg u)

def descendedTrace : TracialState J.Quotient where
  functional := { J.descendedLinear τ hτ with
    monotone' := by
      intro x y hxy
      apply sub_nonneg.mp
      change 0 ≤ J.descendedLinear τ hτ y - J.descendedLinear τ hτ x
      rw [← map_sub]
      obtain ⟨z,hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
      rw [hz]
      exact J.descendedLinear_square_nonneg τ hτ z }
  normalized := by
    change J.descendedValue τ hτ 1 = 1
    rw [← map_one J.quotientMap, J.descendedValue_map]
    exact τ.normalized
  tracial x y := by
    obtain ⟨u,rfl⟩ := J.quotientMap_surjective x
    obtain ⟨v,rfl⟩ := J.quotientMap_surjective y
    change J.descendedValue τ hτ (J.quotientMap u * J.quotientMap v) =
      J.descendedValue τ hτ (J.quotientMap v * J.quotientMap u)
    rw [← map_mul, ← map_mul, J.descendedValue_map, J.descendedValue_map]
    exact τ.tracial u v

end Pureness.ClosedStarIdeal

namespace CurrentMain

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

lemma bounded_ultrafilter_tendsto {X : Type uX} {E : Type uE} [NormedAddCommGroup E] [ProperSpace E]
    (U : Ultrafilter X) (f : X → E) (M : ℝ) (hM : ∀ n, ‖f n‖ ≤ M) :
    Tendsto f (U : Filter X) (𝓝 (limUnder (U : Filter X) f)) := by
  apply tendsto_nhds_limUnder
  obtain ⟨r,_,hr⟩ := (isCompact_closedBall (0 : E) M).ultrafilter_le_nhds' (U.map f)
    (show Metric.closedBall (0 : E) M ∈ U.map f from by
      change {n | f n ∈ Metric.closedBall (0 : E) M} ∈ U
      exact Filter.Eventually.of_forall (fun n => by simpa using hM n))
  exact ⟨r,hr⟩

section UltraTrace

variable {D : Type uD} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (θ : X → TracialState D) (U : Ultrafilter X)

instance boundedFamilyProductOrder : PartialOrder (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrder _

instance boundedFamilyProductStarOrdered : StarOrderedRing (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrderedRing _

def ultraTraceValue (u : lp (fun _ : X => D) ∞) : ℂ :=
  limUnder (U : Filter X) (fun n => (θ n).functional (u n))

omit [Nontrivial D] in

lemma ultraTraceValue_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => (θ n).functional (u n)) (U : Filter X) (𝓝 (ultraTraceValue θ U u)) :=
  bounded_ultrafilter_tendsto U _ ‖u‖ (fun n =>
    (trace_norm_le_norm (θ n) _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

omit [Nontrivial D] in

lemma ultraTraceValue_add (u v : lp (fun _ : X => D) ∞) :
    ultraTraceValue θ U (u+v) = ultraTraceValue θ U u+ultraTraceValue θ U v := by
  apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (u+v))
  simpa only [lp.coeFn_add, Pi.add_apply, map_add] using
    (ultraTraceValue_tendsto θ U u).add (ultraTraceValue_tendsto θ U v)

lemma ultraTraceValue_smul (z : ℂ) (u : lp (fun _ : X => D) ∞) :
    ultraTraceValue θ U (z • u) = z • ultraTraceValue θ U u := by
  apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (z • u))
  simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul, smul_eq_mul] using
    (ultraTraceValue_tendsto θ U u).const_mul z

def ultraTraceLinear : lp (fun _ : X => D) ∞ →ₗ[ℂ] ℂ where
  toFun := ultraTraceValue θ U
  map_add' := ultraTraceValue_add θ U
  map_smul' := ultraTraceValue_smul θ U

def boundedFamilyEval (n : X) : lp (fun _ : X => D) ∞ →⋆ₐ[ℂ] D where
  toFun u := u n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def ultraTrace : TracialState (lp (fun _ : X => D) ∞) where
  functional := { ultraTraceLinear θ U with
    monotone' := by
      intro u v huv
      exact le_of_tendsto_of_tendsto (ultraTraceValue_tendsto θ U u)
        (ultraTraceValue_tendsto θ U v) (Eventually.of_forall (fun n =>
          (θ n).functional.monotone (map_rel (boundedFamilyEval n) huv))) }
  normalized := by
    apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U 1)
    have he (n : X) : (θ n).functional ((1 : lp (fun _ : X => D) ∞) n) = 1 :=
      (θ n).normalized
    simp only [he]
    exact tendsto_const_nhds
  tracial u v := by
    change ultraTraceValue θ U (u*v) = ultraTraceValue θ U (v*u)
    apply tendsto_nhds_unique (ultraTraceValue_tendsto θ U (u*v))
    have he (n : X) : (θ n).functional ((u*v) n) = (θ n).functional ((v*u) n) :=
      (θ n).tracial (u n) (v n)
    simpa only [he] using ultraTraceValue_tendsto θ U (v*u)

end UltraTrace

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

abbrev FamilyUltrapower := (familyNullIdeal τ (U : Filter X)).Quotient

lemma ultraTrace_null (s : X → I) (u : lp (fun _ : X => D) ∞)
    (hu : u ∈ (familyNullIdeal τ (U : Filter X)).ideal) :
    (ultraTrace (fun n => τ (s n)) U).functional u = 0 := by
  have hn : IsFamilyNull τ (U : Filter X) (fun n => u n) :=
    (familyNull_mem τ _ u).mp hu
  have ht : Tendsto (fun n => (τ (s n)).functional (u n)) (U : Filter X) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      (trace_norm_le_twoNorm (τ (s n)) _).trans (traceTwoNorm_le_family τ (s n) _)) hn
  exact tendsto_nhds_unique (ultraTraceValue_tendsto (fun n => τ (s n)) U u) ht

def familyLimitTrace (s : X → I) : TracialState (FamilyUltrapower τ U) :=
  (familyNullIdeal τ (U : Filter X)).descendedTrace
    (ultraTrace (fun n => τ (s n)) U) (ultraTrace_null τ U s)

end

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section PullbackTrace

variable {D : Type uD} {E : Type uE} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

def pullbackTrace (τ : TracialState E) (ι : D →⋆ₐ[ℂ] E) : TracialState D where
  functional := { τ.functional.toLinearMap.comp ι.toLinearMap with
    monotone' := fun _ _ h => τ.functional.monotone (map_rel ι h) }
  normalized := by change τ.functional (ι 1) = 1; rw [map_one, τ.normalized]
  tracial x y := by
    change τ.functional (ι (x*y)) = τ.functional (ι (y*x))
    rw [map_mul ι x y, map_mul ι y x]
    exact τ.tracial _ _

end PullbackTrace

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

omit [Nontrivial D] in

lemma isFamilyCauchy_iff (u : ℕ → D) : IsFamilyCauchy τ u ↔
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, familyTwoNorm τ (u m-u n) < ε := by
  simp only [IsFamilyCauchy, isFamilyNull_iff, eventually_atTop_prod_self]
  constructor <;> intro h ε hε
  · obtain ⟨N,hN⟩ := h ε hε
    exact ⟨N,fun m hm n hn => hN m n hm hn⟩
  · obtain ⟨N,hN⟩ := h ε hε
    exact ⟨N,fun m n hm hn => hN m hm n hn⟩

lemma cauchy_trace_values (i : I) (u : familyCauchyAlgebra τ) :
    CauchySeq (fun n : ℕ => (τ i).functional (u.1 n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N,hN⟩ := (isFamilyCauchy_iff τ _).mp u.2 ε hε
  refine ⟨N,fun m hm n hn => ?_⟩
  rw [dist_eq_norm, ← map_sub]
  exact (trace_norm_le_twoNorm (τ i) _).trans_lt
    ((traceTwoNorm_le_family τ i _).trans_lt (hN m hm n hn))

instance familyCauchyOrder : PartialOrder (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrder _

instance familyCauchyStarOrdered : StarOrderedRing (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrderedRing _

def cauchyTrace (i : I) : TracialState (familyCauchyAlgebra τ) :=
  pullbackTrace (ultraTrace (fun _ : ℕ => τ i) (Ultrafilter.of atTop))
    (familyCauchyAlgebra τ).subtype

lemma cauchyTrace_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop
      (𝓝 ((cauchyTrace τ i).functional u)) := by
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete (cauchy_trace_values τ i u)
  have he : z = (cauchyTrace τ i).functional u := tendsto_nhds_unique
    (hz.mono_left (Ultrafilter.of_le atTop))
    (ultraTraceValue_tendsto (fun _ : ℕ => τ i) (Ultrafilter.of atTop) u.1)
  exact he ▸ hz

lemma cauchyTrace_null (i : I) (u : familyCauchyAlgebra τ)
    (hu : u ∈ (familyCauchyNullIdeal τ).ideal) :
    (cauchyTrace τ i).functional u = 0 := by
  have hmem : u.1 ∈ (familyNullIdeal τ atTop).ideal := hu
  have hn := (familyNull_mem τ atTop u.1).mp hmem
  have ht : Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
      (trace_norm_le_twoNorm (τ i) _).trans (traceTwoNorm_le_family τ i _)) hn
  exact tendsto_nhds_unique (cauchyTrace_tendsto τ i u) ht

def completionTrace (i : I) : TracialState (UniformTracialCompletion τ) :=
  (familyCauchyNullIdeal τ).descendedTrace (cauchyTrace τ i) (cauchyTrace_null τ i)

def boundedFamilyConstant {X : Type uX} (a : D) : lp (fun _ : X => D) ∞ :=
  ⟨fun _ => a, memℓp_infty_iff.mpr ⟨‖a‖,by rintro _ ⟨n,rfl⟩; exact le_rfl⟩⟩

def cauchyConstant (a : D) : familyCauchyAlgebra τ :=
  ⟨boundedFamilyConstant a, isFamilyCauchy_const τ a⟩

def completionMap : D →⋆ₐ[ℂ] UniformTracialCompletion τ where
  toFun a := (familyCauchyNullIdeal τ).quotientMap (cauchyConstant τ a)
  map_zero' := (familyCauchyNullIdeal τ).quotientMap.map_zero
  map_one' := (familyCauchyNullIdeal τ).quotientMap.map_one
  map_add' a b := (familyCauchyNullIdeal τ).quotientMap.map_add (cauchyConstant τ a) (cauchyConstant τ b)
  map_mul' a b := (familyCauchyNullIdeal τ).quotientMap.map_mul (cauchyConstant τ a) (cauchyConstant τ b)
  commutes' z := (familyCauchyNullIdeal τ).quotientMap.commutes z
  map_star' a := (familyCauchyNullIdeal τ).quotientMap_star (cauchyConstant τ a)

end

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

instance completionNontrivial : Nontrivial (UniformTracialCompletion τ) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he := congrArg (completionTrace τ i).functional h
  rw [(completionTrace τ i).normalized, map_zero] at he
  exact one_ne_zero he

end

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

def familyUltrapowerMap : D →⋆ₐ[ℂ] FamilyUltrapower τ U where
  toFun a := (familyNullIdeal τ (U : Filter X)).quotientMap (boundedFamilyConstant a)
  map_zero' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_zero
  map_one' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_one
  map_add' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_add
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  map_mul' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_mul
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  commutes' z := (familyNullIdeal τ (U : Filter X)).quotientMap.commutes z
  map_star' a := (familyNullIdeal τ (U : Filter X)).quotientMap_star (boundedFamilyConstant a)

end CurrentMain

namespace Pureness

open Filter Topology

variable {A : Type uA} [NormedRing A]

def TopologicallySimple (A : Type uA) [NormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

end Pureness

end

namespace CurrentMain

open Pureness Filter

def StablyFinite (A : Type uA) [CStarAlgebra A] : Prop :=
  ∀ n : ℕ, ∀ v : CStarMatrix (Fin n) (Fin n) A,
    star v*v = 1 → v*star v = 1

def UniformPropertyGammaAt (A : Type) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ) : Prop :=
  ∃ p : FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U,
    IsStarProjection p ∧ ∀ x : UniformTracialCompletion (fun τ : TracialState A => τ),
      p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x =
        familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x * p ∧
      ∀ s : ℕ → TracialState A,
        (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
          (p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x) =
        (1/2 : ℂ) *
        (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
          (familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x)

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.TraceEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

def IsFull {D : Type uD} [CStarAlgebra D] (g : D) : Prop :=
  closure (TwoSidedIdeal.span {g} : Set D) = Set.univ

def uniformTwoNorm {D : Type uD} [CStarAlgebra D] [PartialOrder D] (a : D) : ℝ :=
  ⨆ τ : TracialState D, traceTwoNorm τ a

def uniformHalvingError {D : Type uD} [CStarAlgebra D] [PartialOrder D]
    (p x : D) : ℝ :=
  ⨆ τ : TracialState D, ‖τ.functional (p * x) - (1 / 2 : ℂ) * τ.functional x‖

section WeightedAveraging

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Fintype I]

def weightedAverage (w : I → ℝ) (v : I → D) (b : D) : D :=
  ∑ i, w i • (v i * b * star (v i))

lemma trace_mul_nonneg (τ : TracialState D) {a b : D} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ τ.functional (a * b) := by
  have hs : star (CFC.sqrt a) = CFC.sqrt a := (CFC.sqrt_nonneg a).star_eq
  have ht : τ.functional (CFC.sqrt a * b * CFC.sqrt a) = τ.functional (a * b) := by
    rw [τ.tracial (CFC.sqrt a * b) (CFC.sqrt a), ← mul_assoc,
      CFC.sqrt_mul_sqrt_self a ha]
  rw [← ht]
  apply τ.functional.map_nonneg
  simpa only [hs] using (star_left_conjugate_nonneg hb (CFC.sqrt a))

end WeightedAveraging

section PowersStormer

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def traceOneNorm (τ : TracialState D) (a : D) : ℝ :=
  (τ.functional (CFC.abs a)).re

lemma trace_selfAdjoint_contraction_mul_le (τ : TracialState D)
    {s h : D} (hs : IsSelfAdjoint s) (hh : IsSelfAdjoint h) (hsn : ‖s‖ ≤ 1) :
    (τ.functional (s * h)).re ≤ traceOneNorm τ h := by
  have hmap : algebraMap ℝ D ‖s‖ ≤ 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
      (smul_le_smul_of_nonneg_right hsn (zero_le_one : (0 : D) ≤ 1))
  have hs1 : s ≤ 1 := hs.le_algebraMap_norm_self.trans hmap
  have h1s : -(1 : D) ≤ s := (neg_le_neg hmap).trans hs.neg_algebraMap_norm_le_self
  have hp := (trace_mul_nonneg τ (sub_nonneg.mpr hs1) (CFC.posPart_nonneg h)).1
  have hn := (trace_mul_nonneg τ (neg_le_iff_add_nonneg'.mp h1s)
    (CFC.negPart_nonneg h)).1
  have he : (1 - s) * h⁺ + (1 + s) * h⁻ = CFC.abs h - s * h := by
    calc
      _ = (h⁺ + h⁻) - s * (h⁺ - h⁻) := by noncomm_ring
      _ = _ := by rw [CFC.posPart_add_negPart h hh, CFC.posPart_sub_negPart h hh]
  have he' := congrArg (fun a => (τ.functional a).re) he
  simp only [map_add, map_sub, Complex.add_re, Complex.sub_re] at he'
  change (τ.functional (s * h)).re ≤ (τ.functional (CFC.abs h)).re
  simp only [Complex.zero_re] at hp hn
  linarith

def regularizedSign (ε : ℝ) (d : D) : D :=
  cfc (fun t : ℝ => t / (|t| + ε)) d

lemma continuous_regularizedSign {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun t : ℝ => t / (|t| + ε)) :=
  continuous_id.div (continuous_abs.add continuous_const)
    (fun t => ne_of_gt (add_pos_of_nonneg_of_pos (abs_nonneg t) hε))

omit [PartialOrder D] [StarOrderedRing D] in
lemma regularizedSign_selfAdjoint (ε : ℝ) (d : D) :
    IsSelfAdjoint (regularizedSign ε d) := cfc_predicate _ _

omit [PartialOrder D] [StarOrderedRing D] in
lemma regularizedSign_norm_le {ε : ℝ} (hε : 0 < ε) (d : D) :
    ‖regularizedSign ε d‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t _
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (add_pos_of_nonneg_of_pos (abs_nonneg t) hε)]
  apply (div_le_one (add_pos_of_nonneg_of_pos (abs_nonneg t) hε)).mpr
  linarith

lemma regularizedSign_scalar_error {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖‖t‖ - t / (|t| + ε) * t‖ ≤ ε := by
  have hpos := add_pos_of_nonneg_of_pos (abs_nonneg t) hε
  have heq : |t| - t / (|t| + ε) * t = ε * |t| / (|t| + ε) := by
    field_simp
    nlinarith [sq_abs t]
  rw [Real.norm_eq_abs t, heq, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg hε.le (abs_nonneg t)) hpos.le)]
  apply (div_le_iff₀ hpos).mpr
  nlinarith

lemma regularizedSign_error {ε : ℝ} (hε : 0 < ε) {d : D}
    (hd : IsSelfAdjoint d) :
    ‖CFC.abs d - regularizedSign ε d * d‖ ≤ ε := by
  have hf := continuous_regularizedSign hε
  have hmul : cfc (fun t : ℝ => t / (|t| + ε) * t) d =
      regularizedSign ε d * d := by
    rw [cfc_mul (fun t : ℝ => t / (|t| + ε)) (fun t : ℝ => t) d
      (hf := hf.continuousOn), cfc_id' ℝ d]
    rfl
  rw [CFC.abs_eq_cfcₙ_norm d hd, cfcₙ_eq_cfc (hf0 := norm_zero), ← hmul,
    ← cfc_sub (fun t : ℝ => ‖t‖) (fun t : ℝ => t / (|t| + ε) * t) d
      (hf := continuous_norm.continuousOn) (hg := (hf.mul continuous_id).continuousOn)]
  exact norm_cfc_le hε.le (fun t _ => regularizedSign_scalar_error hε t)

lemma traceOneNorm_le_of_pairing (τ : TracialState D) {h : D} (hh : IsSelfAdjoint h)
    {C : ℝ} (hC : ∀ s : D, IsSelfAdjoint s → ‖s‖ ≤ 1 →
      (τ.functional (s * h)).re ≤ C) : traceOneNorm τ h ≤ C := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let s := regularizedSign ε h
  have hbound := hC s (regularizedSign_selfAdjoint ε h) (regularizedSign_norm_le hε h)
  have herror : traceOneNorm τ h - (τ.functional (s * h)).re ≤ ε := by
    calc
      _ = (τ.functional (CFC.abs h - s * h)).re := by
        simp only [traceOneNorm, map_sub, Complex.sub_re]
      _ ≤ ‖τ.functional (CFC.abs h - s * h)‖ := Complex.re_le_norm _
      _ ≤ ‖CFC.abs h - s * h‖ := trace_norm_le_norm τ _
      _ ≤ ε := regularizedSign_error hε hh
  linarith

lemma traceOneNorm_add_le (τ : TracialState D) {a b : D}
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    traceOneNorm τ (a + b) ≤ traceOneNorm τ a + traceOneNorm τ b := by
  apply traceOneNorm_le_of_pairing τ (ha.add hb)
  intro s hs hsn
  simp only [mul_add, map_add, Complex.add_re]
  exact add_le_add (trace_selfAdjoint_contraction_mul_le τ hs ha hsn)
    (trace_selfAdjoint_contraction_mul_le τ hs hb hsn)

@[simp] lemma traceOneNorm_neg (τ : TracialState D) (a : D) :
    traceOneNorm τ (-a) = traceOneNorm τ a := by simp [traceOneNorm]

end PowersStormer

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpectralCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section FiniteSpectralResolution

variable {D : Type uD} [CStarAlgebra D]

def spectralAtom (a : D) (t : ℝ) : D :=
  cfc (fun x : ℝ => if x = t then (1 : ℝ) else 0) a

lemma spectralAtom_projection {a : D} (hfinite : (spectrum ℝ a).Finite) (t : ℝ) :
    IsStarProjection (spectralAtom a t) := by
  refine ⟨?_, cfc_predicate _ _⟩
  change cfc _ a * cfc _ a = cfc _ a
  rw [← cfc_mul _ _ a (hfinite.continuousOn _) (hfinite.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

lemma spectralAtom_orthogonal {a : D} (hfinite : (spectrum ℝ a).Finite)
    {s t : ℝ} (hst : s ≠ t) : spectralAtom a s * spectralAtom a t = 0 := by
  change cfc _ a * cfc _ a = 0
  rw [← cfc_mul _ _ a (hfinite.continuousOn _) (hfinite.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 0) a := by
      apply cfc_congr
      intro x _
      by_cases hxs : x = s
      · subst x
        simp [hst]
      · simp [hxs]
    _ = 0 := cfc_zero ℝ a

lemma spectralAtom_sum {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℝ a).Finite) : ∑ t ∈ hfinite.toFinset, spectralAtom a t = 1 := by
  classical
  simp only [spectralAtom]
  rw [← cfc_sum _ a hfinite.toFinset (fun _ _ => hfinite.continuousOn _)]
  calc
    _ = cfc (fun _ : ℝ => 1) a := by
      apply cfc_congr
      intro x hx
      simp only [Finset.sum_apply]
      simp [Set.Finite.mem_toFinset, hx]
    _ = 1 := cfc_one ℝ a ha

end FiniteSpectralResolution

section ProjectionCorners

variable {D : Type uD} [CStarAlgebra D]

def projectionCornerSubalgebra {p : D} (hp : IsStarProjection p) :
    NonUnitalStarSubalgebra ℂ D where
  carrier := {a | p * a = a ∧ a * p = a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    simp [mul_add, add_mul, ha, ha', hb, hb']
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [← mul_assoc, ha], by rw [mul_assoc, hb']⟩
  smul_mem' := by
    rintro r a ⟨ha, ha'⟩
    simp [ha, ha']
  star_mem' := by
    rintro a ⟨ha, ha'⟩
    constructor
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star ha

abbrev ProjectionCorner {p : D} (hp : IsStarProjection p) := projectionCornerSubalgebra hp

namespace ProjectionCorner

variable {p : D} (hp : IsStarProjection p)

instance instSemiringSubtypeMemNonUnitalStarSubalgebraComplex : Semiring (ProjectionCorner hp) where
  __ : NonUnitalSemiring (ProjectionCorner hp) := inferInstance
  one := ⟨p, hp.isIdempotentElem, hp.isIdempotentElem⟩
  one_mul a := Subtype.ext a.property.1
  mul_one a := Subtype.ext a.property.2

instance instRingSubtypeMemNonUnitalStarSubalgebraComplex : Ring (ProjectionCorner hp) where
  __ : Semiring (ProjectionCorner hp) := inferInstance
  __ : NonUnitalRing (ProjectionCorner hp) := inferInstance

@[simp] lemma coe_one : ((1 : ProjectionCorner hp) : D) = p := rfl

instance instAlgebraComplexSubtypeMemNonUnitalStarSubalgebra : Algebra ℂ (ProjectionCorner hp) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex : NormedRing (ProjectionCorner hp) where
  __ : Ring (ProjectionCorner hp) := inferInstance
  __ : NonUnitalNormedRing (ProjectionCorner hp) := inferInstance

instance instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra : NormedAlgebra ℂ (ProjectionCorner hp) where
  __ : Algebra ℂ (ProjectionCorner hp) := inferInstance
  norm_smul_le r x := norm_smul_le r x

lemma isClosed : IsClosed (projectionCornerSubalgebra hp : Set D) :=
  (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

instance instCompleteSpaceSubtypeMemNonUnitalStarSubalgebraComplex : CompleteSpace (ProjectionCorner hp) := (isClosed hp).completeSpace_coe

instance instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex : CStarAlgebra (ProjectionCorner hp) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le (x : D)

def inclusion : ProjectionCorner hp →⋆ₙₐ[ℂ] D := NonUnitalStarSubalgebraClass.subtype (projectionCornerSubalgebra hp)

def compress (a : D) : ProjectionCorner hp :=
  ⟨p * a * p, by
    constructor
    · simp only [← mul_assoc, hp.isIdempotentElem.eq]
    · simp only [mul_assoc, hp.isIdempotentElem.eq]⟩

@[simp] lemma coe_compress (a : D) : ((compress hp a : ProjectionCorner hp) : D) = p * a * p := rfl

end ProjectionCorner

end ProjectionCorners

section ProjectionPolars

open scoped NNReal

open Topology

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def unitaryPolar (z : D) : D := z * Ring.inverse (CFC.sqrt (star z * z))

@[simp] lemma unitaryPolar_one : unitaryPolar (1 : D) = 1 := by
  simp [unitaryPolar]

omit [PartialOrder D] [StarOrderedRing D] in
def projectionIntertwiner (p q : D) : D := p * q + (1 - p) * (1 - q)

end ProjectionPolars

section SpectralCutoffs

variable {D : Type uD} [CStarAlgebra D]

def gapCutoff (t : ℝ) : ℝ := max 0 (min 1 (t - 1))

end SpectralCutoffs

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ScalarCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section ScalarCompression

variable {D : Type uD} [CStarAlgebra D]

lemma spectralAtom_ne_zero {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) {t : ℝ} (ht : t ∈ spectrum ℝ a) :
    spectralAtom a t ≠ 0 := by
  intro h
  have hn := norm_apply_le_norm_cfc (fun x : ℝ => if x = t then 1 else 0) a ht
    (hf.continuousOn _) ha
  change ‖if t = t then (1 : ℝ) else 0‖ ≤ ‖spectralAtom a t‖ at hn
  rw [h] at hn
  norm_num at hn

structure ProjectionPartition (r : D) where
  Index : Type
  [indexFintype : Fintype Index]
  piece : Index → D
  isProjection : ∀ i, IsStarProjection (piece i)
  nonzero : ∀ i, piece i ≠ 0
  orthogonal : Pairwise (fun i j => piece i * piece j = 0)
  sum_eq : ∑ i, piece i = r

attribute [instance] ProjectionPartition.indexFintype

namespace ProjectionPartition

variable {r : D} (P : ProjectionPartition r)

lemma mul_parent (i : P.Index) : P.piece i * r = P.piece i := by
  classical
  calc
    _ = P.piece i * ∑ j, P.piece j := congrArg (P.piece i * ·) P.sum_eq.symm
    _ = _ := by
      rw [Finset.mul_sum, Finset.sum_eq_single i]
      · exact (P.isProjection i).isIdempotentElem
      · intro j _ hji
        exact P.orthogonal hji.symm
      · simp

lemma parent_mul (i : P.Index) : r * P.piece i = P.piece i := by
  classical
  calc
    _ = (∑ j, P.piece j) * P.piece i := congrArg (· * P.piece i) P.sum_eq.symm
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_eq_single i]
      · exact (P.isProjection i).isIdempotentElem
      · intro j _ hji
        exact P.orthogonal hji
      · simp

end ProjectionPartition

def cornerSpectralPartition {r : D} (hr : IsStarProjection r)
    {b : ProjectionCorner hr} (hb : IsSelfAdjoint b) (hf : (spectrum ℝ b).Finite) :
    ProjectionPartition r where
  Index := hf.toFinset
  piece t := (spectralAtom b t : ProjectionCorner hr)
  isProjection t := (spectralAtom_projection hf t).map (ProjectionCorner.inclusion hr)
  nonzero t := by
    intro hz
    apply spectralAtom_ne_zero hb hf (by simpa only [Set.Finite.mem_toFinset] using t.property)
    exact Subtype.ext hz
  orthogonal := by
    intro s t hst
    have hst' : (s : ℝ) ≠ (t : ℝ) := fun he => hst (Subtype.ext he)
    exact congrArg Subtype.val (spectralAtom_orthogonal hf hst')
  sum_eq := by
    change ∑ i : hf.toFinset, (ProjectionCorner.inclusion hr) (spectralAtom b (i : ℝ)) = r
    rw [Finset.sum_coe_sort hf.toFinset (fun t : ℝ =>
      (ProjectionCorner.inclusion hr) (spectralAtom b t)), ← map_sum, spectralAtom_sum hb hf]
    rfl

namespace ProjectionPartition

variable {r : D}

def refine (P : ProjectionPartition r) (Q : ∀ i, ProjectionPartition (P.piece i)) :
    ProjectionPartition r where
  Index := Σ i : P.Index, (Q i).Index
  piece i := (Q i.1).piece i.2
  isProjection i := (Q i.1).isProjection i.2
  nonzero i := (Q i.1).nonzero i.2
  orthogonal := by
    rintro ⟨i, s⟩ ⟨j, t⟩ hst
    by_cases hij : i = j
    · subst j
      exact (Q i).orthogonal (fun h => hst (congrArg (Sigma.mk i) h))
    · calc
        _ = ((Q i).piece s * P.piece i) * (P.piece j * (Q j).piece t) := by
          rw [(Q i).mul_parent, (Q j).parent_mul]
        _ = (Q i).piece s * (P.piece i * P.piece j) * (Q j).piece t := by
          simp only [mul_assoc]
        _ = 0 := by rw [P.orthogonal hij, mul_zero, zero_mul]
  sum_eq := by
    rw [Fintype.sum_sigma]
    simp only [(Q _).sum_eq]
    exact P.sum_eq

def empty : ProjectionPartition (0 : D) where
  Index := Empty
  piece := Empty.elim
  isProjection i := Empty.elim i
  nonzero i := Empty.elim i
  orthogonal i := Empty.elim i
  sum_eq := by simp

def singleton (hr : IsStarProjection r) (hr0 : r ≠ 0) : ProjectionPartition r where
  Index := Unit
  piece _ := r
  isProjection _ := hr
  nonzero _ := hr0
  orthogonal := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
  sum_eq := by simp

end ProjectionPartition

end ScalarCompression

section SpectralThresholds

variable {D : Type uD} [CStarAlgebra D]

def spectralThreshold (a : D) (t : ℝ) : D :=
  cfc (fun s : ℝ => if t ≤ s then (1 : ℝ) else 0) a

end SpectralThresholds

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ProjectionFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section FullProjectionFrames

open Filter Topology

open scoped CStarAlgebra

variable {A : Type uA} [CStarAlgebra A]

def finiteSandwichIdeal (e : A) : TwoSidedIdeal A :=
  .mk' {a | ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = a}
    ⟨[], by simp⟩
    (by rintro a b ⟨l, rfl⟩ ⟨m, rfl⟩; exact ⟨l ++ m, by simp⟩)
    (by
      rintro a ⟨l, rfl⟩
      refine ⟨l.map (fun v => (-v.1, v.2)), ?_⟩
      simp only [List.map_map, Function.comp_def, neg_mul]
      induction l with
      | nil => simp
      | cons v l ih => simp [ih, add_comm])
    (by
      rintro a b ⟨l, rfl⟩
      refine ⟨l.map (fun v => (a * v.1, v.2)), ?_⟩
      simp only [List.map_map, Function.comp_def, mul_assoc]
      induction l with
      | nil => simp
      | cons v l ih => simpa [mul_add, mul_assoc] using congrArg (fun z => a * v.1 * e * v.2 + z) ih)
    (by
      rintro a b ⟨l, rfl⟩
      refine ⟨l.map (fun v => (v.1, v.2 * b)), ?_⟩
      simp only [List.map_map, Function.comp_def, ← mul_assoc]
      induction l with
      | nil => simp
      | cons v l ih => simpa [add_mul, mul_assoc] using congrArg (fun z => v.1 * e * v.2 * b + z) ih)

@[simp] theorem mem_finiteSandwichIdeal (e a : A) :
    a ∈ finiteSandwichIdeal e ↔
      ∃ l : List (A × A), (l.map fun v => v.1 * e * v.2).sum = a := by
  simp [finiteSandwichIdeal]

end FullProjectionFrames

section ColumnSplitting

variable {D : Type uD} [CStarAlgebra D]

def ProjectionSubequivalent (e g : D) : Prop :=
  ∃ v : D, star v * v = e ∧ g * v = v

end ColumnSplitting

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ProjectionRounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section RoundingNumerics

def roundCoeff (s : ℝ) (i : ℕ) : ℝ := (⌊s * (i + 1 : ℕ)⌋ - ⌊s * i⌋ : ℤ)

def roundDeficit (s : ℝ) (i : ℕ) : ℝ := (⌊s * i⌋ : ℝ) - s * i

@[simp] lemma roundDeficit_zero (s : ℝ) : roundDeficit s 0 = 0 := by simp [roundDeficit]

end RoundingNumerics

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ProjectionSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section MatrixRows

variable {D : Type uD} [CStarAlgebra D]

structure ProjectionRow (I : Type uI) [Fintype I] (q : D) where
  projection : IsStarProjection q
  entry : I → D
  gram_diag : ∀ i, star (entry i) * entry i = q
  gram_offdiag : ∀ i j, i ≠ j → star (entry i) * entry j = 0

namespace ProjectionRow

variable {I : Type uI} [Fintype I] {q : D} (U : ProjectionRow I q)

def coeff (a : D) (i j : I) : D := U.entry i * a * star (U.entry j)

def sample (a : D) : D := ∑ i, U.coeff a i i

def matrix (a : D) (s : Matrix I I ℂ) : D := ∑ i, ∑ j, s i j • U.coeff a i j

end ProjectionRow

end MatrixRows

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpectralLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section LayerCake

variable {I : Type uI} [Fintype I] [LinearOrder I]

def cutCoefficient (j i : I) : ℝ := if j ≤ i then 1 else 0

def layerCoefficient (w : I → ℝ) (i : I) : ℝ := ∑ j, w j * cutCoefficient j i

variable {D : Type uD} [CStarAlgebra D]

def upperLayerCut (e : I → D) (j : I) : D := ∑ i, cutCoefficient j i • e i

end LayerCake

section LayerWeights

def orderedLayerWeights {n : ℕ} (c : Fin n → ℝ) (j : Fin n) : ℝ :=
  Fin.cons (α := fun _ => ℝ) 0 c j.succ - Fin.cons (α := fun _ => ℝ) 0 c j.castSucc

end LayerWeights

section LayerComplete

variable {D : Type uD} [CStarAlgebra D] {n : ℕ}

def completeResolution (e : Fin n → D) : Fin (n + 1) → D :=
  Fin.cons (α := fun _ => D) (1 - ∑ i, e i) e

end LayerComplete

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.MatrixNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI uι uκ

noncomputable section

namespace Pureness

open scoped ComplexOrder ComplexStarModule

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def selfAdjointFunctionalComplex (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (ℜ a) : ℂ) + Complex.I * (f (ℑ a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

end Pureness

namespace CurrentMain

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def rowGram (a : I → D) : CStarMatrix I I D :=
  CStarMatrix.ofMatrix (fun i j => star (a i) * a j)

def rowMul (a : I → D) (Z : CStarMatrix I I D) : I → D :=
  fun i => ∑ j, a j * Z j i

end

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

namespace ProjectionCorner

variable {q : D} (hq : IsStarProjection q)

def compressPositive : D →ₚ[ℂ] ProjectionCorner hq where
  toFun := compress hq
  map_add' a b := Subtype.ext (by simp [coe_compress, mul_add, add_mul])
  map_smul' r a := Subtype.ext (by simp [coe_compress])
  monotone' := by
    intro a b hab
    change q * a * q ≤ q * b * q
    simpa only [hq.isSelfAdjoint.star_eq] using star_left_conjugate_le_conjugate hab q

end ProjectionCorner

end

open scoped ComplexOrder

section RowRotate

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I] [CStarAlgebra D]

def rotateRow (a : I → D) (Z : Matrix I I ℂ) : I → D := fun i => ∑ j, Z j i • a j

def rowPair (a : I → D) (x : D) (i j : I) : D := star (a i) * x * a j

end RowRotate

variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

def scalarRowGram (f : D →ₚ[ℂ] ℂ) (a : I → D) : Matrix I I ℂ :=
  fun i j => f (star (a i) * a j)

omit [DecidableEq I] in
lemma scalarRowGram_posSemidef (f : D →ₚ[ℂ] ℂ) (a : I → D) :
    (scalarRowGram f a).PosSemidef := by
  have he : scalarRowGram f a = Matrix.gram ℂ (fun i => f.toPreGNS (a i)) := by
    ext i j
    simp only [scalarRowGram, Matrix.gram_apply, PositiveLinearMap.preGNS_inner_def,
      PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [he]
  exact Matrix.posSemidef_gram ℂ _

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.RowEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

section RowSubmatrix

variable {I : Type uI} {J : Type uJ} {D : Type uD} [Fintype I] [Fintype J] [CStarAlgebra D]

namespace ProjectionRow

variable {q : D} (U : ProjectionRow I q)

def subrow (f : J ↪ I) : ProjectionRow J q where
  projection := U.projection
  entry := U.entry ∘ f
  gram_diag i := U.gram_diag (f i)
  gram_offdiag i j hij := U.gram_offdiag (f i) (f j) (f.injective.ne hij)

omit [Fintype J] in
def atom (i : I) : D := U.entry i * star (U.entry i)

end ProjectionRow

end RowSubmatrix

end

open scoped ComplexOrder

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpectralBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uE uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {I : Type uI} {D : Type uD} [Fintype I] [CStarAlgebra D]

def sortedIndex (c : I → ℝ) : Fin (Fintype.card I) ≃ I :=
  (Tuple.sort (c ∘ (Fintype.equivFin I).symm)).trans (Fintype.equivFin I).symm

namespace ProjectionRow

variable {q : D} (U : ProjectionRow I q)

def sorted (c : I → ℝ) : ProjectionRow (Fin (Fintype.card I)) q :=
  U.subrow (sortedIndex c).toEmbedding

end ProjectionRow

end

section

open scoped ComplexOrder

def rowCorrectionError (m σ δ : ℝ) : ℝ :=
  2 * m ^ 3 * (Real.sqrt σ)⁻¹ ^ 3 * m * (m ^ 2 * δ)

def rowCompressionError (m σ δ : ℝ) : ℝ :=
  rowCorrectionError m σ δ * (1 + (Real.sqrt σ)⁻¹ * m) +
    (Real.sqrt σ)⁻¹ ^ 2 * (m ^ 2 * δ)

structure BlockControl (m η : ℝ) where
  cutoff : ℝ
  tolerance : ℝ
  cutoff_pos : 0 < cutoff
  cutoff_lt_one : cutoff < 1
  tolerance_pos : 0 < tolerance
  inverse_control : m ^ 2 * ((Real.sqrt cutoff)⁻¹ ^ 2 * (m ^ 2 * tolerance)) ≤ 1 / 2
  trace_control : m * ((m + 1) * rowCorrectionError m cutoff tolerance +
    (cutoff + m ^ 2 * tolerance)) ≤ η ^ 2
  compression_control : m ^ 2 * rowCompressionError m cutoff tolerance < η

end

variable {D : Type uD} [CStarAlgebra D] {q : D} {n : ℕ}

def upperEmbedding (j : Fin n) :
    Fin (Fintype.card {i : Fin n // j ≤ i}) ↪ Fin n :=
  (Fintype.equivFin {i : Fin n // j ≤ i}).symm.toEmbedding.trans
    (Function.Embedding.subtype (j ≤ ·))

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.WeightedFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI uJ

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

structure WeightedBlockFamily (r : D) where
  Index : Type
  [indexFintype : Fintype Index]
  weight : Index → ℝ
  weight_pos : ∀ j, 0 < weight j
  weight_le_one : ∀ j, weight j ≤ 1
  base : Index → D
  baseProjection : ∀ j, IsStarProjection (base j)
  base_nonzero : ∀ j, base j ≠ 0
  base_le : ∀ j, base j ≤ r
  columns : Index → ℕ
  columns_pos : ∀ j, 0 < columns j
  row : ∀ j, ProjectionRow (Fin (columns j)) (base j)

attribute [instance] WeightedBlockFamily.indexFintype

namespace WeightedBlockFamily

variable {r : D} (F : WeightedBlockFamily r)

def range (j : F.Index) : D := (F.row j).sample (F.base j)

def weightedSum : D := ∑ j, F.weight j • F.range j

end WeightedBlockFamily

end

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {I : Type uI} [Fintype I] {q : D}

namespace ProjectionRow

variable (U : ProjectionRow I q)

def overlapTest (z : D) : D := ∑ i, star (U.entry i) * z * U.entry i

end ProjectionRow

end

open scoped ComplexOrder

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.OrthogonalPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

structure ProjectionInsertion (n : ℕ) (z₀ : D) where
  occupied : Fin (n + 1) → D
  sampled : Fin n → D
  inserted : Fin n → D
  initial : occupied 0 = z₀
  occupied_projection : ∀ a, IsStarProjection (occupied a)
  sampled_projection : ∀ a, IsStarProjection (sampled a)
  inserted_projection : ∀ a, IsStarProjection (inserted a)
  complement : ∀ a, inserted a ≤ 1 - occupied a.castSucc
  update : ∀ a, occupied a.succ = occupied a.castSucc + inserted a

structure PackingStepBounds (p z y t : D) (c η ε : ℝ) (K : Finset (unitary D)) : Prop where
  mass : ∀ τ : Pureness.TracialState D,
    |(τ.functional y).re - c * (τ.functional p).re| ≤ ε
  overlap : ∀ τ : Pureness.TracialState D,
    |(τ.functional (z * y)).re - c * (τ.functional (z * p)).re| ≤ ε
  inserted_mass_lower : ∀ τ : Pureness.TracialState D,
    (τ.functional y).re - 3 * (τ.functional (z * y)).re ≤ (τ.functional t).re
  inserted_mass_upper : ∀ τ : Pureness.TracialState D,
    (τ.functional t).re ≤ (τ.functional y).re
  inserted_distance : ∀ τ : Pureness.TracialState D,
    traceTwoNorm τ (t - y) ^ 2 ≤ 5 * (τ.functional (z * y)).re
  inserted_linear : ∀ τ : Pureness.TracialState D, ∀ x : D, ‖x‖ ≤ 1 →
    ‖τ.functional ((t - y) * x)‖ ≤
      2 * Real.sqrt (τ.functional y).re * traceTwoNorm τ (t - y)
  sampled_linear : ∀ x ∈ K, ∀ τ : Pureness.TracialState D,
    ‖τ.functional (y * (x : D)) - (c : ℂ) * τ.functional (p * (x : D))‖ ≤
      η * ((τ.functional y).re + c * (τ.functional p).re) + 2 * ε
  sampled_energy : ∀ x ∈ K, ∀ τ : Pureness.TracialState D,
    traceTwoNorm τ ((x : D) * y - y * (x : D)) ^ 2 ≤
      c * traceTwoNorm τ ((x : D) * p - p * (x : D)) ^ 2 +
        6 * η * ((τ.functional y).re + c * (τ.functional p).re) + 10 * ε

end

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {r : D}

structure SampledPackingRound (F : WeightedBlockFamily r) (z₀ : D)
    (K : Finset (unitary D)) (η δ : ℝ) where
  final : D
  occupied : F.Index × Bool → D
  sampled : F.Index × Bool → D
  inserted : F.Index × Bool → D
  final_projection : IsStarProjection final
  occupied_projection : ∀ a, IsStarProjection (occupied a)
  sampled_projection : ∀ a, IsStarProjection (sampled a)
  inserted_projection : ∀ a, IsStarProjection (inserted a)
  occupied_le_final : ∀ a, occupied a ≤ final
  inserted_orthogonal : Pairwise (fun a b => inserted a * inserted b = 0)
  initial_orthogonal : ∀ a, z₀ * inserted a = 0
  final_eq : final = z₀ + ∑ a, inserted a
  bounds : ∀ a, PackingStepBounds (F.range a.1) (occupied a) (sampled a) (inserted a)
    (η * F.weight a.1 / 2) η δ K

namespace SampledPackingRound

variable {F : WeightedBlockFamily r} {z₀ : D} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

def sampledMass (τ : Pureness.TracialState D) : ℝ := ∑ a, (τ.functional (R.sampled a)).re

def targetMass (_R : SampledPackingRound F z₀ K η δ) (τ : Pureness.TracialState D) : ℝ :=
  η * ∑ j, F.weight j * (τ.functional (F.range j)).re

def overlap (τ : Pureness.TracialState D) : ℝ :=
  ∑ a, (τ.functional (R.occupied a * R.sampled a)).re

def totalError (_R : SampledPackingRound F z₀ K η δ) : ℝ := Fintype.card (F.Index × Bool) * δ

end SampledPackingRound

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.PackingEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI uM

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

namespace SampledPackingRound

variable {z₀ : D} {F : WeightedBlockFamily (1 - z₀)} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

structure Estimates (E : ℝ) : Prop where
  target_upper : ∀ τ : Pureness.TracialState D, R.targetMass τ ≤ 2 * η
  sampled_upper : ∀ τ : Pureness.TracialState D, R.sampledMass τ ≤ 3 * η
  sampled_lower : ∀ τ : Pureness.TracialState D, η * (τ.functional (1 - z₀)).re - 3 * η ^ 2 ≤ R.sampledMass τ
  overlap_upper : ∀ τ : Pureness.TracialState D, R.overlap τ ≤ 4 * η * E + 5 * η ^ 2
  overlap_incr : ∀ τ : Pureness.TracialState D, R.overlap τ ≤ 1000 * η * (E + η)
  linear_sum : ∀ x : unitary D, x ∈ K → ∀ τ : Pureness.TracialState D, (∑ a : F.Index × Bool, ‖τ.functional (R.sampled a * (x : D)) -
    ((η * F.weight a.1 / 2 : ℝ) : ℂ) * τ.functional (F.range a.1 * (x : D))‖) ≤ 7 * η ^ 2
  inserted_energy : ∀ x : unitary D, x ∈ K → ∀ τ : Pureness.TracialState D,
    (∑ a : F.Index × Bool, traceTwoNorm τ ((x : D) * R.inserted a - R.inserted a * (x : D)) ^ 2) ≤
      1000 * η * (E + η)
  remaining : ∀ τ : Pureness.TracialState D, (τ.functional (1 - R.final)).re ≤
    (1 - η) * (τ.functional (1 - z₀)).re + 3 * η ^ 2 + 3 * R.overlap τ

end SampledPackingRound

omit [StarOrderedRing D] [PartialOrder D] in
lemma projection_finset_sum {I : Type uI} (s : Finset I) (t : I → D)
    (ht : ∀ i ∈ s, IsStarProjection (t i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0) :
    IsStarProjection (∑ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsStarProjection.zero]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, IsStarProjection (t i) := fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hso : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → t i * t j = 0 :=
      fun i hi j hj hij => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hao : t a * ∑ i ∈ s, t i = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i hi
      exact ho a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.sum_insert ha]
    exact (ht a (Finset.mem_insert_self a s)).add (ih hs hso) hao

namespace SampledPackingRound

section

variable {r z₀ : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F z₀ K η δ)

def signSum (σ : Bool) : D := ∑ j, R.inserted (j, σ)

omit [StarOrderedRing D] in
lemma signSum_projection (σ : Bool) : IsStarProjection (R.signSum σ) :=
  projection_finset_sum _ _ (fun _ _ => R.inserted_projection _)
    (fun _ _ _ _ h => R.inserted_orthogonal (fun he => h (Prod.mk.inj he).1))

omit [StarOrderedRing D] in
lemma signSum_orthogonal : R.signSum false * R.signSum true = 0 := by
  simp only [signSum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k _
  exact R.inserted_orthogonal (by simp)

omit [StarOrderedRing D] in
lemma initial_signSum_orthogonal (σ : Bool) : z₀ * R.signSum σ = 0 := by
  simp only [signSum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun _ _ => R.initial_orthogonal _

lemma subinitial_signSum_orthogonal {p : D} (hp : IsStarProjection p)
    (hz₀ : IsStarProjection z₀) (hpz : p ≤ z₀) (σ : Bool) : p * R.signSum σ = 0 := by
  calc
    _ = (p * z₀) * R.signSum σ := by rw [(hp.le_iff_mul_eq_left hz₀).mp hpz]
    _ = 0 := by rw [mul_assoc, R.initial_signSum_orthogonal, mul_zero]

end

end SampledPackingRound

structure OrthogonalProjectionPair (D : Type uD) [CStarAlgebra D] where
  left : D
  right : D
  left_projection : IsStarProjection left
  right_projection : IsStarProjection right
  orthogonal : left * right = 0

namespace OrthogonalProjectionPair

variable (Q : OrthogonalProjectionPair D)

def total : D := Q.left + Q.right

def energy (τ : Pureness.TracialState D) (x : D) : ℝ :=
  traceTwoNorm τ (x * Q.left - Q.left * x) ^ 2 + traceTwoNorm τ (x * Q.right - Q.right * x) ^ 2

def balance (τ : Pureness.TracialState D) (x : D) : ℝ :=
  ‖τ.functional (Q.left * x) - τ.functional (Q.right * x)‖

def remaining (τ : Pureness.TracialState D) : ℝ := (τ.functional (1 - Q.total)).re

omit [PartialOrder D] [StarOrderedRing D] in
lemma total_projection : IsStarProjection Q.total :=
  Q.left_projection.add Q.right_projection Q.orthogonal

lemma left_le_total : Q.left ≤ Q.total := le_add_of_nonneg_right Q.right_projection.nonneg

lemma right_le_total : Q.right ≤ Q.total := le_add_of_nonneg_left Q.left_projection.nonneg

variable {r : D} {F : WeightedBlockFamily r} {K : Finset (unitary D)} {η δ : ℝ}

variable (R : SampledPackingRound F Q.total K η δ)

lemma right_signSum_orthogonal (σ : Bool) : Q.right * R.signSum σ = 0 :=
  R.subinitial_signSum_orthogonal Q.right_projection Q.total_projection Q.right_le_total σ

lemma left_signSum_orthogonal (σ : Bool) : Q.left * R.signSum σ = 0 :=
  R.subinitial_signSum_orthogonal Q.left_projection Q.total_projection Q.left_le_total σ

lemma signSum_right_orthogonal (σ : Bool) : R.signSum σ * Q.right = 0 := by
  have h := congrArg star (Q.right_signSum_orthogonal R σ)
  simpa only [star_mul, (R.signSum_projection σ).isSelfAdjoint.star_eq,
    Q.right_projection.isSelfAdjoint.star_eq, star_zero] using h

def appendRound : OrthogonalProjectionPair D where
  left := Q.left + R.signSum false
  right := Q.right + R.signSum true
  left_projection := Q.left_projection.add (R.signSum_projection false) (Q.left_signSum_orthogonal R false)
  right_projection := Q.right_projection.add (R.signSum_projection true) (Q.right_signSum_orthogonal R true)
  orthogonal := by
    simp only [add_mul, mul_add, Q.orthogonal, Q.left_signSum_orthogonal R true,
      Q.signSum_right_orthogonal R false, R.signSum_orthogonal, add_zero]

end OrthogonalProjectionPair

end

def packingEnergy (η : ℝ) (n : ℕ) : ℝ := η * ((1 + 1000 * η) ^ n - 1)

def packingRemainder (η : ℝ) (n : ℕ) : ℝ :=
  (1 - η) ^ n + 3 * n * η ^ 2 + 3 * packingEnergy η n

def packingBalance (η : ℝ) (n : ℕ) : ℝ :=
  n * (7 * η ^ 2 + 2 * η * Real.sqrt (60 * packingEnergy η n + 75 * η))

@[simp] lemma packingEnergy_zero (η : ℝ) : packingEnergy η 0 = 0 := by simp [packingEnergy]

@[simp] lemma packingRemainder_zero (η : ℝ) : packingRemainder η 0 = 1 := by simp [packingRemainder]

@[simp] lemma packingBalance_zero (η : ℝ) : packingBalance η 0 = 0 := by simp [packingBalance]

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [CStarAlgebra D]

def mapUnitary (ι : A →⋆ₐ[ℂ] D) (x : unitary A) : unitary D :=
  ⟨ι (x : A), Unitary.map_mem ι x.property⟩

@[simp] lemma mapUnitary_coe (ι : A →⋆ₐ[ℂ] D) (x : unitary A) :
    (mapUnitary ι x : D) = ι (x : A) := rfl

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.FinitePacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [CStarAlgebra D]

variable [PartialOrder D] [StarOrderedRing D]

namespace OrthogonalProjectionPair

def zero : OrthogonalProjectionPair D where
  left := 0
  right := 0
  left_projection := IsStarProjection.zero D
  right_projection := IsStarProjection.zero D
  orthogonal := mul_zero 0

end OrthogonalProjectionPair

structure PackingBounds (ι : A →⋆ₐ[ℂ] D) (Q : OrthogonalProjectionPair D)
    (K : Finset (unitary A)) (η : ℝ) (n : ℕ) : Prop where
  energy : ∀ x ∈ K, ∀ τ : Pureness.TracialState D, Q.energy τ (ι (x : A)) ≤ packingEnergy η n
  remaining : ∀ τ : Pureness.TracialState D, Q.remaining τ ≤ packingRemainder η n
  balance : ∀ x ∈ K, ∀ τ : Pureness.TracialState D, Q.balance τ (ι (x : A)) ≤ packingBalance η n

end

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.TensorNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uN uR


section

noncomputable section

namespace Pureness

namespace CStarAlgebraNorm

variable {R : Type uR} [Ring R] [StarRing R] [Algebra ℂ R]

def ofFaithful {N : Type uN} [CStarAlgebra N]
    (f : R →⋆ₐ[ℂ] N) (hf : Function.Injective f) : CStarAlgebraNorm R where
  toFun x := ‖f x‖
  map_zero' := by simp
  add_le' x y := by simpa only [map_add] using norm_add_le (f x) (f y)
  neg' x := by simp
  mul_le' x y := by simpa only [map_mul] using norm_mul_le (f x) (f y)
  eq_zero_of_map_eq_zero' x hx := hf (by simpa using norm_eq_zero.mp hx)
  smul' c x := by simp [norm_smul]
  cstar x := by
    change ‖f (star x * x)‖ = ‖f x‖ * ‖f x‖
    rw [map_mul, map_star, CStarRing.norm_star_mul_self]

@[simp] lemma ofFaithful_apply {N : Type uN} [CStarAlgebra N]
    (f : R →⋆ₐ[ℂ] N) (hf : Function.Injective f) (x : R) :
    (ofFaithful f hf).toAlgebraNorm x = ‖f x‖ := rfl

end CStarAlgebraNorm

open scoped TensorProduct

universe u v

variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

theorem IsNuclear.faithful_tensor_norm_eq (hA : IsNuclear.{u, v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g) (z : A ⊗[ℂ] B) :
    ‖f z‖ = ‖g z‖ := by
  have he := (hA B).elim (CStarAlgebraNorm.ofFaithful f hf)
    (CStarAlgebraNorm.ofFaithful g hg)
  exact congrArg (fun p : CStarAlgebraNorm (A ⊗[ℂ] B) => p.toAlgebraNorm z) he

end Pureness

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uD uE uI uJ uX

namespace Pureness

open Filter

open scoped Topology NNReal ENNReal

namespace ClosedStarIdeal

variable {D : Type uD} [CStarAlgebra D] (J : ClosedStarIdeal D)

def quotientStarHom : D →⋆ₐ[ℂ] J.Quotient :=
  { J.quotientMap with map_star' := J.quotientMap_star }

end ClosedStarIdeal

end Pureness

namespace CurrentMain

section

open Pureness

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def familyTraceNorm (a : D) : ℝ := ⨆ i, ‖(τ i).functional a‖

end

open Pureness Filter

open scoped Topology NNReal ENNReal

end CurrentMain

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

omit [Nontrivial D] [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma boundedFamilyConstant_apply {X : Type uX} (a : D) (n : X) :
    boundedFamilyConstant a n = a := rfl

end CurrentMain

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section UltrapowerConstants

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

instance familyUltrapowerNontrivial : Nontrivial (FamilyUltrapower τ U) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he := congrArg (familyLimitTrace τ U (fun _ => i)).functional h
  rw [(familyLimitTrace τ U (fun _ => i)).normalized, map_zero] at he
  exact one_ne_zero he

end UltrapowerConstants

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SimpleIdeals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uC uι

namespace Pureness

section

open Filter Topology

variable {A : Type uA} [NormedRing A]

def closedTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (closure (I : Set A))
    (subset_closure I.zero_mem)
    (by
      intro x y hx hy
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
      exact isClosed_closure.mem_of_tendsto (hux.add hvy)
        (Eventually.of_forall fun j => subset_closure (I.add_mem (hu j) (hv j))))
    (by
      intro x hx
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      exact isClosed_closure.mem_of_tendsto hux.neg
        (Eventually.of_forall fun j => subset_closure (I.neg_mem (hu j))))
    (by
      intro x y hy
      obtain ⟨u, hu, huy⟩ := mem_closure_iff_seq_limit.mp hy
      exact isClosed_closure.mem_of_tendsto (huy.const_mul x)
        (Eventually.of_forall fun j => subset_closure (I.mul_mem_left x (u j) (hu j))))
    (by
      intro x y hx
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      exact isClosed_closure.mem_of_tendsto (hux.mul_const y)
        (Eventually.of_forall fun j => subset_closure (I.mul_mem_right (u j) y (hu j))))

@[simp] theorem coe_closedTwoSidedIdeal (I : TwoSidedIdeal A) :
    (closedTwoSidedIdeal I : Set A) = closure (I : Set A) := by
  simp [closedTwoSidedIdeal]

end

section

variable {A : Type uA} [Ring A]

def finiteIdealSum (h : A) (l : List (A × A)) : A :=
  (l.map fun p => p.1 * h * p.2).sum

end

section

open scoped ComplexOrder ENNReal NNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def normalizePositive (a : A) : A := ‖a‖⁻¹ • a

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma normalizePositive_zero : normalizePositive (0 : A) = 0 := by
  simp [normalizePositive]

noncomputable def normalizedRoot (a : A) (j : ℕ) : A :=
  CFC.nnrpow (normalizePositive a) (((j : ℝ≥0) + 1)⁻¹)

noncomputable def normalizedRootRank (τ : TracialState A) (a : A) : ℝ≥0∞ :=
  ⨆ j : ℕ, ENNReal.ofReal (τ.functional (normalizedRoot a j)).re

end

open Filter Topology

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def sandwichSubalgebra (h : A) (hh : 0 ≤ h) : NonUnitalStarSubalgebra ℝ A where
  carrier := Set.range (fun w : A => h * w * h)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by noncomm_ring⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * h * h * y, by simp only [mul_assoc]⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨star x, by simp only [star_mul, hh.star_eq, mul_assoc]⟩

noncomputable def hereditarySubalgebra (h : A) (hh : 0 ≤ h) : NonUnitalStarSubalgebra ℝ A :=
  (sandwichSubalgebra h hh).topologicalClosure

def hereditaryCarrier (h : A) : Set A := closure (Set.range (fun w : A => h * w * h))

instance hereditarySubalgebra_closed (h : A) (hh : 0 ≤ h) :
    IsClosed (hereditarySubalgebra h hh : Set A) := isClosed_closure

end Pureness

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.OrthogonalElements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uB

open Filter Topology

namespace Pureness

variable {B : Type uB} [NonUnitalNormedRing B] [StarRing B]

def CuntzSubequiv (a b : B) : Prop :=
  a ∈ closure (Set.range fun v : B => star v * b * v)

end Pureness

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.FullProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD

open Filter Topology

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

namespace ClosedSelfAdjointSpan

variable {D : Type uD} [CStarAlgebra D]

lemma span_star_mem {g x : D} (hg : IsSelfAdjoint g)
    (hx : x ∈ TwoSidedIdeal.span {g}) : star x ∈ TwoSidedIdeal.span {g} := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx,hg.star_eq]
    exact TwoSidedIdeal.subset_span (Set.mem_singleton g)
  | zero => simp
  | add x y _ _ hx hy => simpa only [star_add] using (TwoSidedIdeal.span {g}).add_mem hx hy
  | neg x _ hx => simpa only [star_neg] using (TwoSidedIdeal.span {g}).neg_mem hx
  | left_absorb a x _ hx =>
    simpa only [star_mul] using (TwoSidedIdeal.span {g}).mul_mem_right (star x) (star a) hx
  | right_absorb a x _ hx =>
    simpa only [star_mul] using (TwoSidedIdeal.span {g}).mul_mem_left (star a) (star x) hx

def ideal {g : D} (hg : IsSelfAdjoint g) : ClosedStarIdeal D where
  ideal := closedTwoSidedIdeal (TwoSidedIdeal.span {g})
  isClosed := by rw [coe_closedTwoSidedIdeal]; exact isClosed_closure
  star_mem := by
    intro x hx
    rw [← SetLike.mem_coe,coe_closedTwoSidedIdeal] at hx ⊢
    obtain ⟨u,hu,hux⟩ := mem_closure_iff_seq_limit.mp hx
    exact isClosed_closure.mem_of_tendsto hux.star
      (Eventually.of_forall fun n => subset_closure (span_star_mem hg (hu n)))

end ClosedSelfAdjointSpan

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.NuclearTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uR uS


section

noncomputable section

universe v

namespace Pureness

namespace NuclearLift

variable (B : Type) [CStarAlgebra B]

instance instStarULift_solutions : Star (ULift.{v} B) := ⟨fun x => ⟨star x.down⟩⟩

instance instStarRingULift_solutions : StarRing (ULift.{v} B) where
  star_involutive x := by apply ULift.down_injective; exact star_star x.down
  star_mul x y := by apply ULift.down_injective; exact star_mul x.down y.down
  star_add x y := by apply ULift.down_injective; exact star_add x.down y.down

instance instStarModuleComplexULift_solutions : StarModule ℂ (ULift.{v} B) where
  star_smul c x := by apply ULift.down_injective; exact star_smul c x.down

instance instCStarRingULift_solutions : CStarRing (ULift.{v} B) where
  norm_mul_self_le x := CStarRing.norm_mul_self_le x.down

instance instCStarAlgebraULift_solutions : CStarAlgebra (ULift.{v} B) where

end NuclearLift

namespace CStarAlgebraNorm

variable {R : Type uR} {S : Type uS} [Ring R] [StarRing R] [Algebra ℂ R]
  [Ring S] [StarRing S] [Algebra ℂ S]

def comapEquiv (p : CStarAlgebraNorm S) (e : R ≃⋆ₐ[ℂ] S) : CStarAlgebraNorm R where
  toFun x := p.toAlgebraNorm (e x)
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact map_add_le_add p.toAlgebraNorm (e x) (e y)
  neg' x := by simp
  mul_le' x y := by rw [map_mul]; exact map_mul_le_mul p.toAlgebraNorm (e x) (e y)
  eq_zero_of_map_eq_zero' x hx := e.injective (by simpa using p.toAlgebraNorm.eq_zero_of_map_eq_zero' (e x) hx)
  smul' scalar element := by rw [map_smul, map_smul_eq_mul]
  cstar x := by
    change p.toAlgebraNorm (e (star x*x)) = p.toAlgebraNorm (e x)*p.toAlgebraNorm (e x)
    rw [map_mul,map_star]
    exact p.cstar (e x)

end CStarAlgebraNorm

open scoped TensorProduct

end Pureness

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.TensorExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uR

noncomputable section

namespace Pureness

section

open scoped CStarAlgebra

variable {R : Type uR} {E : Type uE} {F : Type uF} [Ring R] [StarAddMonoid R] [Algebra ℂ R]

variable [CStarAlgebra E] [CStarAlgebra F]

variable (f : R →⋆ₐ[ℂ] E) (g : R →⋆ₐ[ℂ] F)

variable (hf : DenseRange f) (hn : ∀ x, ‖g x‖ ≤ ‖f x‖)

def denseStarCompletionHom : E →⋆ₐ[ℂ] F := by
  let L : E →L[ℂ] F := g.toLinearMap.extendOfNorm f.toLinearMap
  have heq (x : R) : L (f x) = g x :=
    LinearMap.extendOfNorm_eq hf ⟨1, fun element => by
      simpa only [AlgHom.toLinearMap_apply, StarAlgHom.coe_toAlgHom, one_mul] using hn element⟩ x
  exact {
    toFun := L
    map_zero' := L.map_zero
    map_add' := L.map_add
    map_one' := by rw [← map_one f, heq, map_one]
    map_mul' := by
      refine hf.induction_on₂ ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_mul)
          ((L.continuous.comp continuous_fst).mul (L.continuous.comp continuous_snd))
      · intro x y
        change L (f x * f y) = L (f x) * L (f y)
        rw [← map_mul, heq, heq, heq, map_mul]
    commutes' := by
      intro c
      rw [← f.commutes]
      change L (f (algebraMap ℂ R c)) = _
      rw [heq]
      exact g.commutes c
    map_star' := by
      intro x
      refine hf.induction_on x ?_ ?_
      · exact isClosed_eq (L.continuous.comp continuous_star) L.continuous.star
      · intro y
        rw [← map_star, heq, heq, map_star] }

end

open scoped TensorProduct

universe u v

variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

theorem IsNuclear.representation_norm_le (hA : IsNuclear.{u,v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (z : A ⊗[ℂ] B) : ‖g z‖ ≤ ‖f z‖ := by
  let k := f.prod g
  have hk : Function.Injective k := by
    intro x y h
    apply hf
    exact congrArg Prod.fst h
  have hn := hA.faithful_tensor_norm_eq f k hf hk z
  change ‖f z‖ = ‖(f z,g z)‖ at hn
  rw [Prod.norm_def] at hn
  exact (le_max_right _ _).trans_eq hn.symm

def IsNuclear.extendRepresentation (hA : IsNuclear.{u,v} A)
    {E : Type uE} {F : Type uF} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hfd : DenseRange f) : E →⋆ₐ[ℂ] F :=
  denseStarCompletionHom f g hfd (hA.representation_norm_le f g hf)

end Pureness

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.GNSRepresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uE uH uN


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

namespace Pureness

open scoped TensorProduct

variable {A : Type uA} {B : Type uB} {N : Type uN} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra N]

def commutingStarTensorHom (φ : A →⋆ₐ[ℂ] N) (ψ : B →⋆ₐ[ℂ] N)
    (hc : ∀ a b, Commute (φ a) (ψ b)) : A ⊗[ℂ] B →⋆ₐ[ℂ] N :=
  { Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom hc with
    map_star' := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | (rw [UniformSpace.Completion.coe_zero]; exact zero_mem _) | simp
      | tmul a b =>
        change φ (star a)*ψ (star b) = star (φ a*ψ b)
        rw [star_mul,← map_star,← map_star]
        exact (hc (star a) (star b)).eq
      | add z w hz hw =>
        let L := Algebra.TensorProduct.lift φ.toAlgHom ψ.toAlgHom hc
        change L (star z) = star (L z) at hz
        change L (star w) = star (L w) at hw
        change L (star (z+w)) = star (L (z+w))
        rw [star_add,map_add,map_add,hz,hw,star_add] }

end Pureness

namespace NuclearTrace

open scoped TensorProduct ComplexOrder InnerProductSpace

section VectorFunctional

variable {E : Type uE} {H : Type uH} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorFunctional (π : E →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : E →ₚ[ℂ] ℂ where
  toFun x := ⟪ξ, π x ξ⟫_ℂ
  map_add' x y := by simp
  map_smul' c x := by simp
  monotone' := by
    intro a b hab
    have h := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
      (map_nonneg π (sub_nonneg.mpr hab))).inner_nonneg_right ξ
    simpa only [map_sub,sub_apply,inner_sub_right,sub_nonneg] using h

@[simp] lemma vectorFunctional_apply (π : E →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : E) :
    vectorFunctional π ξ a = ⟪ξ, π a ξ⟫_ℂ := rfl

end VectorFunctional

end NuclearTrace

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.StateExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uB uE

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace CurrentMain

open scoped ComplexOrder ComplexStarModule

variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

def selfAdjointFunctionalComplex (f : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (f (ℜ a) : ℂ) + Complex.I * (f (ℑ a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
def selfAdjointEmbedding (ι : A →⋆ₐ[ℂ] B) (hi : Function.Injective ι) :
    selfAdjoint A →ₗᵢ[ℝ] selfAdjoint B where
  toFun a := ⟨ι a,by change star (ι a) = ι a; rw [← map_star,a.property.star_eq]⟩
  map_add' a b := Subtype.ext (map_add ι (a : A) (b : A))
  map_smul' c a := Subtype.ext (by
    change ι (c • (a : A)) = c • ι a
    rw [← Complex.coe_smul, map_smul, Complex.coe_smul])
  norm_map' a := (NonUnitalStarAlgHom.isometry ι hi).norm_map_of_map_zero (map_zero ι) (a : A)

omit [PartialOrder B] [StarOrderedRing B] in
lemma state_realPart_bound (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) (a : selfAdjoint A) :
    |(f a).re| ≤ ‖a‖ := by
  have hu (b : selfAdjoint A) : (f b).re ≤ ‖b‖ := by
    have h := f.apply_le_of_isSelfAdjoint b b.property
    have he : f (algebraMap ℝ A ‖(b : A)‖) = (‖b‖ : ℂ) := by
      rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, hf]
      simp
    rw [he] at h
    exact h.1
  refine abs_le.mpr ⟨?_,hu a⟩
  have h := hu (-a)
  change (f (-(a : A))).re ≤ ‖-a‖ at h
  simp only [map_neg,Complex.neg_re,norm_neg] at h
  linarith

omit [PartialOrder B] [StarOrderedRing B] in
def stateRealLinear (f : A →ₚ[ℂ] ℂ) : selfAdjoint A →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp
    (((f : A →ₗ[ℂ] ℂ).restrictScalars ℝ).comp (selfAdjoint.submodule ℝ A).subtype)

omit [PartialOrder B] [StarOrderedRing B] in
def stateRealContinuous (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : selfAdjoint A →L[ℝ] ℝ :=
  (stateRealLinear f).mkContinuous 1 (fun a => by
    change |(f a).re| ≤ 1 * ‖a‖
    simpa only [one_mul] using state_realPart_bound f hf a)

end CurrentMain

open scoped ComplexOrder InnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpatialTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uB uE uF uH uK uι


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

namespace UnitalTomsWinter

variable {H : Type uH} {K : Type uK} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

abbrev SpatialHilbert (H : Type uH) (K : Type uK) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  UniformSpace.Completion (H ⊗[ℂ] K)

def spatialTensorOp (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    SpatialHilbert H K →L[ℂ] SpatialHilbert H K :=
  (TensorProduct.mapL S T).completion

@[simp] lemma spatialTensorOp_coe (S : H →L[ℂ] H) (T : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    spatialTensorOp S T x = (TensorProduct.mapL S T x : SpatialHilbert H K) := by
  exact (TensorProduct.mapL S T).completion_apply_coe x

lemma spatialTensorOp_ext {S T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K}
    (h : ∀ x : H, ∀ y : K, S (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) = T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)) : S = T := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih z =>
    induction z using TensorProduct.induction_on with
    | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | (rw [UniformSpace.Completion.coe_zero]; exact zero_mem _) | simp
    | tmul x y => exact h x y
    | add x y hx hy => simpa [coe_add] using congrArg₂ (· + ·) hx hy

@[simp] lemma spatialTensorOp_zero_left (T : K →L[ℂ] K) : spatialTensorOp (0 : H →L[ℂ] H) T = 0 := by
  apply spatialTensorOp_ext; intro x y; simp

@[simp] lemma spatialTensorOp_zero_right (S : H →L[ℂ] H) : spatialTensorOp S (0 : K →L[ℂ] K) = 0 := by
  apply spatialTensorOp_ext; intro x y; simp

lemma spatialTensorOp_add_left (S₁ S₂ : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (S₁+S₂) T = spatialTensorOp S₁ T + spatialTensorOp S₂ T := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.add_tmul, coe_add]

lemma spatialTensorOp_add_right (S : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp S (T₁+T₂) = spatialTensorOp S T₁ + spatialTensorOp S T₂ := by
  apply spatialTensorOp_ext; intro x y; simp [TensorProduct.tmul_add, coe_add]

lemma spatialTensorOp_smul_left (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (c • S) T = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, smul_apply]
  rw [← TensorProduct.smul_tmul', coe_smul]

lemma spatialTensorOp_smul_right (c : ℂ) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp S (c • T) = c • spatialTensorOp S T := by
  apply spatialTensorOp_ext; intro x y; simp

lemma spatialTensorOp_mul (S₁ S₂ : H →L[ℂ] H) (T₁ T₂ : K →L[ℂ] K) :
    spatialTensorOp (S₁*S₂) (T₁*T₂) = spatialTensorOp S₁ T₁ * spatialTensorOp S₂ T₂ := by
  apply spatialTensorOp_ext; intro x y; simp

variable [CompleteSpace H] [CompleteSpace K]

lemma spatialTensorOp_star (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    spatialTensorOp (star S) (star T) = star (spatialTensorOp S T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    induction x using TensorProduct.induction_on with
    | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | (rw [UniformSpace.Completion.coe_zero]; exact zero_mem _) | simp
    | add x₁ x₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
    | tmul x₁ x₂ =>
      induction y using TensorProduct.induction_on with
      | zero => first | (simp only [map_zero]; done) | (simp only [UniformSpace.Completion.coe_zero, map_zero]; done) | (rw [UniformSpace.Completion.coe_zero]; exact zero_mem _) | simp
      | add y₁ y₂ h₁ h₂ => simpa [coe_add, inner_add_left, inner_add_right] using congrArg₂ (· + ·) h₁ h₂
      | tmul y₁ y₂ => simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

end UnitalTomsWinter

noncomputable section

namespace Pureness

open UnitalTomsWinter

open scoped TensorProduct InnerProductSpace

variable {A : Type uA} {B : Type uB} {H : Type uH} {K : Type uK} [CStarAlgebra A] [CStarAlgebra B]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialTensorOp_one : spatialTensorOp (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply spatialTensorOp_ext
  intro x y
  simp

def spatialLeftHom : A →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun a := spatialTensorOp (α a) 1
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_left]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_left,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' a := by rw [map_star,← spatialTensorOp_star,star_one]

def spatialRightHom : B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) where
  toFun b := spatialTensorOp 1 (β b)
  map_zero' := by simp
  map_one' := by rw [map_one,spatialTensorOp_one]
  map_add' a b := by rw [map_add,spatialTensorOp_add_right]
  map_mul' a b := by rw [map_mul,← spatialTensorOp_mul,mul_one]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,spatialTensorOp_smul_right,
      spatialTensorOp_one,Algebra.algebraMap_eq_smul_one]
  map_star' b := by rw [map_star,← spatialTensorOp_star,star_one]

lemma spatialLeftRight_commute (a : A) (b : B) :
    Commute (spatialLeftHom (K := K) α a) (spatialRightHom (H := H) β b) := by
  change spatialTensorOp (α a) 1 * spatialTensorOp 1 (β b) =
    spatialTensorOp 1 (β b) * spatialTensorOp (α a) 1
  rw [← spatialTensorOp_mul,← spatialTensorOp_mul]
  simp

def spatialStarTensorHom :
    A ⊗[ℂ] B →⋆ₐ[ℂ] (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
  commutingStarTensorHom (N := SpatialHilbert H K →L[ℂ] SpatialHilbert H K) (spatialLeftHom (K := K) α) (spatialRightHom (H := H) β) (spatialLeftRight_commute α β)

end Pureness

end

end

end

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.FaithfulRepresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uH uα uι


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

namespace Pureness

open scoped ComplexOrder InnerProductSpace

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def stateGNSVector (f : A →ₚ[ℂ] ℂ) : f.GNS := f.toPreGNS 1

end Pureness

noncomputable section

noncomputable section

namespace Pureness

open scoped InnerProductSpace ENNReal

variable {A : Type uA} {ι : Type uι} [CStarAlgebra A] {H : ι → Type uH}

variable [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]

variable [∀ i, CompleteSpace (H i)]

variable (ρ : ∀ i, A →⋆ₐ[ℂ] (H i →L[ℂ] H i))

def hilbertSumAction (a : A) (x : lp H 2) : lp H 2 :=
  ⟨fun i => ρ i a (x i), ((lp.memℓp x).norm.const_mul ‖a‖).mono (fun i =>
    ((ρ i a).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le (ρ i).toNonUnitalStarAlgHom a) (norm_nonneg _)))⟩

lemma hilbertSumAction_norm_le (a : A) (x : lp H 2) :
    ‖hilbertSumAction ρ a x‖ ≤ ‖a‖ * ‖x‖ := by
  let y : lp H 2 := (‖a‖ : ℂ) • x
  have hy : ∀ i, ‖hilbertSumAction ρ a x i‖ ≤ ‖y i‖ := by
    intro i
    change ‖ρ i a (x i)‖ ≤ ‖(‖a‖ : ℂ) • x i‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
    exact ((ρ i a).le_opNorm (x i)).trans (mul_le_mul_of_nonneg_right
      (NonUnitalStarAlgHom.norm_apply_le (ρ i).toNonUnitalStarAlgHom a) (norm_nonneg _))
  have hn := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hy
  change ‖hilbertSumAction ρ a x‖ ≤ ‖(‖a‖ : ℂ) • x‖ at hn
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)] at hn
  exact hn

def hilbertSumOperator (a : A) : lp H 2 →L[ℂ] lp H 2 :=
  LinearMap.mkContinuous
    { toFun := hilbertSumAction ρ a
      map_add' := fun x y => by apply lp.ext; funext i; exact (ρ i a).map_add _ _
      map_smul' := fun c x => by apply lp.ext; funext i; exact (ρ i a).map_smul c _ }
    ‖a‖ (hilbertSumAction_norm_le ρ a)

def hilbertSumRepresentation : A →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun := hilbertSumOperator ρ
  map_zero' := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_zero (ρ i))
  map_one' := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_one (ρ i))
  map_add' a b := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_add (ρ i) a b)
  map_mul' a b := by ext x i; exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) (map_mul (ρ i) a b)
  commutes' c := by
    ext x i
    exact congrArg (fun f : H i →L[ℂ] H i => f (x i)) ((ρ i).commutes c)
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    change ⟪ρ i (star a) (x i), y i⟫_ℂ = ⟪x i, ρ i a (y i)⟫_ℂ
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

end Pureness

noncomputable section

namespace Pureness

open scoped InnerProductSpace ComplexOrder

local instance instDecidableEq_solutions_rb5fe56_1 {α : Type uα} : DecidableEq α := Classical.decEq α
variable (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def PositiveStateIndex := {f : A →ₚ[ℂ] ℂ // f 1 = 1}

abbrev UniversalStateHilbert := lp (fun f : PositiveStateIndex A => f.1.GNS) 2

def universalStateGNS : A →⋆ₐ[ℂ]
    (UniversalStateHilbert A →L[ℂ] UniversalStateHilbert A) :=
  hilbertSumRepresentation (fun f : PositiveStateIndex A => f.1.gnsStarAlgHom)

end Pureness

noncomputable section

namespace Pureness

variable (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[instance_reducible]
def universalStateHilbertNormedAddCommGroup :
    NormedAddCommGroup (UniversalStateHilbert A) := inferInstance

attribute [local instance] universalStateHilbertNormedAddCommGroup

@[instance_reducible]
def universalStateHilbertInnerProductSpace :
    InnerProductSpace ℂ (UniversalStateHilbert A) := inferInstance

end Pureness

noncomputable section

namespace Pureness

variable (A : Type uA) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def StateHilbertSpace := UniversalStateHilbert A

instance stateHilbertNormedAddCommGroup : NormedAddCommGroup (StateHilbertSpace A) :=
  inferInstanceAs (NormedAddCommGroup (UniversalStateHilbert A))

instance stateHilbertInnerProductSpace : InnerProductSpace ℂ (StateHilbertSpace A) :=
  inferInstanceAs (InnerProductSpace ℂ (UniversalStateHilbert A))

instance stateHilbertCompleteSpace : CompleteSpace (StateHilbertSpace A) :=
  inferInstanceAs (CompleteSpace (UniversalStateHilbert A))

def stateHilbertRepresentation : A →⋆ₐ[ℂ]
    (StateHilbertSpace A →L[ℂ] StateHilbertSpace A) :=
  universalStateGNS A

end Pureness

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.VectorApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uH uI uV

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

namespace NuclearTrace

section

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (f g : A →ₚ[ℂ] ℂ) {C : ℝ} (hC : 0 ≤ C)

variable (hfg : ∀ a : A, 0 ≤ a → (g a).re ≤ C * (f a).re)

include hfg hC in
lemma domination_preGNS_norm (a : A) :
    ‖g.toPreGNS a‖ ≤ Real.sqrt C * ‖f.toPreGNS a‖ := by
  simp only [PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.ofPreGNS_toPreGNS]
  rw [← Real.sqrt_mul hC]
  exact Real.sqrt_le_sqrt (hfg _ (star_mul_self_nonneg a))

def dominationPreGNS : f.PreGNS →L[ℂ] g.PreGNS :=
  (g.toPreGNS.toLinearMap.comp f.ofPreGNS.toLinearMap).mkContinuous
    (Real.sqrt C) (fun x => by
      simpa using domination_preGNS_norm f g hC hfg (f.ofPreGNS x))

@[simp] lemma dominationPreGNS_apply (x : f.PreGNS) :
    dominationPreGNS f g hC hfg x = g.toPreGNS (f.ofPreGNS x) := rfl

def dominationGNS : f.GNS →L[ℂ] g.GNS :=
  (dominationPreGNS f g hC hfg).completion

@[simp] lemma dominationGNS_coe (x : f.PreGNS) :
    dominationGNS f g hC hfg (x : f.GNS) = (g.toPreGNS (f.ofPreGNS x) : g.GNS) := by
  simp [dominationGNS]

def dominationDensity : f.GNS →L[ℂ] f.GNS :=
  (dominationGNS f g hC hfg).adjoint.comp (dominationGNS f g hC hfg)

end

open scoped ComplexStarModule

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def selfAdjointComplexification (l : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (l (ℜ a) : ℂ) + Complex.I * (l (ℑ a) : ℂ)
  map_add' a b := by simp only [map_add,Complex.ofReal_add]; ring
  map_smul' z a := by
    simp only [realPart_smul,imaginaryPart_smul,map_sub,map_add,map_smul,
      Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,smul_eq_mul]
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]

omit [PartialOrder A] [StarOrderedRing A] in
lemma selfAdjointComplexification_apply (l : selfAdjoint A →ₗ[ℝ] ℝ)
    (a : selfAdjoint A) : selfAdjointComplexification l a = (l a : ℂ) := by
  simp [selfAdjointComplexification]

variable (f : A →ₚ[ℂ] ℂ) (l : selfAdjoint A →ₗ[ℝ] ℝ) (C : ℝ)

variable (hl : ∀ a : selfAdjoint A, 0 ≤ (a : A) → |l a| ≤ C * (f a).re)

include hl in
lemma real_perturbation_nonneg {a : A} (ha : 0 ≤ a) :
    0 ≤ (C : ℂ) • f a + selfAdjointComplexification l a := by
  have hc := hl ⟨a,ha.isSelfAdjoint⟩ ha
  have he : selfAdjointComplexification l a = (l ⟨a,ha.isSelfAdjoint⟩ : ℂ) :=
    selfAdjointComplexification_apply l ⟨a,ha.isSelfAdjoint⟩
  rw [he]
  have hf := f.map_nonneg ha
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
    linarith [neg_abs_le (l ⟨a,ha.isSelfAdjoint⟩)]
  · simp only [smul_eq_mul,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,← hf.2,Complex.zero_im,mul_zero,zero_mul,add_zero]

def realPerturbation : A →ₚ[ℂ] ℂ where
  toLinearMap := (C : ℂ) • f.toLinearMap + selfAdjointComplexification l
  monotone' := by
    intro a b hab
    have h := real_perturbation_nonneg f l C hl (sub_nonneg.mpr hab)
    simp only [map_sub,smul_sub] at h
    change (C : ℂ) • f a + selfAdjointComplexification l a ≤
      (C : ℂ) • f b + selfAdjointComplexification l b
    exact sub_nonneg.mp (by convert h using 1; ring)

end NuclearTrace

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.CoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uE uK uN


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

namespace NuclearTrace

section Coefficients

variable {A : Type uA} {K : Type uK} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))

variable {N : Type uN} [Fintype N] (k : N → K) (a : N → A)

def coefficientMap : A →ₗ[ℂ] A where
  toFun x := ∑ i, ∑ j, (⟪k i,α x (k j)⟫_ℂ) • (star (a i)*a j)
  map_add' x y := by
    simp [map_add,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by
    simp [smul_smul,Finset.smul_sum]

lemma coefficientMap_star (x : A) :
    star (coefficientMap α k a x) = coefficientMap α k a (star x) := by
  classical
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,star_sum,star_smul,
    star_mul,star_star,map_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun c : ℂ => c • (star (a i)*a j)) (inner_conj_symm _ _)

lemma coefficientMap_selfAdjoint (x : A) (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (coefficientMap α k a x) := by
  exact (coefficientMap_star α k a x).trans (congrArg _ hx.star_eq)

end Coefficients

section GNSDensity

variable {A : Type uA} {K : Type uK} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (f : A →ₚ[ℂ] ℂ)

def algebraTensorVector : K ⊗[ℂ] A →ₗ[ℂ] SpatialHilbert K f.GNS :=
  toComplₗᵢ.toLinearMap.comp (TensorProduct.map (LinearMap.id : K →ₗ[ℂ] K)
    (toComplₗᵢ.toLinearMap.comp f.toPreGNS.toLinearMap))

@[simp] lemma algebraTensorVector_tmul (k : K) (a : A) :
    algebraTensorVector (K := K) f (k ⊗ₜ[ℂ] a) =
      ((k ⊗ₜ[ℂ] (f.toPreGNS a : f.GNS) : K ⊗[ℂ] f.GNS) : SpatialHilbert K f.GNS) := rfl

end GNSDensity

end NuclearTrace

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

noncomputable section

open scoped Pointwise

noncomputable section

open scoped ComplexOrder

namespace CurrentMain

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma traceOneNorm_smul_real (τ : Pureness.TracialState A) (c : ℝ) (a : A) :
    traceOneNorm τ (c • a) = ‖c‖ * traceOneNorm τ a := by
  simp [traceOneNorm,CFC.abs_smul,τ.functional.map_smul_of_tower]

def tracialOneSeminorm (τ : Pureness.TracialState A) : Seminorm ℝ (selfAdjoint A) where
  toFun a := traceOneNorm τ a
  map_zero' := by simp [traceOneNorm]
  neg' a := traceOneNorm_neg τ a
  add_le' a b := traceOneNorm_add_le τ a.property b.property
  smul' c a := traceOneNorm_smul_real τ c a

@[simp] lemma tracialOneSeminorm_apply (τ : Pureness.TracialState A) (a : selfAdjoint A) :
    tracialOneSeminorm τ a = traceOneNorm τ a := rfl

end CurrentMain

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.CoefficientApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

noncomputable section

open scoped Pointwise

noncomputable section

open scoped ComplexOrder

noncomputable section

open scoped ComplexOrder

namespace NuclearTrace

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

def coefficientSelfAdjMap (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (k : Fin n → K) (a : Fin n → A) : selfAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun x := ⟨coefficientMap α k a x,coefficientMap_selfAdjoint α k a _ x.property⟩
  map_add' left right := Subtype.ext ((coefficientMap α k a).map_add left right)
  map_smul' scalar value :=
    Subtype.ext ((coefficientMap α k a).map_smul_of_tower scalar (value : A))

def coefficientCone (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ConvexCone ℝ (selfAdjoint A →ₗ[ℝ] selfAdjoint A) :=
  ConvexCone.hull ℝ {L | ∃ (n : ℕ) (k : Fin n → K) (a : Fin n → A),
    L = coefficientSelfAdjMap α k a}

def evalTuple (x : I → selfAdjoint A) :
    (selfAdjoint A →ₗ[ℝ] selfAdjoint A) →ₗ[ℝ] (I → selfAdjoint A) where
  toFun L i := L (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tracialTupleSeminorm (τ : Pureness.TracialState A) :
    Seminorm ℝ (I → selfAdjoint A) :=
  ∑ i, (CurrentMain.tracialOneSeminorm τ).comp (LinearMap.proj i)

@[simp] lemma tracialTupleSeminorm_apply (τ : Pureness.TracialState A)
    (x : I → selfAdjoint A) :
    tracialTupleSeminorm τ x = ∑ i, CurrentMain.traceOneNorm τ (x i) := by
  simp [tracialTupleSeminorm]

end NuclearTrace

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.TraceNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

open scoped Pointwise

open scoped ComplexOrder

open scoped ComplexOrder

namespace Pureness

section

open scoped ComplexOrder

open Topology

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def TracialState.toWeakDual (τ : TracialState A) : WeakDual ℂ A :=
  StrongDual.toWeakDual
    { toLinearMap := τ.functional.toLinearMap, cont := map_continuous τ.functional }

@[simp] lemma TracialState.toWeakDual_apply (τ : TracialState A) (a : A) :
    τ.toWeakDual a = τ.functional a := rfl

noncomputable instance instTopologicalSpaceTracialState : TopologicalSpace (TracialState A) :=
  TopologicalSpace.induced TracialState.toWeakDual inferInstance

noncomputable def tracialStateCarrier : Set (WeakDual ℂ A) :=
  {f | f 1 = 1 ∧ (∀ a, 0 ≤ a → 0 ≤ f a) ∧ ∀ a b, f (a * b) = f (b * a)}

noncomputable def tracialStateFromWeakDual (f : WeakDual ℂ A) (hf : f ∈ tracialStateCarrier) :
    TracialState A where
  functional :=
    { f.toStrongDual.toLinearMap with
      monotone' := by
        intro a b hab
        change f a ≤ f b
        apply sub_nonneg.mp
        rw [← map_sub]
        exact hf.2.1 (b - a) (sub_nonneg.mpr hab) }
  normalized := hf.1
  tracial := hf.2.2

end

open scoped ComplexOrder

end Pureness

namespace NuclearTrace

open scoped ComplexOrder

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

def traceTupleCost (x z : I → selfAdjoint A) : WeakDual ℂ A →ₗ[ℝ] ℝ where
  toFun τ := ∑ i, (τ (CFC.abs ((x i : A) - z i))).re
  map_add' τ ρ := by
    change (∑ i, (τ (CFC.abs ((x i : A) - z i)) + ρ (CFC.abs ((x i : A) - z i))).re) = _
    simp only [Complex.add_re,Finset.sum_add_distrib]
  map_smul' r τ := by
    change (∑ i, (r • τ (CFC.abs ((x i : A) - z i))).re) =
      r • ∑ i, (τ (CFC.abs ((x i : A) - z i))).re
    simp only [Complex.smul_re, Finset.smul_sum]

end NuclearTrace

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.MatrixCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uJ uK uN


section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace NuclearTrace

section Compression

variable {A : Type uA} {K : Type uK} {N : Type uN} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype N] [DecidableEq N]

def operatorMatrix : (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) ≃⋆ₐ[ℂ]
    CStarMatrix N N ℂ :=
  Matrix.toEuclideanCLM.symm.trans CStarMatrix.ofMatrixStarAlgEquiv

def orthonormalLinear (e : N → K) : EuclideanSpace ℂ N →ₗ[ℂ] K :=
  (EuclideanSpace.basisFun N ℂ).toBasis.constr ℂ e

omit [CompleteSpace K] [DecidableEq N] in
@[simp] lemma orthonormalLinear_basis (e : N → K) (i : N) :
    orthonormalLinear e (EuclideanSpace.basisFun N ℂ i) = e i := by
  exact (EuclideanSpace.basisFun N ℂ).toBasis.constr_basis ℂ e i

omit [CompleteSpace K] [DecidableEq N] in
lemma orthonormalLinear_orthonormal (e : N → K) (he : Orthonormal ℂ e) :
    Orthonormal ℂ (orthonormalLinear e ∘ (EuclideanSpace.basisFun N ℂ).toBasis) := by
  convert he using 1
  ext i
  exact orthonormalLinear_basis e i

def orthonormalInclusion (e : N → K) (he : Orthonormal ℂ e) :
    EuclideanSpace ℂ N →ₗᵢ[ℂ] K :=
  (orthonormalLinear e).isometryOfOrthonormal (v := (EuclideanSpace.basisFun N ℂ).toBasis)
    (EuclideanSpace.basisFun N ℂ).orthonormal (orthonormalLinear_orthonormal e he)

omit [CompleteSpace K] [DecidableEq N] in
@[simp] lemma orthonormalInclusion_basis (e : N → K) (he : Orthonormal ℂ e) (i : N) :
    orthonormalInclusion e he (EuclideanSpace.basisFun N ℂ i) = e i := by
  exact orthonormalLinear_basis e i

def compressionMatrix (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (e : N → K)
    (he : Orthonormal ℂ e) : A →ₗ[ℂ] CStarMatrix N N ℂ where
  toFun x := operatorMatrix (((orthonormalInclusion e he).toContinuousLinearMap.adjoint.comp
    (α x)).comp (orthonormalInclusion e he).toContinuousLinearMap)
  map_add' x y := by simp [ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp]
  map_smul' c x := by simp [ContinuousLinearMap.smul_comp]

end Compression

section FiniteSystems

variable {A : Type} [CStarAlgebra A]

structure FiniteCoefficientSystem (A : Type) [CStarAlgebra A] where
  Index : Type
  [finiteIndex : Fintype Index]
  [decidableIndex : DecidableEq Index]
  input : A →ₗ[ℂ] CStarMatrix Index Index ℂ
  input_one : input 1 = 1
  input_norm : ∀ x : A, ‖input x‖ ≤ ‖x‖
  coefficient : Index → A

attribute [instance] FiniteCoefficientSystem.finiteIndex FiniteCoefficientSystem.decidableIndex

section Matrices

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def blockDiagHom : (CStarMatrix I I ℂ × CStarMatrix J J ℂ) →⋆ₐ[ℂ]
    CStarMatrix (I ⊕ J) (I ⊕ J) ℂ where
  toFun T := CStarMatrix.ofMatrix (Matrix.fromBlocks
    (CStarMatrix.ofMatrix.symm T.1) 0 0 (CStarMatrix.ofMatrix.symm T.2))
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := by
    ext i j; cases i <;> cases j <;> simp [CStarMatrix.one_apply,Matrix.fromBlocks]
  map_add' S T := by
    ext i j; cases i <;> cases j <;> simp [CStarMatrix.add_apply,Matrix.fromBlocks]
  map_mul' S T := by
    ext i j
    cases i <;> cases j <;>
      simp [CStarMatrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks]
  commutes' c := by
    ext i j
    cases i <;> cases j <;> simp [Algebra.algebraMap_eq_smul_one,CStarMatrix.smul_apply,
      CStarMatrix.one_apply,Matrix.fromBlocks]
  map_star' T := by
    ext i j; cases i <;> cases j <;> simp [CStarMatrix.star_apply,Matrix.fromBlocks]

end Matrices

section Synthesis

variable {I : Type} [Fintype I]

def matrixSynthesis (a : I → A) : CStarMatrix I I ℂ →ₗ[ℂ] A where
  toFun T := ∑ i, ∑ j, T i j • (star (a i)*a j)
  map_add' S T := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c T := by simp [smul_smul,Finset.smul_sum]

lemma matrixSynthesis_smul (a : I → A) {c : ℝ} (hc : 0 ≤ c) (T : CStarMatrix I I ℂ) :
    matrixSynthesis (fun i => Real.sqrt c • a i) T = c • matrixSynthesis a T := by
  have he (i j : I) : star (Real.sqrt c • a i)*(Real.sqrt c • a j) = c • (star (a i)*a j) := by
    rw [star_smul,star_trivial,smul_mul_smul_comm,Real.mul_self_sqrt hc]
  change (∑ i, ∑ j, T i j • (star (Real.sqrt c • a i)*(Real.sqrt c • a j))) =
    c • (∑ i, ∑ j, T i j • (star (a i)*a j))
  simp only [he,Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => smul_comm (T i j) c (star (a i)*a j)))

end Synthesis

namespace FiniteCoefficientSystem

def output (F : FiniteCoefficientSystem A) : A →ₗ[ℂ] A :=
  (matrixSynthesis F.coefficient).comp F.input

def scale (F : FiniteCoefficientSystem A) (c : ℝ) : FiniteCoefficientSystem A :=
  { F with coefficient := fun i => Real.sqrt c • F.coefficient i }

lemma scale_output (F : FiniteCoefficientSystem A) {c : ℝ} (hc : 0 ≤ c) (x : A) :
    (F.scale c).output x = c • F.output x := matrixSynthesis_smul F.coefficient hc (F.input x)

open scoped Classical in

def add (F G : FiniteCoefficientSystem A) : FiniteCoefficientSystem A where
  Index := F.Index ⊕ G.Index
  finiteIndex := inferInstance
  decidableIndex := inferInstance
  input := blockDiagHom.toLinearMap.comp (F.input.prod G.input)
  input_one := by
    change blockDiagHom (F.input 1,G.input 1) = 1
    rw [F.input_one,G.input_one]
    exact map_one blockDiagHom
  input_norm x := by
    change ‖blockDiagHom (F.input x,G.input x)‖ ≤ ‖x‖
    exact (NonUnitalStarAlgHom.norm_apply_le
      (blockDiagHom (I := F.Index) (J := G.Index)) (F.input x,G.input x)).trans
      (max_le (F.input_norm x) (G.input_norm x))
  coefficient := Sum.elim F.coefficient G.coefficient

lemma add_output (F G : FiniteCoefficientSystem A) (x : A) :
    (F.add G).output x = F.output x + G.output x := by
  classical
  change (∑ i, ∑ j, blockDiagHom (F.input x,G.input x) i j •
    (star (Sum.elim F.coefficient G.coefficient i)*Sum.elim F.coefficient G.coefficient j)) =
    (∑ i, ∑ j, F.input x i j • (star (F.coefficient i)*F.coefficient j)) +
    (∑ i, ∑ j, G.input x i j • (star (G.coefficient i)*G.coefficient j))
  simp [blockDiagHom,Fintype.sum_sum_type,Matrix.fromBlocks]

end FiniteCoefficientSystem

end FiniteSystems

section HullRepresentation

variable {A K : Type} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def finiteSystemCone : ConvexCone ℝ (selfAdjoint A →ₗ[ℝ] selfAdjoint A) where
  carrier := {L | ∃ F : FiniteCoefficientSystem A, ∀ x : selfAdjoint A, (L x : A) = F.output x}
  smul_mem' := by
    intro c hc L hL
    obtain ⟨F,hF⟩ := hL
    refine ⟨F.scale c,fun x => ?_⟩
    change c • (L x : A) = (F.scale c).output x
    rw [hF,F.scale_output hc.le]
  add_mem' := by
    intro L hL M hM
    obtain ⟨F,hF⟩ := hL
    obtain ⟨G,hG⟩ := hM
    refine ⟨F.add G,fun x => ?_⟩
    change (L x : A) + (M x : A) = (F.add G).output x
    rw [hF,hG,F.add_output]

end HullRepresentation

end NuclearTrace

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.PartitionCoupling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uD uI uJ uN uO

namespace CurrentMain

section

open scoped ComplexOrder

section ChoiKraus

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable {N : Type uN} [Fintype N] [DecidableEq N]

open scoped CStarAlgebra

def scalarMatrixUnit (i j : N) : CStarMatrix N N ℂ :=
  CStarMatrix.ofMatrix (Matrix.single i j 1)

omit [Fintype N] in
@[simp] lemma star_scalarMatrixUnit (i j : N) :
    star (scalarMatrixUnit i j) = scalarMatrixUnit j i := by
  change Matrix.conjTranspose (Matrix.single i j (1 : ℂ)) = Matrix.single j i 1
  simp

@[simp] lemma scalarMatrixUnit_mul (i j k : N) :
    scalarMatrixUnit i j * scalarMatrixUnit j k = scalarMatrixUnit i k := by
  apply CStarMatrix.ext
  intro a b
  rw [CStarMatrix.mul_apply]
  change (∑ l : N, Matrix.single i j (1 : ℂ) a l *
    Matrix.single j k (1 : ℂ) l b) = Matrix.single i k (1 : ℂ) a b
  by_cases hia : i = a <;> by_cases hkb : k = b <;> simp [Matrix.single_apply,hia,hkb]

end ChoiKraus

section ScalarMix

variable {D : Type uD} [CStarAlgebra D]

variable {I : Type uI} {O : Type uO} [Fintype I] [Fintype O] [DecidableEq I]

def scalarMix (R : Matrix O I ℂ) (a : I → D) (o : O) : D :=
  ∑ i, R o i • a i

end ScalarMix

end

open Pureness

open scoped ComplexOrder CStarAlgebra

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.TraceConvexity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA


section

noncomputable section

namespace NuclearTrace

open scoped ComplexOrder

def clipScalar (t : ℝ) : ℝ := (Real.sqrt (max t 1))⁻¹

section Algebra

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def rowNormalizer (b : A) : A := cfc clipScalar b

end Algebra

end NuclearTrace

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.KrausApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA


section

noncomputable section

open scoped ComplexOrder

open CurrentMain Pureness

namespace NuclearTrace

section Coefficients

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Fintype I] [DecidableEq I]

def residualCoefficient (i₀ : I) (r : A) (i : I) : A := if i=i₀ then CFC.sqrt r else 0

end Coefficients

section NormalizeSystem

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace FiniteCoefficientSystem

def mass (F : FiniteCoefficientSystem A) : A := ∑ i, star (F.coefficient i)*F.coefficient i

def clip (F : FiniteCoefficientSystem A) : FiniteCoefficientSystem A :=
  { F with coefficient := fun i => F.coefficient i*rowNormalizer F.mass }

def residual (F : FiniteCoefficientSystem A) : A :=
  1-rowNormalizer F.mass*F.mass*rowNormalizer F.mass

def fill (F : FiniteCoefficientSystem A) (i₀ : F.Index) : FiniteCoefficientSystem A :=
  { F with coefficient := residualCoefficient i₀ F.residual }

def normalize (F : FiniteCoefficientSystem A) (i₀ : F.Index) : FiniteCoefficientSystem A :=
  F.clip.add (F.fill i₀)

end FiniteCoefficientSystem

end NormalizeSystem

end NuclearTrace

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.BistochasticTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section

open Pureness

open scoped ComplexOrder

namespace CurrentMain

structure BistochasticTest (A : Type) [CStarAlgebra A] where
  size : ℕ
  coeff : Fin size → A
  col : ∑ i, star (coeff i)*coeff i = 1
  row : ∑ i, coeff i*star (coeff i) = 1

namespace BistochasticTest

variable {A D : Type} [CStarAlgebra A] [CStarAlgebra D]

def map (V : BistochasticTest A) (ι : A →⋆ₐ[ℂ] D) : BistochasticTest D where
  size := V.size
  coeff := fun i => ι (V.coeff i)
  col := by simpa only [map_sum,map_mul,map_star,map_one] using congrArg ι V.col
  row := by simpa only [map_sum,map_mul,map_star,map_one] using congrArg ι V.row

variable [PartialOrder D] [StarOrderedRing D]

def energy (V : BistochasticTest D) (τ : TracialState D) (p : D) : ℝ :=
  ∑ i, traceTwoNorm τ (V.coeff i*p-p*V.coeff i)^2

end BistochasticTest

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.PreparedBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

noncomputable section

open Pureness

open scoped ComplexOrder

namespace CurrentMain

namespace BistochasticTest

variable {A D N : Type} [CStarAlgebra A] [CStarAlgebra D] [Fintype N]

def ofFamily (v : N → A) (hcol : ∑ i, star (v i)*v i = 1)
    (hrow : ∑ i, v i*star (v i) = 1) : BistochasticTest A where
  size := Fintype.card N
  coeff := fun i => v ((Fintype.equivFin N).symm i)
  col := by rw [(Fintype.equivFin N).symm.sum_comp (fun i => star (v i)*v i)]; exact hcol
  row := by rw [(Fintype.equivFin N).symm.sum_comp (fun i => v i*star (v i))]; exact hrow

end BistochasticTest

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.Challenge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The construction certificates are proved here, outside the self-contained challenge.
`main_iff_original` checks that packaging them preserves the original assertion. -/

universe uNuclear

namespace CurrentMain

open Pureness Filter

def OriginalGammaStatement : Prop := ∀
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (_hsimple : TopologicallySimple A) (_hinf : ¬FiniteDimensional ℂ A)
    (_hA : IsNuclear.{0, uNuclear} A) (_hfinite : StablyFinite A)
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
    (_hfree : (U : Filter ℕ) ≤ atTop)
    (_hRR : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U)),
    UniformPropertyGammaAt A U
end CurrentMain

namespace ComparatorModel.CurrentMain

noncomputable section

open Filter

local instance canonicalNorm : Pureness.ClosedStarIdeal.NormConstruction where
  mul_le := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_mul_le
  star_eq := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_star
  square_le := by intros; apply _root_.OAI.Pureness.ClosedStarIdeal.quotient_norm_square_le

local instance canonicalNull : NullConstruction where
  zero := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_zero
  add := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_add <;> assumption
  neg := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_neg; assumption
  star := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_star; assumption
  mul_left := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_mul_left <;> assumption
  mul_right := by intros; apply _root_.OAI.CurrentMain.isFamilyNull_mul_right <;> assumption
  closed := by intros; apply _root_.OAI.CurrentMain.familyNull_isClosed

local instance canonicalCauchy : CauchyConstruction where
  const := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_const
  add := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_add <;> assumption
  star := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_star; assumption
  mul := by intros; apply _root_.OAI.CurrentMain.isFamilyCauchy_mul <;> assumption
  closed := by intros; apply _root_.OAI.CurrentMain.familyCauchyAlgebra_isClosed

local instance canonicalLimit : LimitConstruction where
  tendsto := by intros; apply _root_.OAI.CurrentMain.ultraTraceValue_tendsto

local instance canonicalTrace : TraceConstruction where
  null := by
    intro D I X _ _ _ _ τ _ U s u hu
    apply _root_.OAI.CurrentMain.ultraTrace_null τ U s u
    exact (_root_.OAI.CurrentMain.familyNull_mem τ (U : Filter X) u).mpr hu

end

end ComparatorModel.CurrentMain

end OAI
end


