-- Prove2me | solution 1 for AlgebraicCurve.GluedPic0.mem_closure_mk_pair_of_riemannRoch
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/de448ccf-9ed6-5360-8aa6-79dac633f556

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_AlgebraicCurve_RROpens_exists_forall_hasValue_forall_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq_finset
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_GluedPic0_mem_closure_mk_pair_of_riemannRoch
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"
p2m_attr_erase "simp" "FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

universe u v

open AlgebraicCurve

namespace GenPairH

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v := by
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [map_finsuppSum]
  refine Finset.sum_congr rfl fun v _ => ?_
  show Divisor.degree (Finsupp.single v (D v)) = D v
  rw [Divisor.degree_single, hdeg, Nat.cast_one, mul_one]

theorem single_sub_single_mem_degZero (hdeg : ∀ v : Place K F, v.deg = 1) (P Q : Place K F) :
    (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) ∈ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg]
  simp

theorem sum_smul_single_sub (hdeg : ∀ v : Place K F, v.deg = 1) (D : Divisor K F)
    (hD0 : Divisor.degree D = 0) (P₀ : Place K F) :
    ∑ v ∈ D.support, D v • (Finsupp.single v (1 : ℤ) - Finsupp.single P₀ 1) = D := by
  have h1 : ∑ v ∈ D.support, D v • Finsupp.single v (1 : ℤ) = D := by
    simp_rw [Finsupp.smul_single_one]
    exact Finsupp.sum_single D
  have h2 : ∑ v ∈ D.support, D v = 0 := by rw [← degree_eq_sum hdeg D, hD0]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, h1, h2, zero_smul, sub_zero]

theorem exists_hasValue_ne_zero (hsurj : ∀ v : Place K F, Function.Surjective (algebraMap K v.ResidueField))
    (v : Place K F) {f : F} (hf : f ≠ 0) (h0 : v.ord f = 0) :
    ∃ a : K, v.HasValue f a ∧ a ≠ 0 := by
  obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hf h0
  obtain ⟨a, ha, hne⟩ := v.exists_hasValue_of_surjective (hsurj v) hm
  exact ⟨a, ha, hne hu⟩

section Main

variable [IsAlgClosed K] [IsCurveOver K F]
variable (S : Finset (Place K F × Place K F)) (E₁ E₂ : Finset (Place K F))

def genSet : Set (GluedPic0 K F S) :=
  {c | ∃ (P Q : Place K F) (x : ↥(GluingData.admissible S)),
    ((P ∉ E₁ ∧ Q ∉ E₁ ∧ (x : GluingData K F S) = (Finsupp.single P 1 - Finsupp.single Q 1, 0, 0)) ∨
     (P ∉ E₂ ∧ Q ∉ E₂ ∧ (x : GluingData K F S) = (0, Finsupp.single P 1 - Finsupp.single Q 1, 0))) ∧
    c = GluedPic0.mk S x}

variable {S E₁ E₂}

theorem hsurj (v : Place K F) : Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

theorem inl_pair_mem_admissible (hE₁ : ∀ s ∈ S, s.1 ∈ E₁) {P Q : Place K F} (hP : P ∉ E₁) (hQ : Q ∉ E₁) :
    ((Finsupp.single P 1 - Finsupp.single Q 1, 0, 0) : GluingData K F S) ∈ GluingData.admissible S := by
  refine (GluingData.mem_admissible S).2
    ⟨single_sub_single_mem_degZero IsCurveOver.deg_eq_one_of_isAlgClosed P Q, zero_mem _, fun s hs => ⟨?_, rfl⟩⟩
  show (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1 : Divisor K F) s.1 = 0
  rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne' (fun h => hP (by rw [h]; exact hE₁ s hs)),
    Finsupp.single_eq_of_ne' (fun h => hQ (by rw [h]; exact hE₁ s hs)), sub_zero]

theorem inr_pair_mem_admissible (hE₂ : ∀ s ∈ S, s.2 ∈ E₂) {P Q : Place K F} (hP : P ∉ E₂) (hQ : Q ∉ E₂) :
    ((0, Finsupp.single P 1 - Finsupp.single Q 1, 0) : GluingData K F S) ∈ GluingData.admissible S := by
  refine (GluingData.mem_admissible S).2
    ⟨zero_mem _, single_sub_single_mem_degZero IsCurveOver.deg_eq_one_of_isAlgClosed P Q, fun s hs => ⟨rfl, ?_⟩⟩
  show (Finsupp.single P (1 : ℤ) - Finsupp.single Q 1 : Divisor K F) s.2 = 0
  rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne' (fun h => hP (by rw [h]; exact hE₂ s hs)),
    Finsupp.single_eq_of_ne' (fun h => hQ (by rw [h]; exact hE₂ s hs)), sub_zero]

noncomputable def ι₁ : Divisor K F →+ GluingData K F S := AddMonoidHom.inl _ _

noncomputable def ι₂ : Divisor K F →+ GluingData K F S := (AddMonoidHom.inr _ _).comp (AddMonoidHom.inl _ _)

@[scoped simp] theorem ι₁_apply (D : Divisor K F) : (ι₁ D : GluingData K F S) = (D, 0, 0) := rfl

@[scoped simp] theorem ι₂_apply (D : Divisor K F) : (ι₂ D : GluingData K F S) = (0, D, 0) := rfl

theorem mk_inl_mem [Infinite (Place K F)] (hE₁ : ∀ s ∈ S, s.1 ∈ E₁) (D : Divisor K F)
    (hD0 : Divisor.degree D = 0) (hDE : ∀ v ∈ E₁, D v = 0)
    (hadm : ((D, 0, 0) : GluingData K F S) ∈ GluingData.admissible S) :
    GluedPic0.mk S ⟨(D, 0, 0), hadm⟩ ∈ AddSubgroup.closure (genSet S E₁ E₂) := by
  classical
  obtain ⟨P₀, hP₀⟩ := Infinite.exists_notMem_finset E₁

  let e : Place K F → ↥(GluingData.admissible S) := fun v =>
    if hv : v ∈ E₁ then 0 else ⟨_, inl_pair_mem_admissible hE₁ hv hP₀⟩
  have he : ∀ v, v ∉ E₁ → GluedPic0.mk S (e v) ∈ AddSubgroup.closure (genSet S E₁ E₂) := fun v hv =>
    AddSubgroup.subset_closure ⟨v, P₀, e v, Or.inl ⟨hv, hP₀, by simp only [e, dif_neg hv]⟩, rfl⟩
  have hsupp : ∀ v ∈ D.support, v ∉ E₁ := fun v hv hvE => (Finsupp.mem_support_iff.1 hv) (hDE v hvE)
  have hsum : (⟨(D, 0, 0), hadm⟩ : ↥(GluingData.admissible S)) = ∑ v ∈ D.support, D v • e v := by
    apply Subtype.ext
    rw [AddSubgroup.val_finset_sum (H := GluingData.admissible S)]
    simp_rw [AddSubgroupClass.coe_zsmul]
    rw [Finset.sum_congr rfl fun v hv => by rw [show ((e v : ↥(GluingData.admissible S)) : GluingData K F S) =
        ι₁ (Finsupp.single v (1 : ℤ) - Finsupp.single P₀ 1) by simp only [e, dif_neg (hsupp v hv)]; rfl]]
    simp_rw [← map_zsmul]
    rw [← map_sum, sum_smul_single_sub IsCurveOver.deg_eq_one_of_isAlgClosed D hD0 P₀]
    rfl
  rw [hsum, map_sum]
  refine sum_mem fun v hv => ?_
  rw [map_zsmul]
  exact AddSubgroup.zsmul_mem _ (he v (hsupp v hv)) _

theorem mk_inr_mem [Infinite (Place K F)] (hE₂ : ∀ s ∈ S, s.2 ∈ E₂) (D : Divisor K F)
    (hD0 : Divisor.degree D = 0) (hDE : ∀ v ∈ E₂, D v = 0)
    (hadm : ((0, D, 0) : GluingData K F S) ∈ GluingData.admissible S) :
    GluedPic0.mk S ⟨(0, D, 0), hadm⟩ ∈ AddSubgroup.closure (genSet S E₁ E₂) := by
  classical
  obtain ⟨P₀, hP₀⟩ := Infinite.exists_notMem_finset E₂
  let e : Place K F → ↥(GluingData.admissible S) := fun v =>
    if hv : v ∈ E₂ then 0 else ⟨_, inr_pair_mem_admissible hE₂ hv hP₀⟩
  have he : ∀ v, v ∉ E₂ → GluedPic0.mk S (e v) ∈ AddSubgroup.closure (genSet S E₁ E₂) := fun v hv =>
    AddSubgroup.subset_closure ⟨v, P₀, e v, Or.inr ⟨hv, hP₀, by simp only [e, dif_neg hv]⟩, rfl⟩
  have hsupp : ∀ v ∈ D.support, v ∉ E₂ := fun v hv hvE => (Finsupp.mem_support_iff.1 hv) (hDE v hvE)
  have hsum : (⟨(0, D, 0), hadm⟩ : ↥(GluingData.admissible S)) = ∑ v ∈ D.support, D v • e v := by
    apply Subtype.ext
    rw [AddSubgroup.val_finset_sum (H := GluingData.admissible S)]
    simp_rw [AddSubgroupClass.coe_zsmul]
    rw [Finset.sum_congr rfl fun v hv => by rw [show ((e v : ↥(GluingData.admissible S)) : GluingData K F S) =
        ι₂ (Finsupp.single v (1 : ℤ) - Finsupp.single P₀ 1) by simp only [e, dif_neg (hsupp v hv)]; rfl]]
    simp_rw [← map_zsmul]
    rw [← map_sum, sum_smul_single_sub IsCurveOver.deg_eq_one_of_isAlgClosed D hD0 P₀]
    rfl
  rw [hsum, map_sum]
  refine sum_mem fun v hv => ?_
  rw [map_zsmul]
  exact AddSubgroup.zsmul_mem _ (he v (hsupp v hv)) _

theorem nodeUnit_mem [Infinite (Place K F)] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, s.2 = s'.2 → s = s') (hE₂ : ∀ s ∈ S, s.2 ∈ E₂)
    (w : ↥S → Additive Kˣ) :
    GluedPic0.nodeUnit S w ∈ AddSubgroup.closure (genSet S E₁ E₂) := by
  classical
  obtain ⟨P₀, hP₀⟩ := Infinite.exists_notMem_finset E₂

  let cf : Place K F → K := fun e =>
    if h : ∃ s : ↥S, (s : Place K F × Place K F).2 = e then ((Additive.toMul (w h.choose) : Kˣ) : K) else 1
  have hcf0 : ∀ e, cf e ≠ 0 := fun e => by
    simp only [cf]
    split_ifs
    · exact Units.ne_zero _
    · exact one_ne_zero
  have hcfs : ∀ s : ↥S, cf (s : Place K F × Place K F).2 = ((Additive.toMul (w s) : Kˣ) : K) := by
    intro s
    have h : ∃ s' : ↥S, (s' : Place K F × Place K F).2 = (s : Place K F × Place K F).2 := ⟨s, rfl⟩
    simp only [cf, dif_pos h]
    have hs' : h.choose = s := Subtype.ext (hS _ h.choose.2 _ s.2 h.choose_spec)
    rw [hs']
  obtain ⟨h, hh0, hval, -⟩ :=
    RROpens.exists_forall_hasValue_forall_ord_nonneg Kc g hRR E₂ cf (fun e _ => hcf0 e) P₀ hP₀

  obtain ⟨Dh, hDh, hDh0⟩ := HasPrincipalDivisors.exists_divisor (K := K) h hh0
  have hDhE : ∀ v ∈ E₂, Dh v = 0 := fun v hv => by rw [hDh v]; exact (hval v hv).ord_eq_zero (hcf0 v)
  have hadm : ((0, Dh, 0) : GluingData K F S) ∈ GluingData.admissible S :=
    (GluingData.mem_admissible S).2 ⟨zero_mem _, hDh0, fun s hs => ⟨rfl, hDhE _ (hE₂ s hs)⟩⟩

  have hprin : GluingData.IsGluedPrincipal S ((0, Dh, -w) : GluingData K F S) := by
    refine ⟨1, h, 1, fun s => Additive.toMul (w s), one_ne_zero, hh0, fun v => by simp, fun v => hDh v,
      fun s => ⟨by simpa using (s : Place K F × Place K F).1.hasValue_one, ?_⟩, ?_⟩
    · rw [← hcfs s]
      exact hval _ (hE₂ _ s.2)
    · funext s
      simp [div_eq_mul_inv]
  have hzero : GluedPic0.mk S (⟨(0, Dh, 0), hadm⟩ - GluedPic0.nodeUnitAux S w) = 0 := by
    refine (GluedPic0.mk_eq_zero_iff S _).2 ?_
    rw [AddSubgroup.coe_sub]
    convert hprin using 1
    show ((0, Dh, 0) : GluingData K F S) - (0, 0, w) = (0, Dh, -w)
    ext <;> simp
  rw [map_sub, sub_eq_zero] at hzero
  have hb : GluedPic0.nodeUnit S w = GluedPic0.mk S ⟨(0, Dh, 0), hadm⟩ := hzero.symm
  rw [hb]
  exact mk_inr_mem hE₂ Dh hDh0 hDhE hadm

theorem mk_mem_of_avoid [Infinite (Place K F)] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, s.2 = s'.2 → s = s')
    (hE₁ : ∀ s ∈ S, s.1 ∈ E₁) (hE₂ : ∀ s ∈ S, s.2 ∈ E₂)
    (x : ↥(GluingData.admissible S))
    (hx₁ : ∀ v ∈ E₁, (x : GluingData K F S).1 v = 0) (hx₂ : ∀ v ∈ E₂, (x : GluingData K F S).2.1 v = 0) :
    GluedPic0.mk S x ∈ AddSubgroup.closure (genSet S E₁ E₂) := by
  obtain ⟨hd₁, hd₂, havoid⟩ := (GluingData.mem_admissible S).1 x.2
  have hadm₁ : (((x : GluingData K F S).1, 0, 0) : GluingData K F S) ∈ GluingData.admissible S :=
    (GluingData.mem_admissible S).2 ⟨hd₁, zero_mem _, fun s hs => ⟨(havoid s hs).1, rfl⟩⟩
  have hadm₂ : ((0, (x : GluingData K F S).2.1, 0) : GluingData K F S) ∈ GluingData.admissible S :=
    (GluingData.mem_admissible S).2 ⟨zero_mem _, hd₂, fun s hs => ⟨rfl, (havoid s hs).2⟩⟩
  have hsplit : x = ⟨_, hadm₁⟩ + ⟨_, hadm₂⟩ + GluedPic0.nodeUnitAux S (x : GluingData K F S).2.2 := by
    apply Subtype.ext
    rw [AddSubgroup.coe_add, AddSubgroup.coe_add]
    ext <;> simp [GluedPic0.nodeUnitAux]
  rw [hsplit, map_add, map_add]
  refine add_mem (add_mem (mk_inl_mem hE₁ _ hd₁ hx₁ hadm₁) (mk_inr_mem hE₂ _ hd₂ hx₂ hadm₂)) ?_
  exact nodeUnit_mem Kc g hRR hS hE₂ _

theorem mk_mem [Infinite (Place K F)] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, s.2 = s'.2 → s = s')
    (hE₁ : ∀ s ∈ S, s.1 ∈ E₁) (hE₂ : ∀ s ∈ S, s.2 ∈ E₂)
    (x : ↥(GluingData.admissible S)) :
    GluedPic0.mk S x ∈ AddSubgroup.closure (genSet S E₁ E₂) := by
  classical
  obtain ⟨hd₁, hd₂, havoid⟩ := (GluingData.mem_admissible S).1 x.2

  obtain ⟨g₁, hg₁, hord₁⟩ := Place.exists_forall_ord_eq_finset E₁ (fun v => (x : GluingData K F S).1 v)
  obtain ⟨g₂, hg₂, hord₂⟩ := Place.exists_forall_ord_eq_finset E₂ (fun v => (x : GluingData K F S).2.1 v)
  obtain ⟨G₁, hG₁, hG₁0⟩ := HasPrincipalDivisors.exists_divisor (K := K) g₁ hg₁
  obtain ⟨G₂, hG₂, hG₂0⟩ := HasPrincipalDivisors.exists_divisor (K := K) g₂ hg₂

  have ha : ∀ s : ↥S, ∃ a : K, (s : Place K F × Place K F).1.HasValue g₁ a ∧ a ≠ 0 := fun s =>
    exists_hasValue_ne_zero hsurj _ hg₁ (by rw [hord₁ _ (hE₁ _ s.2)]; exact (havoid _ s.2).1)
  have hb : ∀ s : ↥S, ∃ b : K, (s : Place K F × Place K F).2.HasValue g₂ b ∧ b ≠ 0 := fun s =>
    exists_hasValue_ne_zero hsurj _ hg₂ (by rw [hord₂ _ (hE₂ _ s.2)]; exact (havoid _ s.2).2)
  choose a ha ha0 using ha
  choose b hb hb0 using hb
  let z : GluingData K F S := (G₁, G₂, fun s => Additive.ofMul (Units.mk0 (a s) (ha0 s) / Units.mk0 (b s) (hb0 s)))
  have hzprin : GluingData.IsGluedPrincipal S z :=
    ⟨g₁, g₂, fun s => Units.mk0 (a s) (ha0 s), fun s => Units.mk0 (b s) (hb0 s), hg₁, hg₂, hG₁, hG₂,
      fun s => ⟨ha s, hb s⟩, rfl⟩
  have hzadm : z ∈ GluingData.admissible S :=
    (GluingData.mem_admissible S).2 ⟨hG₁0, hG₂0, fun s hs =>
      ⟨by rw [hG₁, hord₁ _ (hE₁ s hs)]; exact (havoid s hs).1, by rw [hG₂, hord₂ _ (hE₂ s hs)]; exact (havoid s hs).2⟩⟩
  have hz0 : GluedPic0.mk S ⟨z, hzadm⟩ = 0 := (GluedPic0.mk_eq_zero_iff S _).2 hzprin
  have hx : GluedPic0.mk S x = GluedPic0.mk S (x - ⟨z, hzadm⟩) := by rw [map_sub, hz0, sub_zero]
  rw [hx]
  refine mk_mem_of_avoid Kc g hRR hS hE₁ hE₂ _ (fun v hv => ?_) (fun v hv => ?_)
  · show ((x : GluingData K F S) - z).1 v = 0
    rw [Prod.fst_sub, Finsupp.sub_apply, hG₁, hord₁ v hv, sub_self]
  · show ((x : GluingData K F S) - z).2.1 v = 0
    rw [Prod.snd_sub, Prod.fst_sub, Finsupp.sub_apply, hG₂, hord₂ v hv, sub_self]

end Main

end GenPairH
p2m_reactivate "P2MW.S_AlgebraicCurve_GluedPic0_mem_closure_mk_pair_of_riemannRoch.GenPairH"

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    [Infinite (Place K F)]
    (S : Finset (Place K F × Place K F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, s.2 = s'.2 → s = s')
    (E₁ E₂ : Finset (Place K F)) (hE₁ : ∀ s ∈ S, s.1 ∈ E₁) (hE₂ : ∀ s ∈ S, s.2 ∈ E₂)
    (c : GluedPic0 K F S) :
    c ∈ AddSubgroup.closure {c | ∃ (P Q : Place K F) (x : ↥(GluingData.admissible S)),
        ((P ∉ E₁ ∧ Q ∉ E₁ ∧ (x : GluingData K F S) = (Finsupp.single P 1 - Finsupp.single Q 1, 0, 0)) ∨
         (P ∉ E₂ ∧ Q ∉ E₂ ∧ (x : GluingData K F S) = (0, Finsupp.single P 1 - Finsupp.single Q 1, 0))) ∧
        c = GluedPic0.mk S x} := by
  obtain ⟨x, rfl⟩ := GluedPic0.mk_surjective S c
  exact GenPairH.mk_mem Kc g hRR hS hE₁ hE₂ x

end S_AlgebraicCurve_GluedPic0_mem_closure_mk_pair_of_riemannRoch
end P2MW
export P2MW.S_AlgebraicCurve_GluedPic0_mem_closure_mk_pair_of_riemannRoch (solution)
