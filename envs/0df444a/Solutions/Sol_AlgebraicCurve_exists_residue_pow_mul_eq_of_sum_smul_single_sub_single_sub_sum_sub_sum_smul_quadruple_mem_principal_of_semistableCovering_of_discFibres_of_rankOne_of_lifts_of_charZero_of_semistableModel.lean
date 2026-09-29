-- Prove2me | solution 1 for AlgebraicCurve.exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/e7c98fe8-bc3c-5aa1-a3dd-c89c8c6c3dfc

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_WeightedMultigraph_slope_eq_zero_of_gradient_of_harmonic
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Annulus_exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct

namespace ChartPrincipalMomentEngine

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  let u : (v.toValuationSubring)ˣ :=
    ⟨⟨algebraMap K F c, v.algebraMap_mem' c⟩, ⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  have := v.ord_coe_unit u
  simpa [u] using this

theorem ord_smul (v : Place K F) {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, ord_algebraMap v hc, zero_add]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  have := v.evalAt_algebraMap_eq (0 : K)
  simpa using this

theorem degree_eq_sum_of_isRational (D : Divisor K F) (h : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finset.sum_congr rfl fun v hv => ?_
  simp [Place.deg_eq_one_of_isRational (h v hv)]

end PlaceLemmas

section OneChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

@[reducible] def rp (C : ComponentChart A F Fbar) : RegularProlongation A F Fbar where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

theorem const_ne_zero (C : ComponentChart A F Fbar) {f : F} {c : L} (hc : c • f ∈ C.integers)
    (hres : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 :=
  (rp C).smul_const_ne_zero hc hres

theorem fun_ne_zero (C : ComponentChart A F Fbar) {f : F} {c : L} (hc : c • f ∈ C.integers)
    (hres : C.residue ⟨c • f, hc⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨c • (0 : F), hc⟩ : C.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

theorem mapDomain_eq_ord_of_not_mem_nodes (C : ComponentChart A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (D : Divisor L F) (hDdom : ∀ P ∈ C.dom, D P = P.ord f) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∉ C.nodes) :
    Finsupp.mapDomain C.placeMap D Q = Q.ord (C.residue ⟨c • f, hc⟩) := by
  refine C.mapDomain_placeMap ⟨c • f, hc⟩ hres D (fun P hP => ?_) hDoff Q hQ
  rw [hDdom P hP]
  exact (ord_smul P (const_ne_zero C hc hres) (fun_ne_zero C hc hres)).symm

theorem mapDomain_eq_zero_of_mem_nodes (C : ComponentChart A F Fbar)
    (D : Divisor L F) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (Q : Place (ResidueField A) Fbar) (hQ : Q ∈ C.nodes) :
    Finsupp.mapDomain C.placeMap D Q = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun P hP => ?_
  show Finsupp.single (C.placeMap P) (D P) Q = 0
  rw [Finsupp.single_apply, if_neg]
  intro hPQ
  have hPdom : P ∈ C.dom := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp hP) (hDoff P h)
  exact C.placeMap_not_mem_nodes P hPdom (hPQ ▸ hQ)

theorem sum_mapDomain (C : ComponentChart A F Fbar) (D : Divisor L F) :
    ((Finsupp.mapDomain C.placeMap D).sum fun _ n => n) = D.sum fun _ n => n :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem sum_nodes_ord_eq_zero [HasPrincipalDivisors (ResidueField A) Fbar]
    (hrat : ∀ x : Place (ResidueField A) Fbar, x.IsRational)
    (C : ComponentChart A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ C.integers) (hres : C.residue ⟨c • f, hc⟩ ≠ 0)
    (D : Divisor L F) (hDdom : ∀ P ∈ C.dom, D P = P.ord f) (hDoff : ∀ P, P ∉ C.dom → D P = 0)
    (hmass : (D.sum fun _ n => n) = 0) :
    ∑ x ∈ C.nodes, x.ord (C.residue ⟨c • f, hc⟩) = 0 := by
  classical
  set g : Fbar := C.residue ⟨c • f, hc⟩ with hg
  obtain ⟨E, hE, hdegE⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) g hres

  set N : Divisor (ResidueField A) Fbar := ∑ x ∈ C.nodes, Finsupp.single x (x.ord g) with hN
  have hN_apply : ∀ y, N y = if y ∈ C.nodes then y.ord g else 0 := by
    intro y
    rw [hN, Finsupp.finsetSum_apply]
    split_ifs with hy
    · rw [Finset.sum_eq_single y (fun x _ hxy => by rw [Finsupp.single_apply, if_neg hxy])
        (fun h => (h hy).elim), Finsupp.single_eq_same]
    · exact Finset.sum_eq_zero fun x hx => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl
        exact hy hx
  have hEeq : E = Finsupp.mapDomain C.placeMap D + N := by
    ext y
    rw [Finsupp.add_apply, hN_apply, hE y]
    by_cases hy : y ∈ C.nodes
    · rw [if_pos hy, mapDomain_eq_zero_of_mem_nodes C D hDoff y hy, zero_add]
    · rw [if_neg hy, mapDomain_eq_ord_of_not_mem_nodes C hc hres D hDdom hDoff y hy, add_zero]

  have hmassE : (E.sum fun _ n => n) = 0 := by
    rw [← degree_eq_sum_of_isRational E (fun v _ => hrat v)]
    exact hdegE
  have hmassN : (N.sum fun _ n => n) = ∑ x ∈ C.nodes, x.ord g := by
    rw [hN, ← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact Finset.sum_congr rfl fun x _ => Finsupp.sum_single_index rfl
  rw [hEeq, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), sum_mapDomain, hmass, zero_add,
    hmassN] at hmassE
  exact hmassE

end OneChart

section OneAnnulus

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

private theorem transfer_end {I : ValuationSubring F} (res : I →+* Fb) (x : Place (ResidueField A) Fb)
    {S S' : Set (Place L F)} (hS : S = S') {p p' : F} (hp : p = p')
    (H : ∃ hz : p ∈ I, x.ord (res ⟨p, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ I), res ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S, P.ord f = 0) → ∀ P ∈ S,
        ∃ h : P.evalAt f * (P.evalAt p) ^ (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) :
    ∃ hz : p' ∈ I, x.ord (res ⟨p', hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ I), res ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S', P.ord f = 0) → ∀ P ∈ S',
        ∃ h : P.evalAt f * (P.evalAt p') ^ (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  subst hS; subst hp; exact H

theorem param_ne_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) : An.param ≠ 0 := by
  intro h0
  obtain ⟨-, -, -, hne, -⟩ := An.mem_dom P hP
  exact hne (by rw [h0, evalAt_zero])

theorem end_orders (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hatt : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hatt' : An'.IsAttached Cb xb)
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))
    {f : F} (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom)
    (hN : ∀ P ∈ An.dom, N P = P.ord f) (hNsum : (N.sum fun _ k => k) = 0)
    (hNprod : (N.prod fun P k => A.valuation (P.evalAt An.param) ^ k) = 1)
    {ca : L} (hca : ca • f ∈ Ca.integers) (hresa : Ca.residue ⟨ca • f, hca⟩ ≠ 0)
    {cb : L} (hcb : cb • f ∈ Cb.integers) (hresb : Cb.residue ⟨cb • f, hcb⟩ ≠ 0) :
    xa.ord (Ca.residue ⟨ca • f, hca⟩) + xb.ord (Cb.residue ⟨cb • f, hcb⟩) = 0 ∧
    A.valuation ca * (A.valuation cb)⁻¹ *
        A.valuation (An.modulus : L) ^ (xb.ord (Cb.residue ⟨cb • f, hcb⟩)) = 1 := by
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := hwide
  have hz0 : An.param ≠ 0 := param_ne_zero An hQ₁
  have hp' : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hz0).mpr hparam
  have hca0 : ca ≠ 0 := const_ne_zero Ca hca hresa
  have hcb0 : cb ≠ 0 := const_ne_zero Cb hcb hresb
  have hf0 : f ≠ 0 := fun_ne_zero Ca hca hresa

  obtain ⟨-, hza, hxa, hsla⟩ := hatt
  obtain ⟨-, Hb⟩ := hatt'
  obtain ⟨hzb, hxb, hslb⟩ := transfer_end Cb.residue xb hdom hp' Hb

  set c' : L := ca * cb⁻¹ with hc'
  have hc'0 : c' ≠ 0 := mul_ne_zero hca0 (inv_ne_zero hcb0)
  have hh0 : ca • f ≠ 0 := smul_ne_zero hca0 hf0
  have heq : (algebraMap L F c')⁻¹ * (ca • f) = cb • f := by
    have hca' : algebraMap L F ca ≠ 0 := (map_ne_zero _).mpr hca0
    rw [hc', Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀]
    field_simp
  have hhb : (algebraMap L F c')⁻¹ * (ca • f) ∈ Cb.integers := heq ▸ hcb
  have hsub : (⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩ : Cb.integers) = ⟨cb • f, hcb⟩ :=
    Subtype.ext heq
  have hresb' : Cb.residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩ ≠ 0 := by rw [hsub]; exact hresb

  have hordh : ∀ P ∈ An.dom, N P = P.ord (ca • f) := fun P hP => by
    rw [ord_smul P hca0 hf0]; exact hN P hP
  obtain ⟨hmass, hprod⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (rp Ca) xa hza hxa hsla (rp Cb) xb hzb hxb hslb ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩
      (ca • f) hh0 hca hresa c' hc'0 hhb hresb' N hNdom hordh
  rw [hNsum] at hmass
  rw [hNprod] at hprod

  have hordb : xb.ord ((rp Cb).residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩) =
      xb.ord (Cb.residue ⟨cb • f, hcb⟩) := by
    show xb.ord (Cb.residue ⟨(algebraMap L F c')⁻¹ * (ca • f), hhb⟩) = _
    rw [hsub]
  rw [hordb] at hmass hprod
  refine ⟨?_, ?_⟩
  · exact hmass.symm
  · rw [hc', map_mul, map_inv₀] at hprod
    exact hprod.symm

end OneAnnulus

section Wide

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem mem_of_pow_mem {r : L} {k : ℕ} (hk : 0 < k) (hr : r ^ k ∈ A) : r ∈ A := by
  rw [← A.valuation_le_one_iff] at hr ⊢
  rw [map_pow] at hr
  by_contra h
  have h' : 1 < A.valuation r := not_le.mp h
  have : 1 < A.valuation r ^ k := one_lt_pow₀ h' hk.ne'
  exact absurd hr (not_le.mpr this)

theorem mem_maximalIdeal_of_pow {r : A} {k : ℕ} {a : A} (ha : a ∈ maximalIdeal A) (hr : r ^ k = a) :
    r ∈ maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
  intro hu
  exact ha (hr ▸ hu.pow k)

theorem wide_of_isAlgClosed [IsAlgClosed L] (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  set μ : A := An.modulus with hμ
  have hμm : μ ∈ maximalIdeal A := An.modulus_mem
  have hvμ1 : A.valuation (μ : L) < 1 := (A.valuation_lt_one_iff μ).mp hμm
  have hvμ0 : A.valuation (μ : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hmod0

  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (n := 2) two_pos
  have hrA : r ∈ A := mem_of_pow_mem two_pos (hr ▸ μ.2)
  have hr' : (⟨r, hrA⟩ : A) ^ 2 = μ := Subtype.ext (by simpa using hr)
  have hrm : (⟨r, hrA⟩ : A) ∈ maximalIdeal A := mem_maximalIdeal_of_pow hμm hr'
  have hr0 : r ≠ 0 := by rintro rfl; apply hmod0; rw [← hr]; simp

  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (n := 3) three_pos
  have hsA : s ∈ A := mem_of_pow_mem three_pos (hs ▸ μ.2)
  have hs' : (⟨s, hsA⟩ : A) ^ 3 = μ := Subtype.ext (by simpa using hs)
  have hsm : (⟨s, hsA⟩ : A) ∈ maximalIdeal A := mem_maximalIdeal_of_pow hμm hs'
  have hs0 : s ≠ 0 := by rintro rfl; apply hmod0; rw [← hs]; simp
  have htm : (⟨s, hsA⟩ : A) ^ 2 ∈ maximalIdeal A :=
    Ideal.pow_mem_of_mem _ hsm 2 two_pos

  obtain ⟨Q₁, ⟨hQ₁, hQ₁z⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r, hrA⟩ hrm hr0
    ⟨⟨r, hrA⟩, hrm, by rw [← hμ, ← hr]; simp [pow_two]⟩
  obtain ⟨Q₂, ⟨hQ₂, hQ₂z⟩, -⟩ := An.existsUnique_evalAt_eq (⟨s, hsA⟩ ^ 2) htm (by simpa using hs0)
    ⟨⟨s, hsA⟩, hsm, by rw [← hμ, ← hs]; simp [pow_succ]⟩
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁z, hQ₂z]
  intro hv

  have h1 : A.valuation r ^ 2 = A.valuation (μ : L) := by rw [← map_pow, hr]
  have h2 : A.valuation (((⟨s, hsA⟩ : A) ^ 2 : A) : L) ^ 3 = A.valuation (μ : L) ^ 2 := by
    rw [← map_pow, ← map_pow]
    congr 1
    push_cast
    rw [← hs]; ring
  have hv' : A.valuation r = A.valuation (((⟨s, hsA⟩ : A) ^ 2 : A) : L) := hv
  rw [← hv'] at h2

  have ha0 : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr0
  have : A.valuation (μ : L) = 1 := by
    have h3 : A.valuation r ^ 3 * 1 = A.valuation r ^ 3 * A.valuation r := by
      rw [mul_one, ← pow_succ, h2, ← h1, ← pow_mul]
    have h4 : A.valuation r = 1 := (mul_left_cancel₀ (pow_ne_zero 3 ha0) h3).symm
    rw [← h1, h4, one_pow]
  exact absurd this hvμ1.ne

end Wide

section Nodes

open Finset

variable {ι E : Type*} [Fintype E] [DecidableEq ι] {P : ι → Type*}

theorem sum_nodes_eq_sum_ends (nodes : ∀ i, Finset (P i)) (src tgt : E → ι)
    (xs : ∀ e, P (src e)) (xt : ∀ e, P (tgt e))
    (hmem_s : ∀ e, xs e ∈ nodes (src e)) (hmem_t : ∀ e, xt e ∈ nodes (tgt e))
    (hex : ∀ i, ∀ x ∈ nodes i, ∃ e,
      (⟨src e, xs e⟩ : Σ j, P j) = ⟨i, x⟩ ∨ (⟨tgt e, xt e⟩ : Σ j, P j) = ⟨i, x⟩)
    (huniq : ∀ i, ∀ x ∈ nodes i, ∀ e₁ e₂ : E ⊕ E,
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) e₁ = ⟨i, x⟩ →
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) e₂ = ⟨i, x⟩ → e₁ = e₂)
    (φ : ∀ j, P j → ℤ) (i : ι) :
    ∑ x ∈ nodes i, φ i x =
      (∑ e ∈ univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
        ∑ e ∈ univ.filter (fun e => src e = i), φ (src e) (xs e) := by
  classical
  set endOf : E ⊕ E → Σ j, P j :=
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, P j)) (fun e => ⟨tgt e, xt e⟩) with hendOf
  set Φ : (Σ j, P j) → ℤ := fun y => φ y.1 y.2 with hΦ
  set S : Finset (E ⊕ E) := univ.filter (fun t => (endOf t).1 = i) with hS

  have hend_mem : ∀ t : E ⊕ E, (endOf t).2 ∈ nodes (endOf t).1 := by
    rintro (e | e)
    · exact hmem_s e
    · exact hmem_t e

  have hR : (∑ e ∈ univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
      ∑ e ∈ univ.filter (fun e => src e = i), φ (src e) (xs e) = ∑ t ∈ S, Φ (endOf t) := by
    rw [hS, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Fintype.sum_sum_type, add_comm]
    rfl

  have hL : ∑ x ∈ nodes i, φ i x = ∑ y ∈ (nodes i).map (Function.Embedding.sigmaMk i), Φ y := by
    rw [Finset.sum_map]
    rfl

  have himage : S.image endOf = (nodes i).map (Function.Embedding.sigmaMk i) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_map, Function.Embedding.sigmaMk_apply, hS,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨cast (congrArg P ht) (endOf t).2, ?_, ?_⟩
      · have := hend_mem t
        revert this
        generalize endOf t = y at ht ⊢
        obtain ⟨j, x⟩ := y
        cases ht
        exact id
      · generalize endOf t = y at ht ⊢
        obtain ⟨j, x⟩ := y
        cases ht
        rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨e, he | he⟩ := hex i x hx
      · exact ⟨Sum.inl e, by simp [hendOf, congrArg Sigma.fst he], he⟩
      · exact ⟨Sum.inr e, by simp [hendOf, congrArg Sigma.fst he], he⟩
  have hinj : Set.InjOn endOf (S : Set (E ⊕ E)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    simp only [Finset.coe_filter, hS, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht₁ ht₂
    have hy : ∃ x ∈ nodes i, endOf t₁ = ⟨i, x⟩ := by
      have := hend_mem t₁
      revert this
      generalize endOf t₁ = y at ht₁ ⊢
      obtain ⟨j, x⟩ := y
      cases ht₁
      exact fun h => ⟨x, h, rfl⟩
    obtain ⟨x, hx, h₁⟩ := hy
    exact huniq i x hx t₁ t₂ h₁ (heq ▸ h₁)
  rw [hL, hR, ← himage, Finset.sum_image hinj]

end Nodes

end ChartPrincipalMomentEngine

namespace LC2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def mass : Divisor K F →+ ℤ := Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ

theorem mass_eq_sum (D : Divisor K F) : mass D = D.sum fun _ k => k := by
  unfold mass; rw [Finsupp.liftAddHom_apply]; rfl

@[scoped simp] theorem mass_single (P : Place K F) (n : ℤ) : mass (Finsupp.single P n) = n := by
  rw [mass_eq_sum, Finsupp.sum_single_index rfl]

open Classical in

noncomputable def star {M : Type*} [GroupWithZero M] (a : Place K F → M) (P : Place K F) : M :=
  if a P = 0 then 1 else a P

theorem star_ne_zero {M : Type*} [GroupWithZero M] (a : Place K F → M) (P : Place K F) : star a P ≠ 0 := by
  classical
  unfold star; split_ifs with h
  · exact one_ne_zero
  · exact h

theorem star_of_ne_zero {M : Type*} [GroupWithZero M] (a : Place K F → M) {P : Place K F} (h : a P ≠ 0) :
    star a P = a P := by
  classical
  unfold star; rw [if_neg h]

theorem prod_zpow' {M : Type*} [CommGroupWithZero M] {α : Type*} [DecidableEq α] (s : Finset α) (f : α → M) (n : ℤ) :
    (∏ i ∈ s, f i) ^ n = ∏ i ∈ s, f i ^ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_zpow, ih]

theorem prod_star_add {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (D E : Divisor K F) :
    ((D + E).prod fun P k => star a P ^ k) = (D.prod fun P k => star a P ^ k) * (E.prod fun P k => star a P ^ k) :=
  Finsupp.prod_add_index' (fun _ => zpow_zero _) (fun P b₁ b₂ => zpow_add₀ (star_ne_zero a P) b₁ b₂)

theorem prod_star_neg {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (D : Divisor K F) :
    ((-D).prod fun P k => star a P ^ k) = (D.prod fun P k => star a P ^ k)⁻¹ := by
  have h := prod_star_add a D (-D)
  rw [add_neg_cancel, Finsupp.prod_zero_index] at h
  have hne : (D.prod fun P k => star a P ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun P _ => zpow_ne_zero _ (star_ne_zero a P))
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem prod_star_sub {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (D E : Divisor K F) :
    ((D - E).prod fun P k => star a P ^ k) = (D.prod fun P k => star a P ^ k) * (E.prod fun P k => star a P ^ k)⁻¹ := by
  rw [sub_eq_add_neg, prod_star_add, prod_star_neg]

theorem prod_star_zsmul {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (n : ℤ) (D : Divisor K F) :
    ((n • D).prod fun P k => star a P ^ k) = (D.prod fun P k => star a P ^ k) ^ n := by

  rw [Finsupp.prod_of_support_subset (n • D) Finsupp.support_smul (fun P k => star a P ^ k) (fun _ _ => zpow_zero _)]
  unfold Finsupp.prod
  classical
  rw [prod_zpow']
  refine Finset.prod_congr rfl (fun P _ => ?_)
  show star a P ^ (n • D) P = (star a P ^ (D P)) ^ n
  rw [Finsupp.smul_apply, smul_eq_mul, mul_comm, zpow_mul]

theorem prod_star_sum {M : Type*} [CommGroupWithZero M] (a : Place K F → M) {ι : Type*} (s : Finset ι)
    (D : ι → Divisor K F) :
    ((∑ i ∈ s, D i).prod fun P k => star a P ^ k) = ∏ i ∈ s, ((D i).prod fun P k => star a P ^ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Finsupp.prod_zero_index]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, prod_star_add, ih]

theorem prod_star_single {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (P : Place K F) (n : ℤ) :
    ((Finsupp.single P n).prod fun P k => star a P ^ k) = star a P ^ n := by
  rw [Finsupp.prod_single_index (zpow_zero _)]

theorem prod_star_eq_prod {M : Type*} [CommGroupWithZero M] (a : Place K F → M) (D : Divisor K F)
    (h : ∀ P ∈ D.support, a P ≠ 0) :
    (D.prod fun P k => star a P ^ k) = D.prod fun P k => a P ^ k :=
  Finset.prod_congr rfl (fun P hP => by simp only [star_of_ne_zero a (h P hP)])

end LC2
p2m_reactivate "P2MW.S_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.LC2"

theorem LC2.exists_coboundary_of_residue_edge_law
    {L : Type} [Field L] (A : ValuationSubring L)
    (n m : ℕ) (src tgt : Fin m → Fin n)
    (κc : Fin n → L) (hc0 : ∀ i, κc i ≠ 0)
    (hveq : ∀ e, A.valuation (κc (src e)) = A.valuation (κc (tgt e)))
    (γ : Fin n → IsLocalRing.ResidueField A) (hγ0 : ∀ i, γ i ≠ 0)
    (ξ : L) (hξA : ξ ∈ A) (hvξ : A.valuation ξ = 1)
    (c : Fin m → ℤ)
    (hkey : ∀ e, ∃ hW : κc (tgt e) * (κc (src e))⁻¹ * ξ ^ (-(c e)) ∈ A,
      IsLocalRing.residue A ⟨_, hW⟩ * γ (src e) = γ (tgt e)) :
    ∃ b : Fin n → IsLocalRing.ResidueField A, (∀ i, b i ≠ 0) ∧
      ∀ e, (IsLocalRing.residue A ⟨ξ, hξA⟩) ^ (c e) * b (src e) = b (tgt e) := by
  classical

  let jof : Fin n → Fin n := fun i =>
    (Finset.univ.filter (fun j => A.valuation (κc j) = A.valuation (κc i))).min'
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
  have hjof : ∀ i, A.valuation (κc (jof i)) = A.valuation (κc i) := by
    intro i
    have hmem := Finset.min'_mem (Finset.univ.filter (fun j => A.valuation (κc j) = A.valuation (κc i)))
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩⟩
    exact (Finset.mem_filter.mp hmem).2
  have hjof_eq : ∀ e, jof (src e) = jof (tgt e) := by
    intro e
    show (Finset.univ.filter (fun j => A.valuation (κc j) = A.valuation (κc (src e)))).min' _ =
      (Finset.univ.filter (fun j => A.valuation (κc j) = A.valuation (κc (tgt e)))).min' _
    congr 1
    · ext j; simp [hveq e]
  have hvc : ∀ i, A.valuation (κc i) ≠ 0 := fun i => (map_ne_zero _).mpr (hc0 i)

  have memA : ∀ x : L, A.valuation x = 1 → x ∈ A := fun x h => (A.valuation_le_one_iff x).mp h.le
  have resne : ∀ (x : L) (h : A.valuation x = 1), IsLocalRing.residue A ⟨x, memA x h⟩ ≠ 0 := by
    intro x h h0
    have hu : IsUnit (⟨x, memA x h⟩ : A) := (A.valuation_eq_one_iff _).mpr h
    exact ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)) hu
  have hvβ : ∀ i, A.valuation (κc i * (κc (jof i))⁻¹) = 1 := by
    intro i; rw [map_mul, map_inv₀, hjof i, mul_inv_cancel₀ (hvc i)]
  let β : Fin n → IsLocalRing.ResidueField A := fun i => IsLocalRing.residue A ⟨κc i * (κc (jof i))⁻¹, memA _ (hvβ i)⟩
  have hβ0 : ∀ i, β i ≠ 0 := fun i => resne _ (hvβ i)

  have hvr : ∀ e, A.valuation (κc (tgt e) * (κc (src e))⁻¹) = 1 := by
    intro e; rw [map_mul, map_inv₀, ← hveq e, mul_inv_cancel₀ (hvc _)]
  have hβedge : ∀ e, β (tgt e) = IsLocalRing.residue A ⟨κc (tgt e) * (κc (src e))⁻¹, memA _ (hvr e)⟩ * β (src e) := by
    intro e
    show IsLocalRing.residue A ⟨κc (tgt e) * (κc (jof (tgt e)))⁻¹, _⟩ =
      IsLocalRing.residue A ⟨κc (tgt e) * (κc (src e))⁻¹, _⟩ * IsLocalRing.residue A ⟨κc (src e) * (κc (jof (src e)))⁻¹, _⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    rw [hjof_eq e]
    field_simp [hc0 (src e)]

  have hξres : IsLocalRing.residue A ⟨ξ, hξA⟩ ≠ 0 := by
    have := resne ξ hvξ; exact this
  have hξunit : IsUnit (⟨ξ, hξA⟩ : A) := (A.valuation_eq_one_iff _).mpr hvξ
  obtain ⟨U, hU⟩ := hξunit
  have hξpow_mem : ∀ nn : ℤ, ∃ hmem : ξ ^ nn ∈ A, IsLocalRing.residue A ⟨ξ ^ nn, hmem⟩ = (IsLocalRing.residue A ⟨ξ, hξA⟩) ^ nn := by
    intro nn
    have hval : ((U ^ nn : Aˣ) : A).1 = ξ ^ nn := by
      have : ((Units.map (A.subtype : A →* L) (U ^ nn) : Lˣ) : L) = ((Units.map (A.subtype : A →* L) U) ^ nn : Lˣ) := by
        rw [map_zpow]
      rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at this
      rw [MonoidHom.coe_coe, hU] at this
      exact this
    refine ⟨hval ▸ ((U ^ nn : Aˣ) : A).2, ?_⟩
    rw [show (⟨ξ ^ nn, hval ▸ ((U ^ nn : Aˣ) : A).2⟩ : A) = ((U ^ nn : Aˣ) : A) from Subtype.ext hval.symm]
    have : (Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (U ^ nn) : IsLocalRing.ResidueField A) =
        ((Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) U) ^ nn : (IsLocalRing.ResidueField A)ˣ) := by
      rw [map_zpow]
    rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe, hU] at this
    exact this
  refine ⟨fun i => β i * (γ i)⁻¹, fun i => mul_ne_zero (hβ0 i) (inv_ne_zero (hγ0 i)), fun e => ?_⟩
  obtain ⟨hW, hWres⟩ := hkey e
  obtain ⟨hξm, hξr⟩ := hξpow_mem (-(c e))
  have hsplit : IsLocalRing.residue A ⟨κc (tgt e) * (κc (src e))⁻¹ * ξ ^ (-(c e)), hW⟩ =
      IsLocalRing.residue A ⟨κc (tgt e) * (κc (src e))⁻¹, memA _ (hvr e)⟩ * (IsLocalRing.residue A ⟨ξ, hξA⟩) ^ (-(c e)) := by
    rw [← hξr, ← map_mul]
    congr 1
  rw [hsplit] at hWres
  show (IsLocalRing.residue A ⟨ξ, hξA⟩) ^ (c e) * (β (src e) * (γ (src e))⁻¹) = β (tgt e) * (γ (tgt e))⁻¹
  rw [hβedge e]
  set ρ := IsLocalRing.residue A ⟨κc (tgt e) * (κc (src e))⁻¹, memA _ (hvr e)⟩ with hρ
  set ζ := IsLocalRing.residue A ⟨ξ, hξA⟩ with hζ
  have hρ0 : ρ ≠ 0 := resne _ (hvr e)
  have hζ0 : ζ ≠ 0 := hξres

  rw [← hWres, zpow_neg]
  field_simp

open ChartPrincipalMomentEngine in
theorem solution
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (ξ : ℕ → L) (hξ0 : ξ 0 = 1) (hξ : ∀ k, ξ (k + 1) ^ ℓ = ξ k) (hξ1 : ξ 1 ≠ 1)
    (k : ℕ) (c : Fin m → ℤ)
    (Q Q' : Fin m → Place L F) (hQ : ∀ e, Q e ∈ (An e).dom) (hQ' : ∀ e, Q' e ∈ (An e).dom)
    (hQrat : ∀ e, ∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Q e).evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d)
    (hQQ' : ∀ e, (Q' e).evalAt (An e).param = ξ k * (Q e).evalAt (An e).param)
    (Di : Fin n → Divisor L F) (hDi : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hred : ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0)
    {ι : Type} [Fintype ι] (eq : ι → Fin m) (nq : ι → ℤ) (Qq : ι → Fin 4 → Place L F)
    (hQq : ∀ j l, Qq j l ∈ (An (eq j)).dom)
    (hrad : ∀ j, ∃ u : Aˣ,
      (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param)
    (hbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
        (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L)))
    (hprin : (∑ e, c e • ((Finsupp.single (Q e) 1 : Divisor L F) - Finsupp.single (Q' e) 1)) - (∑ i, Di i)
      - (∑ j, nq j • ((Finsupp.single (Qq j 0) 1 : Divisor L F) + Finsupp.single (Qq j 1) 1
          - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1)) ∈
      Divisor.principal (K := L) (F := F))
    :
    ∃ (hξA : ξ k ∈ A) (b : Fin n → IsLocalRing.ResidueField A), (∀ i, b i ≠ 0) ∧
      ∀ e, (IsLocalRing.residue A ⟨ξ k, hξA⟩) ^ (c e) * b (src e) = b (tgt e) := by
  classical
  obtain ⟨f, hf, hG⟩ := hprin

  choose κc hκc hres using fun i => (C i).exists_smul_mem f hf
  have hmod0 : ∀ e, ((An e).modulus : L) ≠ 0 := fun e => (hpair e).2.2.1
  have hwpos : ∀ e, 0 < w e := by
    intro e
    by_contra h0
    have h0' : w e = 0 := Nat.eq_zero_of_not_pos h0
    obtain ⟨u, hu⟩ := hw e
    rw [h0', pow_zero, mul_one] at hu
    have hm := (An e).modulus_mem
    rw [hu, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
    exact hm u.isUnit

  set pair : Fin m → Divisor L F := fun e => (Finsupp.single (Q e) 1 : Divisor L F) - Finsupp.single (Q' e) 1 with hpairdef
  set quad : ι → Divisor L F := fun j => (Finsupp.single (Qq j 0) 1 : Divisor L F) + Finsupp.single (Qq j 1) 1
      - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1 with hquaddef
  have hpair_apply : ∀ e P, pair e P = (if Q e = P then 1 else 0) - (if Q' e = P then 1 else 0) := by
    intro e P; rw [hpairdef, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  have hquad_apply : ∀ j P, quad j P = (if Qq j 0 = P then 1 else 0) + (if Qq j 1 = P then 1 else 0)
      - (if Qq j 2 = P then 1 else 0) - (if Qq j 3 = P then 1 else 0) := by
    intro j P
    rw [hquaddef, Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      Finsupp.single_apply, Finsupp.single_apply]
  have hpair_zero : ∀ e P, P ∉ (An e).dom → pair e P = 0 := by
    intro e P hP
    rw [hpair_apply, if_neg (fun h : Q e = P => hP (h ▸ hQ e)), if_neg (fun h : Q' e = P => hP (h ▸ hQ' e)), sub_self]
  have hquad_zero : ∀ j P, P ∉ (An (eq j)).dom → quad j P = 0 := by
    intro j P hP
    rw [hquad_apply, if_neg (fun h : Qq j 0 = P => hP (h ▸ hQq j 0)), if_neg (fun h : Qq j 1 = P => hP (h ▸ hQq j 1)),
      if_neg (fun h : Qq j 2 = P => hP (h ▸ hQq j 2)), if_neg (fun h : Qq j 3 = P => hP (h ▸ hQq j 3))]
    simp
  have hGdef : ∀ P, ((∑ e, c e • ((Finsupp.single (Q e) 1 : Divisor L F) - Finsupp.single (Q' e) 1)) - (∑ i, Di i)
      - (∑ j, nq j • ((Finsupp.single (Qq j 0) 1 : Divisor L F) + Finsupp.single (Qq j 1) 1
          - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1))) P =
      (∑ e, c e * pair e P) - (∑ i, Di i P) - ∑ j, nq j * quad j P := by
    intro P
    simp only [hpairdef, hquaddef, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

  have hGchart : ∀ i, ∀ P ∈ (C i).dom, P.ord f = -(Di i P) := by
    intro i P hP
    rw [← hG P, hGdef]
    rcases hcover P with ⟨i', hi', huniq, hnoA⟩ | ⟨e', he', -, hnoC⟩
    · have h1 : ∑ e, c e * pair e P = 0 :=
        Finset.sum_eq_zero (fun e _ => by rw [hpair_zero e P (hnoA e), mul_zero])
      have h2 : ∑ j, nq j * quad j P = 0 :=
        Finset.sum_eq_zero (fun j _ => by rw [hquad_zero j P (hnoA (eq j)), mul_zero])
      have h3 : ∑ j, Di j P = Di i P := by
        rw [Finset.sum_eq_single i]
        · intro j _ hji
          by_contra hne
          exact hji ((huniq j (hDi j P (Finsupp.mem_support_iff.mpr hne))).trans (huniq i hP).symm)
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [h1, h2, h3]; ring
    · exact absurd hP (hnoC i)

  set N : Fin m → Divisor L F := fun e => c e • pair e - ∑ j ∈ Finset.univ.filter (fun j => eq j = e), nq j • quad j with hNdef
  have hN_apply : ∀ e P, N e P = c e * pair e P - ∑ j ∈ Finset.univ.filter (fun j => eq j = e), nq j * quad j P := by
    intro e P
    simp only [hNdef, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  have hGann : ∀ e, ∀ P ∈ (An e).dom, P.ord f = N e P := by
    intro e P hP
    rw [← hG P, hGdef, hN_apply]
    rcases hcover P with ⟨i', hi', -, hnoA⟩ | ⟨e', he', huniq, hnoC⟩
    · exact absurd hP (hnoA e)
    · have h1 : ∑ j, Di j P = 0 := Finset.sum_eq_zero (fun j _ => by
        by_contra hne; exact hnoC j (hDi j P (Finsupp.mem_support_iff.mpr hne)))
      have h2 : ∑ e'', c e'' * pair e'' P = c e * pair e P := by
        rw [Finset.sum_eq_single e]
        · intro e'' _ hne
          rw [hpair_zero e'' P (fun h => hne ((huniq e'' h).trans (huniq e hP).symm)), mul_zero]
        · intro h; exact absurd (Finset.mem_univ e) h
      have h3 : ∑ j, nq j * quad j P = ∑ j ∈ Finset.univ.filter (fun j => eq j = e), nq j * quad j P := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => eq j = e), add_eq_left]
        refine Finset.sum_eq_zero (fun j hj => ?_)
        rw [Finset.mem_filter] at hj
        rw [hquad_zero j P (fun h => hj.2 ((huniq (eq j) h).trans (huniq e hP).symm)), mul_zero]
      rw [h1, h2, h3]; ring

  set Dc : Fin n → Divisor L F := fun i => -Di i with hDcdef
  have hdomc : ∀ i, ∀ P ∈ (Dc i).support, P ∈ (C i).dom := by
    intro i P hP; rw [hDcdef, Finsupp.support_neg] at hP; exact hDi i P hP
  have hDic : ∀ i, ∀ P ∈ (C i).dom, Dc i P = P.ord f := by
    intro i P hP; rw [hDcdef, Finsupp.neg_apply, hGchart i P hP]
  have hDoff : ∀ i P, P ∉ (C i).dom → Dc i P = 0 := fun i P hP => by
    by_contra h
    exact hP (hdomc i P (Finsupp.mem_support_iff.mpr h))
  have hmass : ∀ i, ((Dc i).sum fun _ k => k) = 0 := by
    intro i
    have h1 : ((Di i).sum fun _ k => k) = 0 := by
      rw [← sum_mapDomain (C i) (Di i), hred i, Finsupp.sum_zero_index]
    rw [← LC2.mass_eq_sum, hDcdef, map_neg, LC2.mass_eq_sum, h1, neg_zero]

  have hNoff : ∀ e P, P ∉ (An e).dom → N e P = 0 := by
    intro e P hP
    rw [hN_apply, hpair_zero e P hP, mul_zero, zero_sub, neg_eq_zero]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [Finset.mem_filter] at hj
    rw [hquad_zero j P (fun h => hP (hj.2 ▸ h)), mul_zero]
  have hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom := by
    intro e P hP
    by_contra h
    exact (Finsupp.mem_support_iff.mp hP) (hNoff e P h)
  have hN : ∀ e, ∀ P ∈ (An e).dom, N e P = P.ord f := fun e P hP => (hGann e P hP).symm
  have hNsum : ∀ e, ((N e).sum fun _ k => k) = 0 := by
    intro e
    rw [← LC2.mass_eq_sum, hNdef, map_sub, map_zsmul, map_sum, hpairdef, map_sub, LC2.mass_single, LC2.mass_single]
    simp only [map_zsmul, hquaddef, map_sub, map_add, LC2.mass_single]
    simp

  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have hξpow : ∀ k, ξ k ^ (ℓ ^ k) = 1 := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_one, hξ0]
    | succ j ih => rw [pow_succ', pow_mul, hξ j, ih]
  have hvξ : A.valuation (ξ k) = 1 := by
    have h1 : A.valuation (ξ k) ^ (ℓ ^ k) = 1 := by rw [← map_pow, hξpow, map_one]
    exact (pow_eq_one_iff.mp h1).resolve_right (pow_ne_zero k hℓpos.ne')
  have hξ0' : ξ k ≠ 0 := fun h => by rw [h, map_zero] at hvξ; exact zero_ne_one hvξ
  have hξA : ξ k ∈ A := (A.valuation_le_one_iff _).mp hvξ.le
  have hz0 : ∀ e, ∀ P ∈ (An e).dom, P.evalAt (An e).param ≠ 0 := fun e P hP => ((An e).mem_dom P hP).2.2.2.1
  have hvz0 : ∀ e, ∀ P ∈ (An e).dom, A.valuation (P.evalAt (An e).param) ≠ 0 :=
    fun e P hP => (map_ne_zero _).mpr (hz0 e P hP)

  have hquad_moment : ∀ j,
      ((quad j).prod fun P k => LC2.star (fun P => A.valuation (P.evalAt (An (eq j)).param)) P ^ k) = 1 := by
    intro j
    obtain ⟨t, ht, hbalj⟩ := hbal j
    have hvt : A.valuation (1 + ((t : A) : L)) = 1 := by
      have : (1 + t : A) ∉ IsLocalRing.maximalIdeal A := by
        intro h
        have := (IsLocalRing.maximalIdeal A).sub_mem h ht
        rw [add_sub_cancel_right] at this
        exact (IsLocalRing.maximalIdeal A).ne_top_iff_one.mp (Ideal.IsMaximal.ne_top inferInstance) this
      have hu : IsUnit (1 + t : A) := by
        by_contra hnu; exact this ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      have := A.valuation_unit hu.unit
      simpa using this
    have hv : A.valuation ((Qq j 0).evalAt (An (eq j)).param) * A.valuation ((Qq j 1).evalAt (An (eq j)).param) =
        A.valuation ((Qq j 2).evalAt (An (eq j)).param) * A.valuation ((Qq j 3).evalAt (An (eq j)).param) := by
      rw [← map_mul, ← map_mul, hbalj, map_mul, hvt, mul_one]
    rw [hquaddef, LC2.prod_star_sub, LC2.prod_star_sub, LC2.prod_star_add, LC2.prod_star_single, LC2.prod_star_single,
      LC2.prod_star_single, LC2.prod_star_single, zpow_one, zpow_one, zpow_one, zpow_one,
      LC2.star_of_ne_zero _ (hvz0 _ _ (hQq j 0)), LC2.star_of_ne_zero _ (hvz0 _ _ (hQq j 1)),
      LC2.star_of_ne_zero _ (hvz0 _ _ (hQq j 2)), LC2.star_of_ne_zero _ (hvz0 _ _ (hQq j 3)), hv]
    field_simp [hvz0 _ _ (hQq j 2), hvz0 _ _ (hQq j 3)]
  have hNprod : ∀ e, ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) = 1 := by
    intro e
    rw [← LC2.prod_star_eq_prod _ (N e) (fun P hP => hvz0 e P (hNdom e P hP)), hNdef, LC2.prod_star_sub,
      LC2.prod_star_zsmul, LC2.prod_star_sum, hpairdef, LC2.prod_star_sub, LC2.prod_star_single, LC2.prod_star_single,
      zpow_one, zpow_one, LC2.star_of_ne_zero _ (hvz0 e _ (hQ e)), LC2.star_of_ne_zero _ (hvz0 e _ (hQ' e)), hQQ' e,
      map_mul, hvξ, one_mul, mul_inv_cancel₀ (hvz0 e _ (hQ e)), one_zpow, one_mul]
    rw [inv_eq_one]
    refine Finset.prod_eq_one (fun j hj => ?_)
    rw [Finset.mem_filter] at hj
    rw [LC2.prod_star_zsmul, ← hj.2, hquad_moment j, one_zpow]

  set g : ∀ i, Fbar i := fun i => (C i).residue ⟨κc i • f, hκc i⟩ with hg
  set s : Fin m → ℤ := fun e => (xt e).ord (g (tgt e)) with hs

  have hedge : ∀ e, (xs e).ord (g (src e)) + s e = 0 ∧
      A.valuation (κc (src e)) * (A.valuation (κc (tgt e)))⁻¹ *
        A.valuation ((An e).modulus : L) ^ (s e) = 1 := fun e =>
    end_orders (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e) (C (src e)) (xs e) (hatt e).1
      (C (tgt e)) (xt e) (hatt e).2 (wide_of_isAlgClosed (An e) (hmod0 e)) (N e) (hNdom e) (hN e)
      (hNsum e) (hNprod e) (hκc (src e)) (hres (src e)) (hκc (tgt e)) (hres (tgt e))

  have hvert : ∀ i, ∑ x ∈ (C i).nodes, x.ord (g i) = 0 := fun i =>
    sum_nodes_ord_eq_zero (hratBar i) (C i) (hκc i) (hres i) (Dc i) (hDic i) (hDoff i) (hmass i)

  have hnodesum : ∀ (φ : ∀ j, Place (IsLocalRing.ResidueField A) (Fbar j) → ℤ) (i : Fin n),
      ∑ x ∈ (C i).nodes, φ i x =
        (∑ e ∈ Finset.univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
          ∑ e ∈ Finset.univ.filter (fun e => src e = i), φ (src e) (xs e) :=
    sum_nodes_eq_sum_ends (fun i => (C i).nodes) src tgt xs xt (fun e => (hatt e).1.1)
      (fun e => (hatt e).2.1) hnodes.1 hnodes.2

  have hc0 : ∀ i, κc i ≠ 0 := fun i => const_ne_zero (C i) (hκc i) (hres i)
  have hvc : ∀ i, A.valuation (κc i) ≠ 0 := fun i => (Valuation.ne_zero_iff _).mpr (hc0 i)
  have hπL : (π : L) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hvπ0 : A.valuation (π : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hπL
  have hvπ1 : A.valuation (π : L) < 1 := (A.valuation_lt_one_iff π).mp hπ
  have hslope : ∀ e, s e = 0 := by
    let hgt : Fin n → Additive (A.ValueGroup)ˣ :=
      fun i => Additive.ofMul (Units.mk0 (A.valuation (κc i)) (hvc i))
    let vπ : Additive (A.ValueGroup)ˣ := Additive.ofMul (Units.mk0 (A.valuation (π : L)) hvπ0)
    have hvπ : vπ ≠ 0 := by
      intro h
      have h' : Units.mk0 (A.valuation (π : L)) hvπ0 = 1 := by simpa [vπ] using h
      have h'' : A.valuation (π : L) = 1 := by
        have := congrArg (fun u : (A.ValueGroup)ˣ => (u : A.ValueGroup)) h'
        simpa using this
      exact absurd h'' hvπ1.ne
    have hgrad : ∀ e, hgt (tgt e) - hgt (src e) = ((w e : ℤ) * s e) • vπ := by
      intro e
      obtain ⟨-, hprod⟩ := hedge e
      obtain ⟨u, hu⟩ := hw e
      have hvm : A.valuation ((An e).modulus : L) = A.valuation (π : L) ^ (w e) := by
        rw [hu]
        push_cast
        rw [map_mul, map_pow, A.valuation_unit u, one_mul]
      have key : A.valuation (κc (tgt e)) * (A.valuation (κc (src e)))⁻¹ =
          A.valuation (π : L) ^ ((w e : ℤ) * s e) := by
        rw [zpow_mul, zpow_natCast, ← hvm]
        rw [mul_assoc] at hprod
        have := eq_inv_of_mul_eq_one_left hprod
        rw [this, inv_inv, ← mul_assoc, mul_inv_cancel₀ (hvc (tgt e)), one_mul]
      show Additive.ofMul _ - Additive.ofMul _ = ((w e : ℤ) * s e) • Additive.ofMul _
      rw [sub_eq_add_neg, ← ofMul_inv, ← ofMul_mul, ← ofMul_zpow]
      congr 1
      ext
      push_cast
      exact key
    refine WeightedMultigraph.slope_eq_zero_of_gradient_of_harmonic src tgt w hwpos vπ hvπ hgt s hgrad ?_
    intro i
    have h := hnodesum (fun j x => x.ord (g j)) i
    rw [hvert i] at h
    have hneg : ∑ e ∈ Finset.univ.filter (fun e => src e = i), (xs e).ord (g (src e)) =
        -∑ e ∈ Finset.univ.filter (fun e => src e = i), s e := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun e _ => ?_
      linarith [(hedge e).1]
    rw [hneg] at h
    linarith

  have hnode0 : ∀ i, ∀ x ∈ (C i).nodes, x.ord (g i) = 0 := by
    intro i
    have h := hnodesum (fun j x => (x.ord (g j)) ^ 2) i
    have hR : (∑ e ∈ Finset.univ.filter (fun e => tgt e = i), ((xt e).ord (g (tgt e))) ^ 2) +
        ∑ e ∈ Finset.univ.filter (fun e => src e = i), ((xs e).ord (g (src e))) ^ 2 = 0 := by
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro e _
        have : (xs e).ord (g (src e)) = 0 := by linarith [(hedge e).1, hslope e]
        rw [this]; rfl
      · intro e _
        have : (xt e).ord (g (tgt e)) = 0 := hslope e
        rw [this]; rfl
    rw [hR] at h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (x.ord (g i)))).mp h
    intro x hx
    exact pow_eq_zero_iff two_ne_zero |>.mp (hall x hx)

  have hordg : ∀ i (x : Place (ResidueField A) (Fbar i)), x.ord (g i) = 0 := by
    intro i x
    by_cases hx : x ∈ (C i).nodes
    · exact hnode0 i x hx
    · rw [← mapDomain_eq_ord_of_not_mem_nodes (C i) (hκc i) (hres i) (Dc i) (hDic i) (hDoff i) x hx, hDcdef]
      show (Finsupp.mapDomain.addMonoidHom (C i).placeMap (-Di i)) x = 0
      rw [map_neg, Finsupp.neg_apply, neg_eq_zero]
      show Finsupp.mapDomain (C i).placeMap (Di i) x = 0
      rw [hred i, Finsupp.zero_apply]
  haveI hκalg : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hconst : ∀ i, ∃ γ : ResidueField A, γ ≠ 0 ∧ algebraMap (ResidueField A) (Fbar i) γ = g i := by
    intro i
    obtain ⟨t, ht, hfin, -⟩ :=
      AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := ResidueField A) (F := Fbar i)
    haveI := hfin
    obtain ⟨γ, hγ⟩ := RingHom.mem_range.mp
      (AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed t ht (hordg i))
    refine ⟨γ, fun h0 => hres i ?_, hγ⟩
    show g i = 0
    rw [← hγ, h0, map_zero]
  choose γ hγ0 hγ using hconst

  have hveq : ∀ e, A.valuation (κc (src e)) = A.valuation (κc (tgt e)) := by
    intro e
    obtain ⟨-, hprod⟩ := hedge e
    rw [hslope e, zpow_zero, mul_one] at hprod
    have := eq_inv_of_mul_eq_one_left hprod
    rw [inv_inv] at this
    exact this

  choose tq htq hbalq using hbal
  have htqA : ∀ j, (1 + ((tq j : A) : L)) ∈ A := fun j => add_mem (one_mem A) (tq j).2
  have hres_tq : ∀ j, IsLocalRing.residue A ⟨1 + ((tq j : A) : L), htqA j⟩ = 1 := by
    intro j
    rw [show (⟨1 + ((tq j : A) : L), htqA j⟩ : A) = 1 + tq j from Subtype.ext (by push_cast; rfl), map_add, map_one,
      (IsLocalRing.residue_eq_zero_iff _).mpr (htq j), add_zero]
  have hres_tq_ne : ∀ j, IsLocalRing.residue A ⟨1 + ((tq j : A) : L), htqA j⟩ ≠ 0 := fun j => by
    rw [hres_tq j]; exact one_ne_zero

  have zpowA : ∀ (x : L) (hx : x ∈ A), IsLocalRing.residue A ⟨x, hx⟩ ≠ 0 → ∀ nn : ℤ,
      ∃ hmem : x ^ nn ∈ A, IsLocalRing.residue A ⟨x ^ nn, hmem⟩ = (IsLocalRing.residue A ⟨x, hx⟩) ^ nn := by
    intro x hx hresx nn
    have hunit : IsUnit (⟨x, hx⟩ : A) := by
      by_contra h
      exact hresx ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr h))
    obtain ⟨U, hU⟩ := hunit
    have hval : ((U ^ nn : Aˣ) : A).1 = x ^ nn := by
      have : ((Units.map (A.subtype : A →* L) (U ^ nn) : Lˣ) : L) = ((Units.map (A.subtype : A →* L) U) ^ nn : Lˣ) := by
        rw [map_zpow]
      rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map] at this
      rw [MonoidHom.coe_coe, hU] at this
      exact this
    refine ⟨hval ▸ ((U ^ nn : Aˣ) : A).2, ?_⟩
    rw [show (⟨x ^ nn, hval ▸ ((U ^ nn : Aˣ) : A).2⟩ : A) = ((U ^ nn : Aˣ) : A) from Subtype.ext hval.symm]
    have : (Units.map (IsLocalRing.residue A : A →* ResidueField A) (U ^ nn) : ResidueField A) =
        ((Units.map (IsLocalRing.residue A : A →* ResidueField A) U) ^ nn : (ResidueField A)ˣ) := by rw [map_zpow]
    rw [Units.coe_map, Units.val_zpow_eq_zpow_val, Units.coe_map, MonoidHom.coe_coe, hU] at this
    exact this

  have memA_of_v1 : ∀ x : L, A.valuation x = 1 → x ∈ A := fun x h => (A.valuation_le_one_iff x).mp h.le
  have res_ne_of_v1 : ∀ (x : L) (h : A.valuation x = 1), IsLocalRing.residue A ⟨x, memA_of_v1 x h⟩ ≠ 0 := by
    intro x h h0
    have hu : IsUnit (⟨x, memA_of_v1 x h⟩ : A) := (A.valuation_eq_one_iff _).mpr h
    exact ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0)) hu

  have hkey : ∀ e, ∃ hW : κc (tgt e) * (κc (src e))⁻¹ * (ξ k) ^ (-(c e)) ∈ A,
      IsLocalRing.residue A ⟨_, hW⟩ * γ (src e) = γ (tgt e) := by
    intro e

    have hzpar : (An e).param ≠ 0 := param_ne_zero (An e) (hQ e)
    have hp' : (An' e).param = algebraMap L F ((An e).modulus : L) * (An e).param⁻¹ :=
      (eq_mul_inv_iff_mul_eq₀ hzpar).mpr (hpair e).2.2.2
    have hca0 : κc (src e) ≠ 0 := hc0 (src e)
    have hcb0 : κc (tgt e) ≠ 0 := hc0 (tgt e)
    set c' : L := κc (src e) * (κc (tgt e))⁻¹ with hc'
    have hc'0 : c' ≠ 0 := mul_ne_zero hca0 (inv_ne_zero hcb0)
    have hh0 : κc (src e) • f ≠ 0 := smul_ne_zero hca0 hf
    have heq : (algebraMap L F c')⁻¹ * (κc (src e) • f) = κc (tgt e) • f := by
      have hca' : algebraMap L F (κc (src e)) ≠ 0 := (map_ne_zero _).mpr hca0
      rw [hc', Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀]
      field_simp
    have hhb : (algebraMap L F c')⁻¹ * (κc (src e) • f) ∈ (C (tgt e)).integers := heq ▸ hκc (tgt e)
    have hsub : (⟨(algebraMap L F c')⁻¹ * (κc (src e) • f), hhb⟩ : (C (tgt e)).integers) = ⟨κc (tgt e) • f, hκc (tgt e)⟩ :=
      Subtype.ext heq
    have hresb' : (C (tgt e)).residue ⟨(algebraMap L F c')⁻¹ * (κc (src e) • f), hhb⟩ ≠ 0 := by rw [hsub]; exact hres (tgt e)
    have hordh : ∀ P ∈ (An e).dom, N e P = P.ord (κc (src e) • f) := fun P hP => by
      rw [ord_smul P hca0 hf]; exact hN e P hP
    obtain ⟨hu, -, hlam⟩ :=
      AlgebraicCurve.Annulus.exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached A hrk
        (hratBar (src e)) (hratBar (tgt e)) (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e)
        (C (src e)) (xs e) (hatt e).1 (C (tgt e)) (xt e) (hatt e).2
        (κc (src e) • f) hh0 (hκc (src e)) (hres (src e)) c' hc'0 hhb hresb' (N e) (hNdom e) hordh

    have hσa : (xs e).ord ((C (src e)).residue ⟨κc (src e) • f, hκc (src e)⟩) = 0 := hnode0 (src e) (xs e) (hatt e).1.1
    have hσb : (xt e).ord ((C (tgt e)).residue ⟨(algebraMap L F c')⁻¹ * (κc (src e) • f), hhb⟩) = 0 := by
      rw [hsub]; exact hnode0 (tgt e) (xt e) (hatt e).2.1
    have hlama : (xs e).evalAt ((C (src e)).residue ⟨κc (src e) • f, hκc (src e)⟩ *
        ((C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩) ^ (-((xs e).ord ((C (src e)).residue ⟨κc (src e) • f, hκc (src e)⟩)))) =
        γ (src e) := by
      rw [hσa, neg_zero, zpow_zero, mul_one]
      show (xs e).evalAt (g (src e)) = γ (src e)
      rw [← hγ (src e), Place.evalAt_algebraMap_eq]
    have hlamb : (xt e).evalAt ((C (tgt e)).residue ⟨(algebraMap L F c')⁻¹ * (κc (src e) • f), hhb⟩ *
        ((C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩) ^ (-((xt e).ord ((C (tgt e)).residue ⟨(algebraMap L F c')⁻¹ * (κc (src e) • f), hhb⟩)))) =
        γ (tgt e) := by
      rw [hσb, neg_zero, zpow_zero, mul_one, hsub]
      show (xt e).evalAt (g (tgt e)) = γ (tgt e)
      rw [← hγ (tgt e), Place.evalAt_algebraMap_eq]
    rw [hlama, hlamb] at hlam

    have hzq : ∀ j l, (Qq j l).evalAt (An (eq j)).param ≠ 0 := fun j l => hz0 _ _ (hQq j l)
    set S : Finset ι := Finset.univ.filter (fun j => eq j = e) with hS
    obtain hτmem : ∀ j, ∃ hmem : (1 + ((tq j : A) : L)) ^ (nq j) ∈ A,
        IsLocalRing.residue A ⟨_, hmem⟩ = 1 := by
      intro j
      obtain ⟨hmem, hres1⟩ := zpowA _ (htqA j) (hres_tq_ne j) (nq j)
      exact ⟨hmem, by rw [hres1, hres_tq j, one_zpow]⟩
    choose hτjA hτjres using hτmem
    set T : A := ∏ j ∈ S, (⟨(1 + ((tq j : A) : L)) ^ (nq j), hτjA j⟩ : A) with hT
    have hTval : (T : L) = ∏ j ∈ S, (1 + ((tq j : A) : L)) ^ (nq j) := by
      rw [hT]; push_cast; rfl
    have hTres : IsLocalRing.residue A T = 1 := by
      rw [hT, map_prod]; exact Finset.prod_eq_one (fun j _ => hτjres j)
    have hT0 : (T : L) ≠ 0 := by
      rw [hTval]
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => zpow_ne_zero _ (fun h0 => by
        have := hres_tq j
        rw [show (⟨1 + ((tq j : A) : L), htqA j⟩ : A) = 0 from Subtype.ext h0, map_zero] at this
        exact zero_ne_one this))

    have hPiN : ((N e).prod fun P k => (-(P.evalAt (An e).param)) ^ k) = ((ξ k)⁻¹) ^ (c e) * ((T : L))⁻¹ := by
      have hneg0 : ∀ P ∈ (N e).support, (fun P => -(P.evalAt (An e).param)) P ≠ 0 :=
        fun P hP => neg_ne_zero.mpr (hz0 e P (hNdom e P hP))
      rw [← LC2.prod_star_eq_prod (fun P => -(P.evalAt (An e).param)) (N e) hneg0, hNdef, LC2.prod_star_sub,
        LC2.prod_star_zsmul, LC2.prod_star_sum, hpairdef, LC2.prod_star_sub, LC2.prod_star_single, LC2.prod_star_single,
        zpow_one, zpow_one, LC2.star_of_ne_zero _ (neg_ne_zero.mpr (hz0 e _ (hQ e))),
        LC2.star_of_ne_zero _ (neg_ne_zero.mpr (hz0 e _ (hQ' e))), hQQ' e, hTval]
      congr 1
      · rw [show -((Q e).evalAt (An e).param) * (-(ξ k * (Q e).evalAt (An e).param))⁻¹ = (ξ k)⁻¹ from by
          field_simp [hz0 e _ (hQ e), hξ0']]
      · congr 1
        refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [Finset.mem_filter] at hj
        rw [LC2.prod_star_zsmul]
        congr 1
        rw [hquaddef, LC2.prod_star_sub, LC2.prod_star_sub, LC2.prod_star_add, LC2.prod_star_single, LC2.prod_star_single,
          LC2.prod_star_single, LC2.prod_star_single, zpow_one, zpow_one, zpow_one, zpow_one]
        rw [← hj.2]
        rw [LC2.star_of_ne_zero _ (neg_ne_zero.mpr (hzq j 0)), LC2.star_of_ne_zero _ (neg_ne_zero.mpr (hzq j 1)),
          LC2.star_of_ne_zero _ (neg_ne_zero.mpr (hzq j 2)), LC2.star_of_ne_zero _ (neg_ne_zero.mpr (hzq j 3))]
        rw [show -((Qq j 0).evalAt (An (eq j)).param) * -((Qq j 1).evalAt (An (eq j)).param) =
          (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((tq j : A) : L)) from by
            rw [neg_mul_neg, hbalq j]]
        field_simp [hzq j 2, hzq j 3]

    have hmassN : ((N e).sum fun _ k => k) = 0 := hNsum e
    have hval : c'⁻¹ * ((An e).modulus : L) ^ ((xs e).ord ((C (src e)).residue ⟨κc (src e) • f, hκc (src e)⟩) - ((N e).sum fun _ k => k)) *
        ((N e).prod fun P k => (-(P.evalAt (An e).param)) ^ k) * (T : L) =
        κc (tgt e) * (κc (src e))⁻¹ * (ξ k) ^ (-(c e)) := by
      rw [hσa, hmassN, sub_self, zpow_zero, mul_one, hPiN, hc', inv_zpow', zpow_neg]
      field_simp
    have hW : κc (tgt e) * (κc (src e))⁻¹ * (ξ k) ^ (-(c e)) ∈ A := by
      rw [← hval]; exact mul_mem hu T.2
    refine ⟨hW, ?_⟩
    have hWeq : (⟨_, hW⟩ : A) = ⟨_, hu⟩ * T := Subtype.ext (by push_cast; rw [← hval])
    rw [hWeq, map_mul, hTres, mul_one]
    exact hlam

  obtain ⟨b, hb0, hb⟩ := LC2.exists_coboundary_of_residue_edge_law A n m src tgt κc hc0 hveq γ hγ0 (ξ k) hξA hvξ c hkey
  exact ⟨hξA, b, hb0, hb⟩

end S_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel (solution)
