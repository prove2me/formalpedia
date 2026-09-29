-- Prove2me | solution 1 for AlgebraicCurve.exists_residue_prod_zpow_eq_one_of_forall_mapDomain_placeMap_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one_of_semistableCovering_of_discFibres_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7fc360db-e5f4-5669-995c-2716abef4553

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_WeightedMultigraph_slope_eq_zero_of_gradient_of_harmonic
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_residue_prod_zpow_eq_one_of_forall_mapDomain_placeMap_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one_of_semistableCovering_of_discFibres_of_rankOne
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace CycleLawEngine

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

section Flow

variable {G : Type*} [CommGroup G] {n m : ℕ}

theorem zpow_finset_sum {ι : Type*} (a : G) (s : Finset ι) (k : ι → ℤ) :
    a ^ (∑ i ∈ s, k i) = ∏ i ∈ s, a ^ k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

theorem prod_zpow_comp_eq_prod_zpow_sum (v : Fin m → Fin n) (φ : Fin n → G) (ε : Fin m → ℤ) :
    ∏ e, φ (v e) ^ ε e = ∏ i, φ i ^ (∑ e, if v e = i then ε e else 0) := by
  classical
  have h : ∀ e, φ (v e) ^ ε e = ∏ i, (if v e = i then φ i ^ ε e else 1) := by
    intro e
    rw [Finset.prod_ite_eq]
    simp
  simp_rw [h]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_finset_sum]
  refine Finset.prod_congr rfl fun e _ => ?_
  split_ifs with he
  · rfl
  · rw [zpow_zero]

theorem prod_div_zpow_eq_one_of_flow (src tgt : Fin m → Fin n) (φ : Fin n → G) (ε : Fin m → ℤ)
    (hε : ∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) :
    ∏ e, (φ (src e) / φ (tgt e)) ^ ε e = 1 := by
  simp_rw [div_zpow]
  rw [Finset.prod_div_distrib, prod_zpow_comp_eq_prod_zpow_sum src φ ε,
    prod_zpow_comp_eq_prod_zpow_sum tgt φ ε]
  rw [Finset.prod_congr rfl fun i _ => by rw [hε i], div_self']

end Flow

section Constant

theorem transcendental_of_place {κ Fb : Type*} [Field κ] [IsAlgClosed κ] [Field Fb] [Algebra κ Fb]
    (x : Place κ Fb) : Algebra.Transcendental κ Fb := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  haveI : Algebra.IsIntegral κ Fb := ⟨fun y => (halg.isAlgebraic y).isIntegral⟩
  have hsurj : Function.Surjective (algebraMap κ Fb) := (IsAlgClosed.algebraMap_bijective_of_isIntegral).2
  apply x.ne_top'
  ext f
  refine ⟨fun _ => ValuationSubring.mem_top f, fun _ => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj f
  exact x.algebraMap_mem' a

theorem exists_eq_algebraMap_of_forall_ord_eq_zero {κ Fb : Type*} [Field κ] [IsAlgClosed κ] [Field Fb]
    [Algebra κ Fb] [IsCurveOver κ Fb] [Algebra.EssFiniteType κ Fb] (x : Place κ Fb) {g : Fb}
    (hg : ∀ x : Place κ Fb, x.ord g = 0) : ∃ γ : κ, g = algebraMap κ Fb γ := by
  haveI := transcendental_of_place x
  obtain ⟨j, hj, -, -⟩ :=
    AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
      (K := κ) (F := Fb) IsCurveOver.finrank_kaehler
  haveI : FiniteDimensional (IntermediateField.adjoin κ ({j} : Set Fb)) Fb :=
    AlgebraicCurve.IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType hj
  obtain ⟨γ, hγ⟩ := RingHom.mem_range.mp
    (AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj hg)
  exact ⟨γ, hγ.symm⟩

end Constant

section Products

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_prod_zpow (v : Place K F) {ι : Type*} (s : Finset ι) (g : ι → F) (k : ι → ℤ)
    (hg : ∀ i ∈ s, g i ≠ 0) :
    (∏ i ∈ s, g i ^ k i) ≠ 0 ∧ v.ord (∏ i ∈ s, g i ^ k i) = ∑ i ∈ s, k i * v.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, by simp [Place.ord_one]⟩
  | insert a s ha ih =>
    obtain ⟨hne, hord⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
    have hza : g a ^ k a ≠ 0 := zpow_ne_zero _ hga
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert ha]; exact mul_ne_zero hza hne
    · rw [Finset.prod_insert ha, Finset.sum_insert ha, v.ord_mul hza hne, v.ord_zpow, hord]

theorem prod_neg_one_zpow {ι : Type*} (s : Finset ι) (k : ι → ℤ) :
    (∏ i ∈ s, (-1 : F) ^ k i) = (-1 : F) ^ (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (by norm_num : (-1 : F) ≠ 0)]

variable {Fb : Type*} [Field Fb]

theorem coe_unit_inv (R : ValuationSubring F) (u : Rˣ) :
    (((u⁻¹ : Rˣ) : R) : F) = (((u : Rˣ) : R) : F)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  exact congrArg Subtype.val u.inv_mul

theorem isUnit_of_res_ne_zero (R : ValuationSubring F) (res : R →+* Fb)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal R) {x : R} (hx : res x ≠ 0) : IsUnit x := by
  by_contra h
  have hmem : x ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal x).mpr h
  rw [← hker] at hmem
  exact hx hmem

theorem zpow_mem_and_res (R : ValuationSubring F) (res : R →+* Fb)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal R) {x : F} (hx : x ∈ R) {r : Fb}
    (hr : res ⟨x, hx⟩ = r) (hr0 : r ≠ 0) (k : ℤ) :
    ∃ h : x ^ k ∈ R, res ⟨x ^ k, h⟩ = r ^ k := by
  obtain ⟨u, hu⟩ := isUnit_of_res_ne_zero R res hker (x := ⟨x, hx⟩) (by rw [hr]; exact hr0)

  have hval : ∀ j : ℤ, (((u ^ j : Rˣ) : R) : F) = x ^ j := by
    intro j
    have h1 : ((Units.map R.subtype.toMonoidHom (u ^ j) : Fˣ) : F) = (((u ^ j : Rˣ) : R) : F) := rfl
    rw [← h1, map_zpow, Units.val_zpow_eq_zpow_val]
    congr 1
    show (((u : Rˣ) : R) : F) = x
    rw [hu]
  refine ⟨by rw [← hval k]; exact ((u ^ k : Rˣ) : R).2, ?_⟩
  have h2 : (⟨x ^ k, by rw [← hval k]; exact ((u ^ k : Rˣ) : R).2⟩ : R) = ((u ^ k : Rˣ) : R) :=
    Subtype.ext (hval k).symm
  rw [h2]
  have h3 : res ((u ^ k : Rˣ) : R) = ((Units.map res.toMonoidHom (u ^ k) : Fbˣ) : Fb) := rfl
  rw [h3, map_zpow, Units.val_zpow_eq_zpow_val]
  congr 1
  show res ((u : Rˣ) : R) = r
  rw [hu, hr]

theorem prod_zpow_mem_and_res (R : ValuationSubring F) (res : R →+* Fb)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal R) {ι : Type*} (s : Finset ι) (g : ι → F)
    (k : ι → ℤ) (r : Fb) (hr0 : r ≠ 0) (hg : ∀ i ∈ s, ∃ h : g i ∈ R, res ⟨g i, h⟩ = r) :
    ∃ h : (∏ i ∈ s, g i ^ k i) ∈ R, res ⟨∏ i ∈ s, g i ^ k i, h⟩ = r ^ (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp [one_mem], ?_⟩
    simp only [Finset.prod_empty, Finset.sum_empty, zpow_zero]
    exact map_one res
  | insert a s ha ih =>
    obtain ⟨hmem, hres⟩ := ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    obtain ⟨ha_mem, ha_res⟩ := hg a (Finset.mem_insert_self a s)
    obtain ⟨hka, hka_res⟩ := zpow_mem_and_res R res hker ha_mem ha_res hr0 (k a)
    refine ⟨by rw [Finset.prod_insert ha]; exact mul_mem hka hmem, ?_⟩
    have heq : (⟨∏ i ∈ insert a s, g i ^ k i, by rw [Finset.prod_insert ha]; exact mul_mem hka hmem⟩ : R) =
        ⟨g a ^ k a, hka⟩ * ⟨∏ i ∈ s, g i ^ k i, hmem⟩ :=
      Subtype.ext (by show (∏ i ∈ insert a s, g i ^ k i) = g a ^ k a * ∏ i ∈ s, g i ^ k i; exact Finset.prod_insert ha)
    rw [heq, map_mul, hka_res, hres, Finset.sum_insert ha, zpow_add₀ hr0]

end Products

section AnnulusFactor

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem mem_maximalIdeal_of_ord_eq_one (v : Place L F) {f : F} (hf : f ≠ 0) (h : v.ord f = 1) :
    (⟨f, v.mem_toValuationSubring_of_ord_nonneg_alt hf (by rw [h]; exact zero_le_one)⟩ : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rw [hu] at this
  change v.ord f = 0 at this
  rw [h] at this
  exact one_ne_zero this

theorem ord_param_sub_evalAt_of_ne (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom) (hQ : Q ∈ An.dom)
    (hne : Q ≠ P) : Q.ord (An.param - algebraMap L F (P.evalAt An.param)) = 0 := by

  obtain ⟨hQrat, hzQ, -, hzQ0, -⟩ := An.mem_dom Q hQ
  have hd : Q.evalAt An.param - P.evalAt An.param ≠ 0 := by
    intro h
    apply hne
    obtain ⟨cP, hcPm⟩ := (An.mem_dom P hP).2.2.1
    obtain ⟨R, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨P.evalAt An.param, cP⟩ hcPm (An.mem_dom P hP).2.2.2.1
      (An.mem_dom P hP).2.2.2.2
    exact (huniq Q ⟨hQ, sub_eq_zero.mp h⟩).trans (huniq P ⟨hP, rfl⟩).symm
  have h1 : Q.ord (An.param - algebraMap L F (Q.evalAt An.param)) = 1 := An.ord_param_sub Q hQ
  have hne0 : An.param - algebraMap L F (Q.evalAt An.param) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h1; exact zero_ne_one h1
  set a : Q.toValuationSubring := ⟨_, Q.mem_toValuationSubring_of_ord_nonneg_alt hne0 (by rw [h1]; exact zero_le_one)⟩
    with ha
  have ha_mem : a ∈ IsLocalRing.maximalIdeal Q.toValuationSubring := mem_maximalIdeal_of_ord_eq_one Q hne0 h1
  set b : Q.toValuationSubring := ⟨algebraMap L F (Q.evalAt An.param - P.evalAt An.param), Q.algebraMap_mem' _⟩
    with hb
  have hb_unit : IsUnit b := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap L F ((Q.evalAt An.param - P.evalAt An.param)⁻¹),
      Q.algebraMap_mem' _⟩, Subtype.ext ?_⟩
    show algebraMap L F (Q.evalAt An.param - P.evalAt An.param) *
      algebraMap L F ((Q.evalAt An.param - P.evalAt An.param)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  have hsum_unit : IsUnit (a + b) := by
    by_contra h
    have hm : a + b ∈ IsLocalRing.maximalIdeal Q.toValuationSubring := (IsLocalRing.mem_maximalIdeal _).mpr h
    have : b ∈ IsLocalRing.maximalIdeal Q.toValuationSubring := by
      have := Ideal.sub_mem _ hm ha_mem
      rwa [add_sub_cancel_left] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this hb_unit
  obtain ⟨u, hu⟩ := hsum_unit
  have hval : ((u : Q.toValuationSubring) : F) = An.param - algebraMap L F (P.evalAt An.param) := by
    rw [hu]
    show (An.param - algebraMap L F (Q.evalAt An.param)) + algebraMap L F (Q.evalAt An.param - P.evalAt An.param) = _
    rw [map_sub]; ring
  rw [← hval]
  exact Q.ord_coe_unit u

theorem param_sub_evalAt_ne_zero (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    An.param - algebraMap L F (P.evalAt An.param) ≠ 0 := by
  intro h0
  have h1 := An.ord_param_sub P hP
  rw [h0, Place.ord_zero] at h1
  exact zero_ne_one h1

theorem ord_weierstrassProd (An : Annulus A F) (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom)
    {Q : Place L F} (hQ : Q ∈ An.dom) :
    (N.prod fun P k => (An.param - algebraMap L F (P.evalAt An.param)) ^ k) ≠ 0 ∧
    Q.ord (N.prod fun P k => (An.param - algebraMap L F (P.evalAt An.param)) ^ k) = N Q := by
  classical
  obtain ⟨hne, hord⟩ := ord_prod_zpow Q N.support (fun P => An.param - algebraMap L F (P.evalAt An.param))
    (fun P => N P) (fun P hP => param_sub_evalAt_ne_zero An (hNdom P hP))
  refine ⟨hne, ?_⟩
  show Q.ord (∏ P ∈ N.support, (An.param - algebraMap L F (P.evalAt An.param)) ^ N P) = N Q
  rw [hord]
  have h : ∀ P ∈ N.support, N P * Q.ord (An.param - algebraMap L F (P.evalAt An.param)) =
      if P = Q then N Q else 0 := by
    intro P hP
    split_ifs with hPQ
    · rw [hPQ, An.ord_param_sub Q hQ, mul_one]
    · rw [ord_param_sub_evalAt_of_ne An (hNdom P hP) hQ (Ne.symm hPQ), mul_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with hQs
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hQs).symm

end AnnulusFactor

section EndResidues

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem algebraMap_mem_and_res_eq_zero (R : RegularProlongation A F Fb) {c : L} (hcA : c ∈ A)
    (hcm : (⟨c, hcA⟩ : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ h : algebraMap L F c ∈ R.integers, R.residue ⟨algebraMap L F c, h⟩ = 0 := by
  refine ⟨(R.algebraMap_mem_iff c).mpr hcA, ?_⟩
  have := R.residue_algebraMap ⟨c, hcA⟩
  rw [show (⟨algebraMap L F c, (R.algebraMap_mem_iff c).mpr hcA⟩ : R.integers) =
      ⟨algebraMap L F ((⟨c, hcA⟩ : A) : L), (R.algebraMap_mem_iff _).mpr (⟨c, hcA⟩ : A).2⟩ from rfl, this,
    (IsLocalRing.residue_eq_zero_iff _).mpr hcm, map_zero]

theorem weierstrassProd_mem_and_res_eq_one_src (An : Annulus A F) (R : RegularProlongation A F Fb)
    (x : Place (ResidueField A) Fb) (hz : An.param ∈ R.integers) (hx : x.ord (R.residue ⟨An.param, hz⟩) = 1)
    (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom) (hNsum : (N.sum fun _ k => k) = 0) :
    ∃ h : (N.prod fun P k => (An.param - algebraMap L F (P.evalAt An.param)) ^ k) ∈ R.integers,
      R.residue ⟨_, h⟩ = 1 := by
  classical
  have hzbar : R.residue ⟨An.param, hz⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hx; exact zero_ne_one hx
  have hfac : ∀ P ∈ N.support, ∃ h : An.param - algebraMap L F (P.evalAt An.param) ∈ R.integers,
      R.residue ⟨_, h⟩ = R.residue ⟨An.param, hz⟩ := by
    intro P hP
    obtain ⟨-, -, ⟨hcA, hcm⟩, -, -⟩ := An.mem_dom P (hNdom P hP)
    obtain ⟨hc, hc0⟩ := algebraMap_mem_and_res_eq_zero R hcA hcm
    refine ⟨sub_mem hz hc, ?_⟩
    rw [show (⟨An.param - algebraMap L F (P.evalAt An.param), sub_mem hz hc⟩ : R.integers) =
        ⟨An.param, hz⟩ - ⟨algebraMap L F (P.evalAt An.param), hc⟩ from rfl, map_sub, hc0, sub_zero]
  obtain ⟨h, hres⟩ := prod_zpow_mem_and_res R.integers R.residue R.ker_residue N.support
    (fun P => An.param - algebraMap L F (P.evalAt An.param)) (fun P => N P) _ hzbar hfac
  refine ⟨h, ?_⟩
  show R.residue ⟨∏ P ∈ N.support, (An.param - algebraMap L F (P.evalAt An.param)) ^ N P, h⟩ = 1
  rw [hres, show (∑ P ∈ N.support, N P) = N.sum (fun _ k => k) from rfl, hNsum, zpow_zero]

theorem weierstrassProd_eq_kummer_mul_tgt (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0)
    (R : RegularProlongation A F Fb) (x : Place (ResidueField A) Fb)
    (hz' : algebraMap L F (An.modulus : L) * An.param⁻¹ ∈ R.integers)
    (hx' : x.ord (R.residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hz'⟩) = 1)
    (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom) (hNsum : (N.sum fun _ k => k) = 0) :
    ∃ (V : F) (h : V ∈ R.integers), R.residue ⟨V, h⟩ = 1 ∧
      (N.prod fun P k => (An.param - algebraMap L F (P.evalAt An.param)) ^ k) =
        algebraMap L F (N.prod fun P k => (P.evalAt An.param) ^ k) * V := by
  classical
  have hz'bar : R.residue ⟨_, hz'⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hx'; exact zero_ne_one hx'
  obtain ⟨uz', huz'⟩ := RegularProlongation.isUnit_of_residue_ne_zero R hz'bar
  have hz'0 : algebraMap L F (An.modulus : L) * An.param⁻¹ ≠ 0 := by
    intro h0; apply hz'bar
    rw [show (⟨_, hz'⟩ : R.integers) = 0 from Subtype.ext h0, map_zero]
  have hz0 : An.param ≠ 0 := by
    intro h0; apply hz'0; rw [h0, inv_zero, mul_zero]

  have hz'inv_val : (((uz'⁻¹ : R.integersˣ) : R.integers) : F) = (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹ := by
    rw [coe_unit_inv, huz']
  have hinv : (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹ ∈ R.integers := by
    rw [← hz'inv_val]; exact ((uz'⁻¹ : R.integersˣ) : R.integers).2

  set V : Place L F → F := fun P =>
    1 - algebraMap L F ((An.modulus : L) * (P.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹
    with hV
  have hVfac : ∀ P ∈ N.support, ∃ h : V P ∈ R.integers, R.residue ⟨V P, h⟩ = 1 := by
    intro P hP
    obtain ⟨-, -, ⟨hcA, hcm⟩, hc0, m, hm, hmod⟩ := An.mem_dom P (hNdom P hP)

    have hquot : (An.modulus : L) * (P.evalAt An.param)⁻¹ = (m : L) := by
      rw [hmod, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    obtain ⟨hmR, hm0⟩ := algebraMap_mem_and_res_eq_zero R m.2 (by simpa using hm)
    have hmR' : algebraMap L F ((An.modulus : L) * (P.evalAt An.param)⁻¹) ∈ R.integers := by
      rw [hquot]; exact hmR
    have hres_m : R.residue ⟨_, hmR'⟩ = 0 := by
      rw [show (⟨_, hmR'⟩ : R.integers) = ⟨algebraMap L F (m : L), hmR⟩ from Subtype.ext (by
        show algebraMap L F ((An.modulus : L) * (P.evalAt An.param)⁻¹) = algebraMap L F (m : L); rw [hquot])]
      exact hm0
    have hmemV : V P ∈ R.integers := sub_mem (one_mem _) (mul_mem hmR' hinv)
    refine ⟨hmemV, ?_⟩
    have : (⟨V P, hmemV⟩ : R.integers) = 1 - ⟨_, hmR'⟩ * ⟨_, hinv⟩ := Subtype.ext rfl
    rw [this, map_sub, map_one, map_mul, hres_m, zero_mul, sub_zero]

  have hsplit : ∀ P ∈ N.support, An.param - algebraMap L F (P.evalAt An.param) =
      algebraMap L F (-(P.evalAt An.param)) * V P := by
    intro P hP
    obtain ⟨-, -, -, hc0, -⟩ := An.mem_dom P (hNdom P hP)
    have hπ0 : algebraMap L F (An.modulus : L) ≠ 0 := (map_ne_zero _).mpr hmod0
    have hc0' : algebraMap L F (P.evalAt An.param) ≠ 0 := (map_ne_zero _).mpr hc0
    show An.param - algebraMap L F (P.evalAt An.param) = algebraMap L F (-(P.evalAt An.param)) *
      (1 - algebraMap L F ((An.modulus : L) * (P.evalAt An.param)⁻¹) * (algebraMap L F (An.modulus : L) * An.param⁻¹)⁻¹)
    rw [map_neg, map_mul, map_inv₀, mul_inv, inv_inv]
    field_simp
    ring
  obtain ⟨hVmem, hVres⟩ := prod_zpow_mem_and_res R.integers R.residue R.ker_residue N.support V
    (fun P => N P) 1 one_ne_zero hVfac
  refine ⟨∏ P ∈ N.support, V P ^ N P, hVmem, by rw [hVres, one_zpow], ?_⟩
  show (∏ P ∈ N.support, (An.param - algebraMap L F (P.evalAt An.param)) ^ N P) =
    algebraMap L F (∏ P ∈ N.support, (P.evalAt An.param) ^ N P) * ∏ P ∈ N.support, V P ^ N P
  rw [Finset.prod_congr rfl fun P hP => by rw [hsplit P hP, mul_zpow], Finset.prod_mul_distrib]
  congr 1
  rw [map_prod]
  simp_rw [map_zpow₀]
  have hneg : ∀ (a : F) (k : ℤ), (-a) ^ k = (-1) ^ k * a ^ k := fun a k => by
    rw [neg_eq_neg_one_mul, mul_zpow]
  rw [Finset.prod_congr rfl fun P _ => by rw [map_neg, hneg], Finset.prod_mul_distrib, prod_neg_one_zpow,
    show (∑ P ∈ N.support, N P) = N.sum (fun _ k => k) from rfl, hNsum, zpow_zero, one_mul]

end EndResidues

section EndValues

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fa : Type*} [Field Fa] [Algebra (ResidueField A) Fa]
variable {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem inv_mem_and_res_eq_one (R : RegularProlongation A F Fb) {W : F} (hW : W ∈ R.integers)
    (hW1 : R.residue ⟨W, hW⟩ = 1) : ∃ h : W⁻¹ ∈ R.integers, R.residue ⟨W⁻¹, h⟩ = 1 := by
  obtain ⟨uW, huW⟩ := RegularProlongation.isUnit_of_residue_ne_zero R (f := ⟨W, hW⟩)
    (by rw [hW1]; exact one_ne_zero)
  have hval : (((uW⁻¹ : R.integersˣ) : R.integers) : F) = W⁻¹ := by
    rw [coe_unit_inv, huW]
  refine ⟨by rw [← hval]; exact ((uW⁻¹ : R.integersˣ) : R.integers).2, ?_⟩
  have hinvres : R.residue ((uW⁻¹ : R.integersˣ) : R.integers) = (R.residue ((uW : R.integersˣ) : R.integers))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
  rw [show (⟨W⁻¹, by rw [← hval]; exact ((uW⁻¹ : R.integersˣ) : R.integers).2⟩ : R.integers) =
      ((uW⁻¹ : R.integersˣ) : R.integers) from Subtype.ext hval.symm, hinvres, huW, hW1, inv_one]

theorem end_values [IsAlgClosed L] [HasPrincipalDivisors L F]
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hparam : An'.param * An.param = algebraMap L F (An.modulus : L)) (hmod0 : (An.modulus : L) ≠ 0)
    (Ca : ComponentChart A F Fa) (xa : Place (ResidueField A) Fa) (hxa_rat : xa.IsRational)
    (hatt : An.IsAttached Ca xa)
    (Cb : ComponentChart A F Fb) (xb : Place (ResidueField A) Fb) (hxb_rat : xb.IsRational)
    (hatt' : An'.IsAttached Cb xb)
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param))
    {f : F} (N : Divisor L F) (hNdom : ∀ P ∈ N.support, P ∈ An.dom)
    (hN : ∀ P ∈ An.dom, N P = P.ord f) (hNsum : (N.sum fun _ k => k) = 0)
    {ca : L} (hca : ca • f ∈ Ca.integers) (hresa : Ca.residue ⟨ca • f, hca⟩ ≠ 0)
    {cb : L} (hcb : cb • f ∈ Cb.integers) (hresb : Cb.residue ⟨cb • f, hcb⟩ ≠ 0)
    (h0a : xa.ord (Ca.residue ⟨ca • f, hca⟩) = 0) :
    ∃ hu : ca * cb⁻¹ * (N.prod fun P k => (P.evalAt An.param) ^ k)⁻¹ ∈ A, IsUnit (⟨_, hu⟩ : A) ∧
      xa.evalAt (Ca.residue ⟨ca • f, hca⟩) =
        xb.evalAt (Cb.residue ⟨cb • f, hcb⟩) * IsLocalRing.residue A ⟨_, hu⟩ := by
  classical
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne12⟩ := hwide
  have hne : An.dom.Nonempty := ⟨Q₁, hQ₁⟩
  have hz0 : An.param ≠ 0 := param_ne_zero An hQ₁
  have hp' : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hz0).mpr hparam
  have hca0 : ca ≠ 0 := const_ne_zero Ca hca hresa
  have hcb0 : cb ≠ 0 := const_ne_zero Cb hcb hresb
  have hf0 : f ≠ 0 := fun_ne_zero Ca hca hresa
  obtain ⟨-, hza, hxa, hsla⟩ := hatt
  obtain ⟨-, Hb⟩ := hatt'
  obtain ⟨hzb, hxb, hslb⟩ := transfer_end Cb.residue xb hdom hp' Hb

  set u : L := N.prod fun P k => (P.evalAt An.param) ^ k with hu_def
  set W : F := N.prod fun P k => (An.param - algebraMap L F (P.evalAt An.param)) ^ k with hW_def
  have hu0 : u ≠ 0 := by
    rw [hu_def, Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun P hP => zpow_ne_zero _ (An.mem_dom P (hNdom P hP)).2.2.2.1
  have hW0 : W ≠ 0 := (ord_weierstrassProd An N hNdom hQ₁).1
  obtain ⟨hWa, hWa1⟩ := weierstrassProd_mem_and_res_eq_one_src An (rp Ca) xa hza hxa N hNdom hNsum
  obtain ⟨V, hVb, hVb1, hWV⟩ := weierstrassProd_eq_kummer_mul_tgt An hmod0 (rp Cb) xb hzb hxb N hNdom hNsum
  rw [← hW_def, ← hu_def] at hWV
  obtain ⟨hWinv, hWinv1⟩ := inv_mem_and_res_eq_one (rp Ca) hWa hWa1
  obtain ⟨hVinv, hVinv1⟩ := inv_mem_and_res_eq_one (rp Cb) hVb hVb1
  have hV0 : V ≠ 0 := by
    intro h0
    have : (rp Cb).residue ⟨V, hVb⟩ = 0 := by
      rw [show (⟨V, hVb⟩ : (rp Cb).integers) = 0 from Subtype.ext h0, map_zero]
    rw [hVb1] at this; exact one_ne_zero this

  set g : F := (ca • f) * W⁻¹ with hg_def
  have hg0 : g ≠ 0 := mul_ne_zero (smul_ne_zero hca0 hf0) (inv_ne_zero hW0)
  have hga : g ∈ Ca.integers := mul_mem hca hWinv
  have hres_ga : Ca.residue ⟨g, hga⟩ = Ca.residue ⟨ca • f, hca⟩ := by
    rw [show (⟨g, hga⟩ : Ca.integers) = ⟨ca • f, hca⟩ * ⟨W⁻¹, hWinv⟩ from rfl, map_mul]
    rw [show Ca.residue ⟨W⁻¹, hWinv⟩ = 1 from hWinv1, mul_one]
  have hresga : (rp Ca).residue ⟨g, hga⟩ ≠ 0 := by
    show Ca.residue ⟨g, hga⟩ ≠ 0
    rw [hres_ga]; exact hresa

  set c' : L := ca * cb⁻¹ * u⁻¹ with hc'_def
  have hc'0 : c' ≠ 0 := mul_ne_zero (mul_ne_zero hca0 (inv_ne_zero hcb0)) (inv_ne_zero hu0)
  have heq : (algebraMap L F c')⁻¹ * g = (cb • f) * V⁻¹ := by
    rw [hg_def, hWV, hc'_def, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_inv₀, map_inv₀]
    have h1 : algebraMap L F ca ≠ 0 := (map_ne_zero _).mpr hca0
    have h2 : algebraMap L F cb ≠ 0 := (map_ne_zero _).mpr hcb0
    have h3 : algebraMap L F u ≠ 0 := (map_ne_zero _).mpr hu0
    field_simp
  have hgb : (algebraMap L F c')⁻¹ * g ∈ Cb.integers := by rw [heq]; exact mul_mem hcb hVinv
  have hres_gb : Cb.residue ⟨_, hgb⟩ = Cb.residue ⟨cb • f, hcb⟩ := by
    rw [show (⟨_, hgb⟩ : Cb.integers) = ⟨cb • f, hcb⟩ * ⟨V⁻¹, hVinv⟩ from Subtype.ext heq, map_mul]
    rw [show Cb.residue ⟨V⁻¹, hVinv⟩ = 1 from hVinv1, mul_one]
  have hresgb : (rp Cb).residue ⟨_, hgb⟩ ≠ 0 := by
    show Cb.residue ⟨_, hgb⟩ ≠ 0
    rw [hres_gb]; exact hresb

  have hzero : ∀ P ∈ An.dom, P.ord g = 0 := by
    intro P hP
    rw [hg_def, P.ord_mul (smul_ne_zero hca0 hf0) (inv_ne_zero hW0), P.ord_inv,
      ord_smul P hca0 hf0, (ord_weierstrassProd An N hNdom hP).2, ← hN P hP, add_neg_cancel]

  have hfin : ∀ h : F, h ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord h ≠ 0}.Finite := by
    intro h hh
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) h hh
    refine (D.support.finite_toSet).subset fun P hP => ?_
    exact Finsupp.mem_support_iff.mpr (by rw [hD P]; exact hP.2)

  obtain ⟨-, hu', hunit', heval'⟩ :=
    AlgebraicCurve.Annulus.ord_residue_eq_neg_and_evalAt_residue_mul_zpow_eq_of_forall_ord_eq_zero_of_rankOne
      hrk An hmod0 hfin (rp Ca) xa hza hxa hsla (rp Cb) xb hzb hxb hslb hxa_rat hxb_rat hne
      g hg0 hga hresga c' hc'0 hgb hresgb hzero

  have hoa : xa.ord ((rp Ca).residue ⟨g, hga⟩) = 0 := by
    show xa.ord (Ca.residue ⟨g, hga⟩) = 0
    rw [hres_ga]; exact h0a
  have key : ∀ (o : ℤ), o = 0 → ∀ (hu'' : c' * (An.modulus : L) ^ (-o) ∈ A), IsUnit (⟨_, hu''⟩ : A) →
      xa.evalAt ((rp Ca).residue ⟨g, hga⟩ * (rp Ca).residue ⟨An.param, hza⟩ ^ (-o)) =
        xb.evalAt ((rp Cb).residue ⟨_, hgb⟩ *
          (rp Cb).residue ⟨algebraMap L F (An.modulus : L) * An.param⁻¹, hzb⟩ ^ o) *
          IsLocalRing.residue A ⟨_, hu''⟩ →
      ∃ hu : c' ∈ A, IsUnit (⟨_, hu⟩ : A) ∧
        xa.evalAt (Ca.residue ⟨ca • f, hca⟩) = xb.evalAt (Cb.residue ⟨cb • f, hcb⟩) * IsLocalRing.residue A ⟨_, hu⟩ := by
    intro o ho hu'' hunit'' heval''
    subst ho
    have hcA : c' ∈ A := by simpa using hu''
    have hsub : (⟨c' * (An.modulus : L) ^ (-(0 : ℤ)), hu''⟩ : A) = ⟨c', hcA⟩ := Subtype.ext (by simp)
    rw [hsub] at hunit'' heval''
    simp only [neg_zero, zpow_zero, mul_one] at heval''
    refine ⟨hcA, hunit'', ?_⟩
    have e1 : (rp Ca).residue ⟨g, hga⟩ = Ca.residue ⟨ca • f, hca⟩ := hres_ga
    have e2 : (rp Cb).residue ⟨_, hgb⟩ = Cb.residue ⟨cb • f, hcb⟩ := hres_gb
    rw [e1, e2] at heval''
    exact heval''
  exact key _ hoa hu' hunit' heval'

end EndValues

section UnitsPush

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem coe_prod_units_zpow {ι : Type*} (s : Finset ι) (U : ι → (↥A)ˣ) (k : ι → ℤ) :
    ((((∏ i ∈ s, U i ^ k i : (↥A)ˣ)) : A) : L) = ∏ i ∈ s, (((U i : (↥A)ˣ) : A) : L) ^ k i := by
  set ψ : (↥A)ˣ →* Lˣ := Units.map A.subtype.toMonoidHom with hψ
  have h1 : ∀ X : (↥A)ˣ, (((X : (↥A)ˣ) : A) : L) = ((ψ X : Lˣ) : L) := fun X => rfl
  rw [h1, map_prod]
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, ← h1]

theorem residue_coe_prod_units_zpow {ι : Type*} (s : Finset ι) (U : ι → (↥A)ˣ) (k : ι → ℤ) :
    IsLocalRing.residue A ((∏ i ∈ s, U i ^ k i : (↥A)ˣ) : A) =
      ∏ i ∈ s, (IsLocalRing.residue A ((U i : (↥A)ˣ) : A)) ^ k i := by
  set ψ : (↥A)ˣ →* (ResidueField A)ˣ := Units.map (IsLocalRing.residue A).toMonoidHom with hψ
  have h1 : ∀ X : (↥A)ˣ, IsLocalRing.residue A ((X : (↥A)ˣ) : A) = ((ψ X : (ResidueField A)ˣ) : ResidueField A) :=
    fun X => rfl
  rw [h1, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, ← h1]

end UnitsPush

end CycleLawEngine

open CycleLawEngine in

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
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
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (f : F) (hf : f ≠ 0)
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hDi : ∀ i, ∀ P ∈ (C i).dom, Di i P = P.ord f)
    (hD0 : ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0)
    (N : Fin m → Divisor L F) (hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom)
    (hN : ∀ e, ∀ P ∈ (An e).dom, N e P = P.ord f)
    (hNsum : ∀ e, ((N e).sum fun _ k => k) = 0)
    (hNprod : ∀ e, ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) = 1)
    :
    ∀ ε : Fin m → ℤ,
      (∀ i : Fin n, (∑ e, if src e = i then ε e else 0) = (∑ e, if tgt e = i then ε e else 0)) →
      ∃ h : (∏ e, ((N e).prod fun P k => (P.evalAt (An e).param) ^ k) ^ (ε e)) ∈ A,
        IsLocalRing.residue A ⟨(∏ e, ((N e).prod fun P k => (P.evalAt (An e).param) ^ k) ^ (ε e)), h⟩ = 1 := by
  classical

  choose c hc hres using fun i => (C i).exists_smul_mem f hf

  have hDoff : ∀ i P, P ∉ (C i).dom → Di i P = 0 := fun i P hP => by
    by_contra h
    exact hP (hdom i P (Finsupp.mem_support_iff.mpr h))
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
  have hmass : ∀ i, ((Di i).sum fun _ k => k) = 0 := fun i => by
    rw [← sum_mapDomain (C i) (Di i), hD0 i, Finsupp.sum_zero_index]

  set g : ∀ i, Fbar i := fun i => (C i).residue ⟨c i • f, hc i⟩ with hg
  set s : Fin m → ℤ := fun e => (xt e).ord (g (tgt e)) with hs

  have hedge : ∀ e, (xs e).ord (g (src e)) + s e = 0 ∧
      A.valuation (c (src e)) * (A.valuation (c (tgt e)))⁻¹ *
        A.valuation ((An e).modulus : L) ^ (s e) = 1 := fun e =>
    end_orders (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e) (C (src e)) (xs e) (hatt e).1
      (C (tgt e)) (xt e) (hatt e).2 (wide_of_isAlgClosed (An e) (hmod0 e)) (N e) (hNdom e) (hN e)
      (hNsum e) (hNprod e) (hc (src e)) (hres (src e)) (hc (tgt e)) (hres (tgt e))

  have hvert : ∀ i, ∑ x ∈ (C i).nodes, x.ord (g i) = 0 := fun i =>
    sum_nodes_ord_eq_zero (hratBar i) (C i) (hc i) (hres i) (Di i) (hDi i) (hDoff i) (hmass i)

  have hnodesum : ∀ (φ : ∀ j, Place (IsLocalRing.ResidueField A) (Fbar j) → ℤ) (i : Fin n),
      ∑ x ∈ (C i).nodes, φ i x =
        (∑ e ∈ Finset.univ.filter (fun e => tgt e = i), φ (tgt e) (xt e)) +
          ∑ e ∈ Finset.univ.filter (fun e => src e = i), φ (src e) (xs e) :=
    sum_nodes_eq_sum_ends (fun i => (C i).nodes) src tgt xs xt (fun e => (hatt e).1.1)
      (fun e => (hatt e).2.1) hnodes.1 hnodes.2

  have hc0 : ∀ i, c i ≠ 0 := fun i => const_ne_zero (C i) (hc i) (hres i)
  have hvc : ∀ i, A.valuation (c i) ≠ 0 := fun i => (Valuation.ne_zero_iff _).mpr (hc0 i)
  have hπL : (π : L) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hvπ0 : A.valuation (π : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hπL
  have hvπ1 : A.valuation (π : L) < 1 := (A.valuation_lt_one_iff π).mp hπ
  have hslope : ∀ e, s e = 0 := by
    let hgt : Fin n → Additive (A.ValueGroup)ˣ :=
      fun i => Additive.ofMul (Units.mk0 (A.valuation (c i)) (hvc i))
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
      have key : A.valuation (c (tgt e)) * (A.valuation (c (src e)))⁻¹ =
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

  have hoa0 : ∀ e, (xs e).ord (g (src e)) = 0 := fun e => by
    have := (hedge e).1
    rw [hslope e, add_zero] at this
    exact this
  have hord0 : ∀ (i : Fin n) (x : Place (IsLocalRing.ResidueField A) (Fbar i)), x.ord (g i) = 0 := by
    intro i x
    by_cases hx : x ∈ (C i).nodes
    · exact hnode0 i x hx
    · have := mapDomain_eq_ord_of_not_mem_nodes (C i) (hc i) (hres i) (Di i) (hDi i) (hDoff i) x hx
      rw [hD0 i, Finsupp.coe_zero, Pi.zero_apply] at this
      exact this.symm
  haveI hκ : IsAlgClosed (IsLocalRing.ResidueField A) :=
    ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  have hγex : ∀ (i : Fin n) (x : Place (IsLocalRing.ResidueField A) (Fbar i)),
      ∃ γ : IsLocalRing.ResidueField A, g i = algebraMap _ _ γ := fun i x =>
    exists_eq_algebraMap_of_forall_ord_eq_zero x (hord0 i)
  let γ : Fin n → IsLocalRing.ResidueField A := fun i =>
    if h : Nonempty (Place (IsLocalRing.ResidueField A) (Fbar i)) then
      Classical.choose (hγex i (Classical.choice h)) else 1
  have hγ : ∀ (i : Fin n) (x : Place (IsLocalRing.ResidueField A) (Fbar i)), g i = algebraMap _ _ (γ i) := by
    intro i x
    have hne : Nonempty (Place (IsLocalRing.ResidueField A) (Fbar i)) := ⟨x⟩
    show g i = algebraMap _ _ (if h : Nonempty (Place (IsLocalRing.ResidueField A) (Fbar i)) then
      Classical.choose (hγex i (Classical.choice h)) else 1)
    rw [dif_pos hne]
    exact Classical.choose_spec (hγex i (Classical.choice hne))
  have hγ0 : ∀ i, γ i ≠ 0 := by
    intro i
    by_cases hne : Nonempty (Place (IsLocalRing.ResidueField A) (Fbar i))
    · intro h
      obtain ⟨x⟩ := hne
      exact hres i (by show g i = 0; rw [hγ i x, h, map_zero])
    · show (if h : Nonempty (Place (IsLocalRing.ResidueField A) (Fbar i)) then
        Classical.choose (hγex i (Classical.choice h)) else (1 : IsLocalRing.ResidueField A)) ≠ 0
      rw [dif_neg hne]; exact one_ne_zero

  set u : Fin m → L := fun e => (N e).prod fun P k => (P.evalAt (An e).param) ^ k with hu_def
  have hang : ∀ e, ∃ hr : c (src e) * (c (tgt e))⁻¹ * (u e)⁻¹ ∈ A, IsUnit (⟨_, hr⟩ : A) ∧
      γ (src e) = γ (tgt e) * IsLocalRing.residue A ⟨_, hr⟩ := by
    intro e
    obtain ⟨hr, hunit, heq⟩ := end_values hrk (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e)
      (C (src e)) (xs e) (hratBar _ _) (hatt e).1 (C (tgt e)) (xt e) (hratBar _ _) (hatt e).2
      (wide_of_isAlgClosed (An e) (hmod0 e)) (N e) (hNdom e) (hN e) (hNsum e)
      (hc (src e)) (hres (src e)) (hc (tgt e)) (hres (tgt e)) (hoa0 e)
    refine ⟨hr, hunit, ?_⟩
    have e1 : (C (src e)).residue ⟨c (src e) • f, hc (src e)⟩ = algebraMap _ _ (γ (src e)) := hγ (src e) (xs e)
    have e2 : (C (tgt e)).residue ⟨c (tgt e) • f, hc (tgt e)⟩ = algebraMap _ _ (γ (tgt e)) := hγ (tgt e) (xt e)
    rw [e1, e2, Place.evalAt_algebraMap_eq, Place.evalAt_algebraMap_eq] at heq
    exact heq
  choose hrA hrU hrγ using hang

  have huU : ∀ e, ∃ hu : u e ∈ A, IsUnit (⟨u e, hu⟩ : A) := by
    intro e
    have hv : A.valuation (u e) = 1 := by
      rw [hu_def]
      show A.valuation ((N e).prod fun P k => (P.evalAt (An e).param) ^ k) = 1
      rw [Finsupp.prod, map_prod]
      simp_rw [map_zpow₀]
      exact hNprod e
    have hmem : u e ∈ A := (A.valuation_le_one_iff _).mp hv.le
    refine ⟨hmem, ?_⟩
    rw [ValuationSubring.valuation_eq_one_iff]
    exact hv
  choose huA huU' using huU

  intro ε hε
  set Ur : Fin m → (↥A)ˣ := fun e => (hrU e).unit with hUr
  set Uu : Fin m → (↥A)ˣ := fun e => (huU' e).unit with hUu
  have hUr_val : ∀ e, (((Ur e : (↥A)ˣ) : A) : L) = c (src e) * (c (tgt e))⁻¹ * (u e)⁻¹ := fun e => by
    rw [hUr, IsUnit.unit_spec]
  have hUu_val : ∀ e, (((Uu e : (↥A)ˣ) : A) : L) = u e := fun e => by
    rw [hUu, IsUnit.unit_spec]
  have hr0 : ∀ e, c (src e) * (c (tgt e))⁻¹ * (u e)⁻¹ ≠ 0 := fun e => by
    rw [← hUr_val e]
    exact fun h => (Ur e).ne_zero (Subtype.ext h)
  have hu0 : ∀ e, u e ≠ 0 := fun e h => by
    have := hr0 e; rw [h, inv_zero, mul_zero] at this; exact this rfl

  have hpot : ∏ e, (c (src e) * (c (tgt e))⁻¹) ^ ε e = 1 := by
    have := prod_div_zpow_eq_one_of_flow src tgt (fun i => Units.mk0 (c i) (hc0 i)) ε hε
    have h2 := congrArg (fun x : Lˣ => (x : L)) this
    simp only [Units.coe_prod, Units.val_one, Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val,
      Units.val_mk0] at h2
    simpa [div_eq_mul_inv] using h2

  have hsplit : ∏ e, (u e) ^ ε e = ∏ e, (c (src e) * (c (tgt e))⁻¹ * (u e)⁻¹) ^ (-ε e) := by
    have hpt : ∀ e, (c (src e) * (c (tgt e))⁻¹ * (u e)⁻¹) ^ (-ε e) =
        ((c (src e) * (c (tgt e))⁻¹) ^ ε e)⁻¹ * (u e) ^ ε e := by
      intro e
      rw [zpow_neg, ← inv_zpow, mul_inv, inv_inv, mul_zpow, inv_zpow]
    rw [Finset.prod_congr rfl fun e _ => hpt e, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hpot,
      inv_one, one_mul]
  have hX : ∏ e, (c (src e) * (c (tgt e))⁻¹ * (u e)⁻¹) ^ (-ε e) =
      (((∏ e, Ur e ^ (-ε e) : (↥A)ˣ)) : A) := by
    rw [coe_prod_units_zpow]
    exact Finset.prod_congr rfl fun e _ => by rw [hUr_val]
  have hmem : (∏ e, (u e) ^ ε e) ∈ A := by
    rw [hsplit, hX]; exact ((∏ e, Ur e ^ (-ε e) : (↥A)ˣ) : A).2
  refine ⟨hmem, ?_⟩
  rw [show (⟨∏ e, (u e) ^ ε e, hmem⟩ : A) = ((∏ e, Ur e ^ (-ε e) : (↥A)ˣ) : A) from
    Subtype.ext (by rw [← hX, ← hsplit])]
  rw [residue_coe_prod_units_zpow]

  have hρ : ∀ e, IsLocalRing.residue A ((Ur e : (↥A)ˣ) : A) = γ (src e) / γ (tgt e) := by
    intro e
    rw [eq_div_iff (hγ0 _), mul_comm]
    rw [show ((Ur e : (↥A)ˣ) : A) = ⟨_, hrA e⟩ from by rw [hUr]; rfl]
    exact (hrγ e).symm
  simp_rw [hρ]
  have hε' : ∀ i : Fin n, (∑ e, if src e = i then -ε e else 0) = (∑ e, if tgt e = i then -ε e else 0) := by
    intro i
    have hneg : ∀ v : Fin m → Fin n, (∑ e, if v e = i then -ε e else 0) = -(∑ e, if v e = i then ε e else 0) := by
      intro v
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
    rw [hneg src, hneg tgt, hε i]
  have := prod_div_zpow_eq_one_of_flow src tgt (fun i => Units.mk0 (γ i) (hγ0 i)) (fun e => -ε e) hε'
  have h2 := congrArg (fun x : (IsLocalRing.ResidueField A)ˣ => (x : IsLocalRing.ResidueField A)) this
  simp only [Units.coe_prod, Units.val_one, Units.val_zpow_eq_zpow_val, Units.val_div_eq_div_val,
    Units.val_mk0] at h2
  exact h2

end S_AlgebraicCurve_exists_residue_prod_zpow_eq_one_of_forall_mapDomain_placeMap_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one_of_semistableCovering_of_discFibres_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_exists_residue_prod_zpow_eq_one_of_forall_mapDomain_placeMap_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one_of_semistableCovering_of_discFibres_of_rankOne (solution)
