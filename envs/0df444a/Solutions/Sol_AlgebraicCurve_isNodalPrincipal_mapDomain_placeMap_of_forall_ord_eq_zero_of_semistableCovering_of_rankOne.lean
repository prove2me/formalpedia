-- Prove2me | solution 1 for AlgebraicCurve.isNodalPrincipal_mapDomain_placeMap_of_forall_ord_eq_zero_of_semistableCovering_of_rankOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a59f43e4-4822-5fde-9ef1-906597b97768

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
import Definitions.Def_AlgebraicCurve_NodalPic0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isNodalPrincipal_mapDomain_placeMap_of_forall_ord_eq_zero_of_semistableCovering_of_rankOne
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

theorem RW.exists_rescaling
    {L : Type*} [Field L] (A : ValuationSubring L)
    (n m : ℕ) (src tgt : Fin m → Fin n)
    (κc : Fin n → L) (hc0 : ∀ i, κc i ≠ 0)
    (hveq : ∀ e, A.valuation (κc (src e)) = A.valuation (κc (tgt e))) :
    ∃ β : Fin n → IsLocalRing.ResidueField A, (∀ i, β i ≠ 0) ∧
      ∀ e, ∃ hW : κc (tgt e) * (κc (src e))⁻¹ ∈ A, β (tgt e) = IsLocalRing.residue A ⟨_, hW⟩ * β (src e) := by
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
  have hvr : ∀ e, A.valuation (κc (tgt e) * (κc (src e))⁻¹) = 1 := by
    intro e; rw [map_mul, map_inv₀, ← hveq e, mul_inv_cancel₀ (hvc _)]
  refine ⟨fun i => IsLocalRing.residue A ⟨κc i * (κc (jof i))⁻¹, memA _ (hvβ i)⟩, fun i => resne _ (hvβ i),
    fun e => ⟨memA _ (hvr e), ?_⟩⟩
  show IsLocalRing.residue A ⟨κc (tgt e) * (κc (jof (tgt e)))⁻¹, _⟩ =
    IsLocalRing.residue A ⟨κc (tgt e) * (κc (src e))⁻¹, _⟩ * IsLocalRing.residue A ⟨κc (src e) * (κc (jof (src e)))⁻¹, _⟩
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  push_cast
  rw [hjof_eq e]
  field_simp [hc0 (src e)]

open ChartPrincipalMomentEngine in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField A) (Fbar i)]
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
    (f : F) (hf : f ≠ 0)
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hDi : ∀ i, ∀ P ∈ (C i).dom, Di i P = P.ord f)
    (hdeg : ∀ i, Divisor.degree (Di i) = 0)
    (hN0 : ∀ e, ∀ P ∈ (An e).dom, P.ord f = 0) :
    NodalData.IsNodalPrincipal (K := IsLocalRing.ResidueField A) (Fbar := Fbar) src tgt xs xt
      (fun i => Finsupp.mapDomain (C i).placeMap (Di i)) := by
  classical

  choose κc hκc hres using fun i => (C i).exists_smul_mem f hf
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
    rw [← degree_eq_sum_of_isRational (Di i) (fun P hP => hratF i P (hdom i P hP))]
    exact hdeg i

  set N : Fin m → Divisor L F := fun _ => 0 with hNdef
  have hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom := by
    intro e P hP; simp [hNdef] at hP
  have hN : ∀ e, ∀ P ∈ (An e).dom, N e P = P.ord f := by
    intro e P hP; rw [hN0 e P hP]; rfl
  have hNsum : ∀ e, ((N e).sum fun _ k => k) = 0 := fun e => Finsupp.sum_zero_index
  have hNprod : ∀ e, ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) = 1 :=
    fun e => Finsupp.prod_zero_index

  set g : ∀ i, Fbar i := fun i => (C i).residue ⟨κc i • f, hκc i⟩ with hg
  set s : Fin m → ℤ := fun e => (xt e).ord (g (tgt e)) with hs

  have hedge : ∀ e, (xs e).ord (g (src e)) + s e = 0 ∧
      A.valuation (κc (src e)) * (A.valuation (κc (tgt e)))⁻¹ *
        A.valuation ((An e).modulus : L) ^ (s e) = 1 := fun e =>
    end_orders (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e) (C (src e)) (xs e) (hatt e).1
      (C (tgt e)) (xt e) (hatt e).2 (wide_of_isAlgClosed (An e) (hmod0 e)) (N e) (hNdom e) (hN e)
      (hNsum e) (hNprod e) (hκc (src e)) (hres (src e)) (hκc (tgt e)) (hres (tgt e))

  have hvert : ∀ i, ∑ x ∈ (C i).nodes, x.ord (g i) = 0 := fun i =>
    sum_nodes_ord_eq_zero (hratBar i) (C i) (hκc i) (hres i) (Di i) (hDi i) (hDoff i) (hmass i)

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

  have hdivg : ∀ i (x : Place (ResidueField A) (Fbar i)), Finsupp.mapDomain (C i).placeMap (Di i) x = x.ord (g i) := by
    intro i x
    by_cases hx : x ∈ (C i).nodes
    · rw [hnode0 i x hx, mapDomain_eq_zero_of_mem_nodes (C i) (Di i) (hDoff i) x hx]
    · exact mapDomain_eq_ord_of_not_mem_nodes (C i) (hκc i) (hres i) (Di i) (hDi i) (hDoff i) x hx

  have hveq : ∀ e, A.valuation (κc (src e)) = A.valuation (κc (tgt e)) := by
    intro e
    obtain ⟨-, hprod⟩ := hedge e
    rw [hslope e, zpow_zero, mul_one] at hprod
    have := eq_inv_of_mul_eq_one_left hprod
    rw [inv_inv] at this
    exact this
  have hval : ∀ e, ∃ hW : κc (tgt e) * (κc (src e))⁻¹ ∈ A,
      IsLocalRing.residue A ⟨_, hW⟩ * (xs e).evalAt (g (src e)) = (xt e).evalAt (g (tgt e)) := by
    intro e
    have hzpar : (An e).param ≠ 0 := by
      obtain ⟨P, hP⟩ : (An e).dom.Nonempty := by
        obtain ⟨P, hP, -⟩ := wide_of_isAlgClosed (An e) (hmod0 e); exact ⟨P, hP⟩
      exact param_ne_zero (An e) hP
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
    have hordh : ∀ P ∈ (An e).dom, (0 : Divisor L F) P = P.ord (κc (src e) • f) := fun P hP => by
      rw [ord_smul P hca0 hf, hN0 e P hP]; rfl
    obtain ⟨hu, -, hlam⟩ :=
      AlgebraicCurve.Annulus.exists_isUnit_residue_mul_evalAt_eq_evalAt_of_isAttached_of_isAttached A hrk
        (hratBar (src e)) (hratBar (tgt e)) (An e) (An' e) (hpair e).1 (hpair e).2.2.2 (hmod0 e)
        (C (src e)) (xs e) (hatt e).1 (C (tgt e)) (xt e) (hatt e).2
        (κc (src e) • f) hh0 (hκc (src e)) (hres (src e)) c' hc'0 hhb hresb' 0 (by simp) hordh
    have hσa : (xs e).ord ((C (src e)).residue ⟨κc (src e) • f, hκc (src e)⟩) = 0 := hnode0 (src e) (xs e) (hatt e).1.1
    have hσb : (xt e).ord ((C (tgt e)).residue ⟨(algebraMap L F c')⁻¹ * (κc (src e) • f), hhb⟩) = 0 := by
      rw [hsub]; exact hnode0 (tgt e) (xt e) (hatt e).2.1
    have hlama : (xs e).evalAt ((C (src e)).residue ⟨κc (src e) • f, hκc (src e)⟩ *
        ((C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩) ^ (-((xs e).ord ((C (src e)).residue ⟨κc (src e) • f, hκc (src e)⟩)))) =
        (xs e).evalAt (g (src e)) := by
      rw [hσa, neg_zero, zpow_zero, mul_one]
    have hlamb : (xt e).evalAt ((C (tgt e)).residue ⟨(algebraMap L F c')⁻¹ * (κc (src e) • f), hhb⟩ *
        ((C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩) ^ (-((xt e).ord ((C (tgt e)).residue ⟨(algebraMap L F c')⁻¹ * (κc (src e) • f), hhb⟩)))) =
        (xt e).evalAt (g (tgt e)) := by
      rw [hσb, neg_zero, zpow_zero, mul_one, hsub]
    rw [hlama, hlamb] at hlam
    have hval' : c'⁻¹ * ((An e).modulus : L) ^ ((xs e).ord ((C (src e)).residue ⟨κc (src e) • f, hκc (src e)⟩) - ((0 : Divisor L F).sum fun _ k => k)) *
        ((0 : Divisor L F).prod fun P k => (-(P.evalAt (An e).param)) ^ k) = κc (tgt e) * (κc (src e))⁻¹ := by
      rw [hσa, Finsupp.sum_zero_index, Finsupp.prod_zero_index, sub_self, zpow_zero, mul_one, mul_one, hc', mul_inv, inv_inv,
        mul_comm]
    refine ⟨hval' ▸ hu, ?_⟩
    have : (⟨_, hval' ▸ hu⟩ : A) = ⟨_, hu⟩ := Subtype.ext hval'.symm
    rw [this]; exact hlam

  obtain ⟨β, hβ0, hβ⟩ := RW.exists_rescaling A n m src tgt κc hc0 hveq
  let gg : ∀ i, Fbar i := fun i => algebraMap (ResidueField A) (Fbar i) (β i)⁻¹ * g i
  have hgg0 : ∀ i, gg i ≠ 0 := fun i =>
    mul_ne_zero ((map_ne_zero _).mpr (inv_ne_zero (hβ0 i))) (hres i)
  have hordgg : ∀ i (x : Place (ResidueField A) (Fbar i)), x.ord (gg i) = x.ord (g i) := by
    intro i x
    rw [show gg i = algebraMap (ResidueField A) (Fbar i) (β i)⁻¹ * g i from rfl,
      x.ord_mul ((map_ne_zero _).mpr (inv_ne_zero (hβ0 i))) (hres i),
      ord_algebraMap x (inv_ne_zero (hβ0 i)), zero_add]

  have hnode_ord0 : ∀ e, (xs e).ord (g (src e)) = 0 ∧ (xt e).ord (g (tgt e)) = 0 :=
    fun e => ⟨hnode0 _ _ (hatt e).1.1, hnode0 _ _ (hatt e).2.1⟩
  have hvalue : ∀ (i : Fin n) (x : Place (ResidueField A) (Fbar i)), x.ord (g i) = 0 →
      x.HasValue (gg i) ((β i)⁻¹ * x.evalAt (g i)) := by
    intro i x hx0
    have hg0 : g i ≠ 0 := hres i
    have hgmem : g i ∈ x.toValuationSubring := Place.mem_toValuationSubring_of_ord_nonneg_alt x hg0 (by rw [hx0])
    have hcmem : algebraMap (ResidueField A) (Fbar i) (β i)⁻¹ ∈ x.toValuationSubring := x.algebraMap_mem' _
    refine ⟨mul_mem hcmem hgmem, ?_⟩
    rw [show (⟨gg i, mul_mem hcmem hgmem⟩ : x.toValuationSubring) = ⟨_, hcmem⟩ * ⟨g i, hgmem⟩ from rfl, map_mul, map_mul,
      ← x.algebraMap_evalAt (hratBar i x) hgmem, ← x.algebraMap_evalAt (hratBar i x) hcmem, Place.evalAt_algebraMap_eq]
  refine ⟨gg, fun e => Units.mk0 ((β (src e))⁻¹ * (xs e).evalAt (g (src e)))
      (mul_ne_zero (inv_ne_zero (hβ0 _)) (Place.evalAt_ne_zero_of_ord_eq_zero (xs e) (hratBar _ _)
        (hres (src e)) (hnode_ord0 e).1)),
    hgg0, fun i x => by rw [hordgg, hdivg], fun e => ⟨?_, ?_⟩⟩
  · simpa only [Units.val_mk0] using hvalue (src e) (xs e) (hnode_ord0 e).1
  · have h2 := hvalue (tgt e) (xt e) (hnode_ord0 e).2
    obtain ⟨hW, hβe⟩ := hβ e
    obtain ⟨hW', hve⟩ := hval e
    have hρ : IsLocalRing.residue A ⟨_, hW⟩ = IsLocalRing.residue A ⟨_, hW'⟩ := rfl
    have hρ0 : IsLocalRing.residue A ⟨_, hW'⟩ ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hve
      exact (Place.evalAt_ne_zero_of_ord_eq_zero (xt e) (hratBar _ _) (hres (tgt e)) (hnode_ord0 e).2) hve.symm
    have key : (β (tgt e))⁻¹ * (xt e).evalAt (g (tgt e)) = (β (src e))⁻¹ * (xs e).evalAt (g (src e)) := by
      rw [← hve, hβe, hρ, mul_inv, mul_comm ((IsLocalRing.residue A ⟨_, hW'⟩)⁻¹) ((β (src e))⁻¹), mul_assoc,
        inv_mul_cancel_left₀ hρ0]
    simpa only [Units.val_mk0, key] using h2

end S_AlgebraicCurve_isNodalPrincipal_mapDomain_placeMap_of_forall_ord_eq_zero_of_semistableCovering_of_rankOne
end P2MW
export P2MW.S_AlgebraicCurve_isNodalPrincipal_mapDomain_placeMap_of_forall_ord_eq_zero_of_semistableCovering_of_rankOne (solution)
