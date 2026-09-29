-- Prove2me | solution 1 for AlgebraicCurve.add_le_finrank_span_tmul_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3b232fef-299c-5f4c-8dfc-c094fd914002

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

import Theorems.Thm_AlgebraicCurve_exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
import Theorems.Thm_TateModule_add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_add_le_finrank_span_tmul_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

namespace VCI

open IsLocalRing

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

theorem exists_place_sq_eq_modulus [IsAlgClosed L] (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q : Place L F, Q ∈ An.dom ∧ (Q.evalAt An.param) ^ 2 = (An.modulus : L) := by
  set μ : A := An.modulus with hμ
  have hμm : μ ∈ maximalIdeal A := An.modulus_mem
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (μ : L) (n := 2) two_pos
  have hrA : r ∈ A := mem_of_pow_mem two_pos (hr ▸ μ.2)
  have hr' : (⟨r, hrA⟩ : A) ^ 2 = μ := Subtype.ext (by simpa using hr)
  have hrm : (⟨r, hrA⟩ : A) ∈ maximalIdeal A := mem_maximalIdeal_of_pow hμm hr'
  have hr0 : r ≠ 0 := by rintro rfl; apply hmod0; rw [← hr]; simp
  obtain ⟨Q, ⟨hQ, hQz⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r, hrA⟩ hrm hr0
    ⟨⟨r, hrA⟩, hrm, by rw [← hμ, ← hr]; simp [pow_two]⟩
  exact ⟨Q, hQ, by rw [hQz, ← hr]⟩

theorem exists_place_evalAt_eq_of_valuation_eq (An : Annulus A F) (P : Place L F) (hP : P ∈ An.dom)
    (c : A) (hv : A.valuation (c : L) = A.valuation (P.evalAt An.param)) :
    ∃ Q : Place L F, Q ∈ An.dom ∧ Q.evalAt An.param = c := by
  obtain ⟨-, -, ⟨hA, hmax⟩, hne, m0, hm0, hmod⟩ := An.mem_dom P hP
  have hc0 : (c : L) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact hne ((map_eq_zero A.valuation).mp hv.symm)
  have hle1 : A.valuation ((c : L) * (P.evalAt An.param)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, hv, mul_inv_cancel₀ ((map_ne_zero A.valuation).mpr hne)]
  have hle2 : A.valuation ((P.evalAt An.param) * (c : L)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀, ← hv, mul_inv_cancel₀ ((map_ne_zero A.valuation).mpr hc0)]
  have hu1 : (c : L) * (P.evalAt An.param)⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hle1
  have hu2 : (P.evalAt An.param) * (c : L)⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hle2
  have hcmem : c ∈ maximalIdeal A := by
    have : (c : A) = ⟨P.evalAt An.param, hA⟩ * ⟨(c : L) * (P.evalAt An.param)⁻¹, hu1⟩ := by
      apply Subtype.ext
      show (c : L) = P.evalAt An.param * ((c : L) * (P.evalAt An.param)⁻¹)
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hmax
  have hcdiv : ∃ m ∈ maximalIdeal A, (An.modulus : L) = c * m := by
    refine ⟨⟨(P.evalAt An.param) * (c : L)⁻¹, hu2⟩ * m0, Ideal.mul_mem_left _ _ hm0, ?_⟩
    rw [hmod]
    push_cast
    calc P.evalAt An.param * (m0 : L)
        = P.evalAt An.param * ((c : L) * (c : L)⁻¹) * (m0 : L) := by rw [mul_inv_cancel₀ hc0, mul_one]
      _ = (c : L) * (P.evalAt An.param * (c : L)⁻¹ * (m0 : L)) := by ring
  obtain ⟨Q, ⟨hQ, hQz⟩, -⟩ := An.existsUnique_evalAt_eq c hcmem hc0 hcdiv
  exact ⟨Q, hQ, hQz⟩

theorem residue_ne_one_of_pow_eq_one {ℓ : ℕ} (hℓ : IsUnit ((ℓ : ℕ) : ResidueField A))
    (x : A) (hx : x ^ ℓ = 1) (hx1 : x ≠ 1) : residue A x ≠ 1 := by
  intro h
  have ht : x - 1 ∈ maximalIdeal A := by
    rw [← Ideal.Quotient.eq]
    have h__ := h
    try simp at h__
    try simp
    exact h__
  have hgeom : (∑ i ∈ Finset.range ℓ, x ^ i) * (x - 1) = 0 := by
    rw [geom_sum_mul, hx, sub_self]
  have hS : (∑ i ∈ Finset.range ℓ, x ^ i) = 0 := by
    rcases mul_eq_zero.mp hgeom with h1 | h1
    · exact h1
    · exact absurd (sub_eq_zero.mp h1) hx1
  have hres : residue A (∑ i ∈ Finset.range ℓ, x ^ i) = (ℓ : ResidueField A) := by
    rw [map_sum]
    simp [map_pow, h]
  rw [hS, map_zero] at hres
  exact hℓ.ne_zero hres.symm

theorem degree_eq_sum [IsAlgClosed L] [IsCurveOver L F] (D : Divisor L F) :
    Divisor.degree D = D.sum fun _ k => k := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [IsCurveOver.deg_eq_one_of_isAlgClosed v]

end VCI

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
    (x : Fin m → TateModule ℓ (Pic0 L F))
    (hx : ∀ e : Fin m,
      ∀ (k : ℕ) (Q Q' : Place L F), Q ∈ (An e).dom → Q' ∈ (An e).dom →
        (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ (Q.evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d) →
        Q'.evalAt (An e).param = ξ k * Q.evalAt (An e).param →
        ∃ (Di : Fin n → Divisor L F) (r : ℕ) (eq : Fin r → Fin m) (nq : Fin r → ℤ) (Qq : Fin r → Fin 4 → Place L F),
          (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) ∧
          (∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0) ∧
          (∀ j l, Qq j l ∈ (An (eq j)).dom) ∧
          (∀ j, (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 0).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d) ∧
            (∃ (N d : ℕ) (u : Aˣ), 0 < N ∧ ((Qq j 1).evalAt (An (eq j)).param) ^ N = ((u : A) : L) * (π : L) ^ d)) ∧
          (∀ j, ∃ u : Aˣ,
            (Qq j 0).evalAt (An (eq j)).param = ((u : A) : L) * (Qq j 2).evalAt (An (eq j)).param) ∧
          (∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
            (Qq j 0).evalAt (An (eq j)).param * (Qq j 1).evalAt (An (eq j)).param =
              (Qq j 2).evalAt (An (eq j)).param * (Qq j 3).evalAt (An (eq j)).param * (1 + ((t : A) : L))) ∧
          ∀ hD : (Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1) : Divisor L F) ∈
              Divisor.degZero (K := L) (F := F),
            TateModule.proj ℓ (Pic0 L F) k (x e) = Pic0.mk ⟨Finsupp.single Q 1 - Finsupp.single Q' 1 - ∑ i, Di i
              - ∑ j, nq j • (Finsupp.single (Qq j 0) 1 + Finsupp.single (Qq j 1) 1
                  - Finsupp.single (Qq j 2) 1 - Finsupp.single (Qq j 3) 1), hD⟩)
    :
    m + 1 ≤ Module.finrank ℚ_[ℓ] ↥(Submodule.span ℚ_[ℓ]
      (Set.range fun e : Fin m => ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x e : ModularCurve.RationalTateModule ℓ (Pic0 L F)))) + n := by
  classical

  have hn : 0 < n := by
    obtain ⟨t, ht, hfin, hsep⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := L) (F := F)
    haveI := hsep
    obtain ⟨P⟩ := AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional L t ht hfin
    rcases hcover P with ⟨i, -⟩ | ⟨e, -⟩
    · exact i.pos
    · exact (src e).pos

  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  have hξpow : ∀ k, ξ k ^ (ℓ ^ k) = 1 := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_one, hξ0]
    | succ j ih => rw [pow_succ', pow_mul, hξ j, ih]
  have hξA : ∀ k, ξ k ∈ A := by
    intro k
    refine VCI.mem_of_pow_mem (pow_pos hℓpos k) ?_
    rw [hξpow k]; exact one_mem A
  let ζ : ℕ → IsLocalRing.ResidueField A := fun k => IsLocalRing.residue A ⟨ξ k, hξA k⟩
  have hζ0 : ζ 0 = 1 := by
    show IsLocalRing.residue A ⟨ξ 0, hξA 0⟩ = 1
    have : (⟨ξ 0, hξA 0⟩ : A) = 1 := Subtype.ext hξ0
    rw [this, map_one]
  have hζ : ∀ k, ζ (k + 1) ^ ℓ = ζ k := by
    intro k
    show (IsLocalRing.residue A ⟨ξ (k + 1), hξA (k + 1)⟩) ^ ℓ = IsLocalRing.residue A ⟨ξ k, hξA k⟩
    rw [← map_pow]
    congr 1
    exact Subtype.ext (by push_cast; exact hξ k)
  have hζ1 : ζ 1 ≠ 1 := by
    show IsLocalRing.residue A ⟨ξ 1, hξA 1⟩ ≠ 1
    refine VCI.residue_ne_one_of_pow_eq_one hℓ ⟨ξ 1, hξA 1⟩ (Subtype.ext ?_) (fun h => hξ1 ?_)
    · push_cast; have := hξpow 1; rwa [pow_one] at this
    · exact congrArg Subtype.val h

  have hmod0 : ∀ e, ((An e).modulus : L) ≠ 0 := fun e => (hpair e).2.2.1
  have hQex : ∀ e, ∃ Q : Place L F, Q ∈ (An e).dom ∧ (Q.evalAt (An e).param) ^ 2 = ((An e).modulus : L) :=
    fun e => VCI.exists_place_sq_eq_modulus (An e) (hmod0 e)
  choose Qe hQe using hQex
  have hQrat : ∀ e, ∃ (N d : ℕ) (u : Aˣ), 0 < N ∧
      ((Qe e).evalAt (An e).param) ^ N = ((u : A) : L) * (π : L) ^ d := by
    intro e
    obtain ⟨u, hu⟩ := hw e
    exact ⟨2, w e, u, two_pos, by rw [(hQe e).2, hu]; push_cast; rfl⟩

  have H : ∀ (k : ℕ) (c : Fin m → ℤ), (∑ e, c e • TateModule.proj ℓ (Pic0 L F) k (x e)) = 0 →
      ∃ b : Fin n → IsLocalRing.ResidueField A, (∀ i, b i ≠ 0) ∧ ∀ e, ζ k ^ (c e) * b (src e) = b (tgt e) := by
    intro k c hrel

    have hQ'ex : ∀ e, ∃ Q' : Place L F, Q' ∈ (An e).dom ∧
        Q'.evalAt (An e).param = ξ k * (Qe e).evalAt (An e).param := by
      intro e
      obtain ⟨-, -, ⟨hA, -⟩, -, -⟩ := (An e).mem_dom (Qe e) (hQe e).1
      have hv : A.valuation (((⟨ξ k, hξA k⟩ * ⟨(Qe e).evalAt (An e).param, hA⟩ : A) : L)) =
          A.valuation ((Qe e).evalAt (An e).param) := by
        push_cast
        rw [map_mul]
        have : A.valuation (ξ k) = 1 := by
          have h1 : A.valuation (ξ k) ^ (ℓ ^ k) = 1 := by rw [← map_pow, hξpow, map_one]
          exact (pow_eq_one_iff.mp h1).resolve_right (pow_ne_zero k hℓpos.ne')
        rw [this, one_mul]
      obtain ⟨Q', hQ', hQ'z⟩ := VCI.exists_place_evalAt_eq_of_valuation_eq (An e) (Qe e) (hQe e).1 _ hv
      exact ⟨Q', hQ', by rw [hQ'z]; push_cast; rfl⟩
    choose Q' hQ' using hQ'ex
    have hxe := fun e => hx e k (Qe e) (Q' e) (hQe e).1 (hQ' e).1 (hQrat e) (hQ' e).2
    choose Die r eqe nqe Qqe hDie_dom hDie_red hQqe hQqrat hrade hbale hDie_mk using hxe

    let quad : ∀ e, Fin (r e) → Divisor L F := fun e j =>
      (Finsupp.single (Qqe e j 0) 1 : Divisor L F) + Finsupp.single (Qqe e j 1) 1
        - Finsupp.single (Qqe e j 2) 1 - Finsupp.single (Qqe e j 3) 1
    have hdegquad : ∀ e j, Divisor.degree (quad e j) = 0 := by
      intro e j
      show Divisor.degree ((Finsupp.single (Qqe e j 0) 1 : Divisor L F) + Finsupp.single (Qqe e j 1) 1
        - Finsupp.single (Qqe e j 2) 1 - Finsupp.single (Qqe e j 3) 1) = 0
      rw [map_sub, map_sub, map_add, Divisor.degree_single, Divisor.degree_single, Divisor.degree_single,
        Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
        IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed]
      simp

    have hdegDie : ∀ e i, Divisor.degree (Die e i) = 0 := by
      intro e i
      rw [VCI.degree_eq_sum]
      have hmd := Finsupp.sum_mapDomain_index (f := (C i).placeMap) (s := Die e i)
        (h := fun (_ : Place (IsLocalRing.ResidueField A) (Fbar i)) (k : ℤ) => k) (fun _ => rfl) (fun _ _ _ => rfl)
      rw [hDie_red e i, Finsupp.sum_zero_index] at hmd
      exact hmd.symm
    let X : Fin m → Divisor L F := fun e =>
      (Finsupp.single (Qe e) 1 : Divisor L F) - Finsupp.single (Q' e) 1 - ∑ i, Die e i
        - ∑ j, nqe e j • ((Finsupp.single (Qqe e j 0) 1 : Divisor L F) + Finsupp.single (Qqe e j 1) 1
            - Finsupp.single (Qqe e j 2) 1 - Finsupp.single (Qqe e j 3) 1)
    have hdeg : ∀ e, X e ∈ Divisor.degZero (K := L) (F := F) := by
      intro e
      show (Finsupp.single (Qe e) 1 : Divisor L F) - Finsupp.single (Q' e) 1 - ∑ i, Die e i
        - ∑ j, nqe e j • ((Finsupp.single (Qqe e j 0) 1 : Divisor L F) + Finsupp.single (Qqe e j 1) 1
            - Finsupp.single (Qqe e j 2) 1 - Finsupp.single (Qqe e j 3) 1) ∈ Divisor.degZero
      rw [Divisor.mem_degZero, map_sub, map_sub, map_sub, map_sum, map_sum, Divisor.degree_single, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed]
      simp [hdegDie, hdegquad, quad]
    have hmk : ∀ e, TateModule.proj ℓ (Pic0 L F) k (x e) = Pic0.mk ⟨X e, hdeg e⟩ := fun e => hDie_mk e (hdeg e)

    have hprinX : (∑ e, c e • X e) ∈ Divisor.principal (K := L) (F := F) := by
      have h0 : Pic0.mk (∑ e, c e • (⟨X e, hdeg e⟩ : Divisor.degZero (K := L) (F := F))) = 0 := by
        have : Pic0.mk (∑ e, c e • (⟨X e, hdeg e⟩ : Divisor.degZero (K := L) (F := F))) =
            ∑ e, c e • Pic0.mk ⟨X e, hdeg e⟩ := by
          show QuotientAddGroup.mk' _ (∑ e, c e • (⟨X e, hdeg e⟩ : Divisor.degZero (K := L) (F := F))) =
            ∑ e, c e • QuotientAddGroup.mk' _ ⟨X e, hdeg e⟩
          rw [map_sum]
          exact Finset.sum_congr rfl (fun e _ => map_zsmul _ _ _)
        rw [this]
        simp_rw [← hmk]
        exact hrel
      rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
      have hcoe : ((∑ e, c e • (⟨X e, hdeg e⟩ : Divisor.degZero (K := L) (F := F)) : Divisor.degZero (K := L) (F := F)) : Divisor L F) =
          ∑ e, c e • X e := by
        rw [AddSubgroup.val_finsetSum]
        rfl
      rwa [hcoe] at h0

    let Di : Fin n → Divisor L F := fun i => ∑ e, c e • Die e i
    let eq : (Σ e : Fin m, Fin (r e)) → Fin m := fun p => eqe p.1 p.2
    let nq : (Σ e : Fin m, Fin (r e)) → ℤ := fun p => c p.1 * nqe p.1 p.2
    let Qq : (Σ e : Fin m, Fin (r e)) → Fin 4 → Place L F := fun p => Qqe p.1 p.2
    have hregroup : ∑ e, c e • X e =
        (∑ e, c e • ((Finsupp.single (Qe e) 1 : Divisor L F) - Finsupp.single (Q' e) 1)) - (∑ i, Di i)
          - ∑ p : (Σ e : Fin m, Fin (r e)), nq p • ((Finsupp.single (Qq p 0) 1 : Divisor L F) + Finsupp.single (Qq p 1) 1
              - Finsupp.single (Qq p 2) 1 - Finsupp.single (Qq p 3) 1) := by
      show ∑ e, c e • ((Finsupp.single (Qe e) 1 : Divisor L F) - Finsupp.single (Q' e) 1 - ∑ i, Die e i
          - ∑ j, nqe e j • ((Finsupp.single (Qqe e j 0) 1 : Divisor L F) + Finsupp.single (Qqe e j 1) 1
            - Finsupp.single (Qqe e j 2) 1 - Finsupp.single (Qqe e j 3) 1)) =
        (∑ e, c e • ((Finsupp.single (Qe e) 1 : Divisor L F) - Finsupp.single (Q' e) 1)) - (∑ i, ∑ e, c e • Die e i)
          - ∑ p : (Σ e : Fin m, Fin (r e)), (c p.1 * nqe p.1 p.2) •
              ((Finsupp.single (Qqe p.1 p.2 0) 1 : Divisor L F) + Finsupp.single (Qqe p.1 p.2 1) 1
              - Finsupp.single (Qqe p.1 p.2 2) 1 - Finsupp.single (Qqe p.1 p.2 3) 1)
      rw [Finset.sum_comm, Fintype.sum_sigma, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      rw [smul_sub, smul_sub, Finset.smul_sum, Finset.smul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_smul]
    have hDi_dom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom := by
      intro i P hP
      have hP' := Finsupp.support_finsetSum (s := (Finset.univ : Finset (Fin m))) (f := fun e => c e • Die e i) hP
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hP'
      obtain ⟨e, he⟩ := hP'
      exact hDie_dom e i P (Finsupp.support_smul he)
    have hDi_red : ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) = 0 := by
      intro i
      show Finsupp.mapDomain.addMonoidHom (C i).placeMap (∑ e, c e • Die e i) = 0
      rw [map_sum]
      refine Finset.sum_eq_zero (fun e _ => ?_)
      rw [map_zsmul]
      show c e • Finsupp.mapDomain (C i).placeMap (Die e i) = 0
      rw [hDie_red e i, smul_zero]
    have hprin : (∑ e, c e • ((Finsupp.single (Qe e) 1 : Divisor L F) - Finsupp.single (Q' e) 1)) - (∑ i, Di i)
        - (∑ p : (Σ e : Fin m, Fin (r e)), nq p • ((Finsupp.single (Qq p 0) 1 : Divisor L F) + Finsupp.single (Qq p 1) 1
              - Finsupp.single (Qq p 2) 1 - Finsupp.single (Qq p 3) 1)) ∈
        Divisor.principal (K := L) (F := F) := hregroup ▸ hprinX
    obtain ⟨hξA', b, hb0, hb⟩ :=
      AlgebraicCurve.exists_residue_pow_mul_eq_of_sum_smul_single_sub_single_sub_sum_sub_sum_smul_quadruple_mem_principal_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
        A π hπ hπ0 hrk F n m Fbar hratBar C hratF An An' src tgt xs xt w hpair hw hatt hnodes hcover hdisc hgenus
        S hS hSlift ℓ hℓ hSℓ M D ξ hξ0 hξ hξ1 k c Qe Q' (fun e => (hQe e).1) (fun e => (hQ' e).1) hQrat
        (fun e => (hQ' e).2) Di hDi_dom hDi_red eq nq Qq (fun p l => hQqe p.1 p.2 l) (fun p => hrade p.1 p.2)
        (fun p => hbale p.1 p.2) hprin
    exact ⟨b, hb0, fun e => hb e⟩
  exact TateModule.add_one_le_finrank_span_tmul_add_of_forall_proj_rel_coboundary ℓ (Pic0 L F) n m hn src tgt (IsLocalRing.ResidueField A) ζ hζ0 hζ hζ1 x H

end S_AlgebraicCurve_add_le_finrank_span_tmul_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_add_le_finrank_span_tmul_of_forall_proj_eq_mk_single_sub_single_quadruples_annulus_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel (solution)
