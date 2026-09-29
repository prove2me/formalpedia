-- Prove2me | solution 1 for AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f403ae3f-545c-53cd-b42b-1ecc9745475a

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_WeightedMultigraph_slope_eq_zero_of_gradient_of_harmonic
import Theorems.Thm_AlgebraicCurve_Annulus_ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached
import Theorems.Thm_AlgebraicCurve_ComponentChart_ord_residue_eq_zero_of_forall_ord_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

universe u v w

open AlgebraicCurve IsLocalRing

namespace VertAux

theorem energy
    {ιV : Type u} {ιE : Type v} [Fintype ιV] [Fintype ιE] [DecidableEq ιV] (src tgt : ιE → ιV)
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ] (γ : Γ) (hγ0 : γ ≠ 0) (hγ1 : γ < 1)
    (w : ιE → ℕ) (hw : ∀ e, 0 < w e) (m : ιE → ℤ)
    (v : ιV → Γ) (hv : ∀ i, v i ≠ 0)
    (hedge : ∀ e, v (tgt e) = v (src e) * γ ^ ((w e : ℤ) * m e))
    (hkirch : ∀ i, (∑ e ∈ Finset.univ.filter (fun e => src e = i), m e) =
      ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), m e) :
    ∀ e, m e = 0 := by

  set uγ : Γˣ := Units.mk0 γ hγ0 with huγ
  set u : ιV → Γˣ := fun i => Units.mk0 (v i) (hv i) with hu
  have hedgeU : ∀ e, u (tgt e) = u (src e) * uγ ^ ((w e : ℤ) * m e) := by
    intro e
    apply Units.ext
    simp only [hu, huγ, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    exact hedge e
  have huγ1 : uγ ≠ 1 := by
    intro h1
    have : (uγ : Γ) = 1 := by rw [h1, Units.val_one]
    rw [huγ, Units.val_mk0] at this
    exact (ne_of_lt hγ1) this
  let H : ιV → Additive Γˣ := fun i => Additive.ofMul (u i)
  let vπ : Additive Γˣ := Additive.ofMul uγ
  have hvπ : vπ ≠ 0 := by
    intro h0
    apply huγ1
    exact Additive.ofMul.injective h0
  have hgrad : ∀ e, H (tgt e) - H (src e) = ((w e : ℤ) * m e) • vπ := by
    intro e
    show Additive.ofMul (u (tgt e)) - Additive.ofMul (u (src e)) = ((w e : ℤ) * m e) • Additive.ofMul uγ
    rw [← ofMul_div, ← ofMul_zpow, hedgeU e, mul_div_cancel_left]
  have hharm : ∀ i, (∑ e ∈ Finset.univ.filter (fun e => tgt e = i), m e) =
      ∑ e ∈ Finset.univ.filter (fun e => src e = i), m e := fun i => (hkirch i).symm
  exact WeightedMultigraph.slope_eq_zero_of_gradient_of_harmonic src tgt w hw vπ hvπ H m hgrad hharm

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem inv_mem_integers_of_residue_ne_zero (C : ComponentChart A F Fbar) (f : F) (hf : f ∈ C.integers)
    (h : C.residue ⟨f, hf⟩ ≠ 0) : f⁻¹ ∈ C.integers := by
  have hu : IsUnit (⟨f, hf⟩ : ↥C.integers) := by
    by_contra hnu
    apply h
    have : (⟨f, hf⟩ : ↥C.integers) ∈ RingHom.ker C.residue := by
      rw [C.ker_residue]; exact hnu
    exact this
  have h1 : C.integers.valuation f = 1 := (C.integers.valuation_eq_one_iff ⟨f, hf⟩).mp hu
  rw [← C.integers.valuation_le_one_iff, map_inv₀, h1, inv_one]

theorem residue_algebraMap_eq_zero (C : ComponentChart A F Fbar) (t : A) (ht : t ∈ maximalIdeal A) :
    C.residue ⟨algebraMap L F (t : L), (C.algebraMap_mem_iff _).mpr t.2⟩ = 0 := by
  have hmem : (⟨algebraMap L F (t : L), (C.algebraMap_mem_iff _).mpr t.2⟩ : ↥C.integers) ∈
      RingHom.ker C.residue := by
    rw [C.ker_residue, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp ht
    have ht0 : (t : L) ≠ 0 := by
      intro h0
      apply hu.ne_zero
      exact Subtype.ext (by simp [h0])
    have h1 : C.integers.valuation (algebraMap L F (t : L)) = 1 := (C.integers.valuation_eq_one_iff _).mp hu
    have hmemi : algebraMap L F (t : L)⁻¹ ∈ C.integers := by
      rw [← C.integers.valuation_le_one_iff, map_inv₀, map_inv₀, h1, inv_one]
    have hti : (t : L)⁻¹ ∈ A := (C.algebraMap_mem_iff _).mp hmemi
    exact isUnit_iff_exists_inv.mpr ⟨⟨(t : L)⁻¹, hti⟩, Subtype.ext (mul_inv_cancel₀ ht0)⟩
  exact hmem

theorem degree_eq_sum_of_isRational {K F' : Type*} [Field K] [Field F'] [Algebra K F'] (D : Divisor K F')
    (hrat : ∀ v ∈ D.support, v.IsRational) (s : Finset (Place K F')) (hs : D.support ⊆ s) :
    Divisor.degree D = ∑ v ∈ s, D v := by
  classical
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rw [Finset.sum_subset hs (fun v _ hv => by
    have : D v = 0 := by simpa [Finsupp.mem_support_iff] using hv
    simp [this])]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  by_cases hD : v ∈ D.support
  · simp [Place.deg_eq_one_of_isRational (hrat v hD)]
  · have : D v = 0 := by simpa [Finsupp.mem_support_iff] using hD
    simp [this]

theorem exists_two_radii [IsAlgClosed L] (An : Annulus A F) (hμ : (An.modulus : L) ≠ 0) :
    ∃ P₁ ∈ An.dom, ∃ P₂ ∈ An.dom, A.valuation (P₁.evalAt An.param) ≠ A.valuation (P₂.evalAt An.param) := by
  have hμlt : A.valuation (An.modulus : L) < 1 := (A.valuation_lt_one_iff _).mp An.modulus_mem
  have hμ0 : A.valuation (An.modulus : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hμ

  have hadm : ∀ n : ℕ, 2 ≤ n → ∃ P ∈ An.dom, (P.evalAt An.param) ^ n = (An.modulus : L) := by
    intro n hn
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (An.modulus : L) (by omega : 0 < n)
    have hr0 : r ≠ 0 := by rintro rfl; rw [zero_pow (by omega)] at hr; exact hμ hr.symm
    have hvr : A.valuation r < 1 := by
      have hlt : A.valuation r ^ n < 1 := by rw [← map_pow, hr]; exact hμlt
      by_contra hle
      push_neg at hle
      exact absurd hlt (not_lt.mpr (one_le_pow_of_one_le' hle n))
    have hrA : r ∈ A := (A.valuation_le_one_iff r).mp hvr.le
    have hrm : (⟨r, hrA⟩ : A) ∈ maximalIdeal A := (A.valuation_lt_one_iff _).mpr hvr
    have hpowA : r ^ (n - 1) ∈ A := A.pow_mem hrA _
    have hpowm : (⟨r ^ (n - 1), hpowA⟩ : A) ∈ maximalIdeal A := by
      rw [A.valuation_lt_one_iff]
      show A.valuation (r ^ (n - 1)) < 1
      rw [map_pow]
      exact pow_lt_one' hvr (by omega)
    obtain ⟨P, ⟨hP, hPz⟩, -⟩ := An.existsUnique_evalAt_eq ⟨r, hrA⟩ hrm hr0
      ⟨⟨r ^ (n - 1), hpowA⟩, hpowm, by
        show (An.modulus : L) = r * r ^ (n - 1)
        rw [← pow_succ', Nat.sub_add_cancel (by omega), hr]⟩
    exact ⟨P, hP, by rw [hPz]; exact hr⟩
  obtain ⟨P₁, hP₁, h₁⟩ := hadm 2 le_rfl
  obtain ⟨P₂, hP₂, h₂⟩ := hadm 3 (by norm_num)
  refine ⟨P₁, hP₁, P₂, hP₂, fun heq => ?_⟩
  have h2 : A.valuation (P₂.evalAt An.param) ^ 2 = A.valuation (An.modulus : L) := by rw [← heq, ← map_pow, h₁]
  have h3 : A.valuation (P₂.evalAt An.param) ^ 3 = A.valuation (An.modulus : L) := by rw [← map_pow, h₂]
  have ha0 : A.valuation (P₂.evalAt An.param) ≠ 0 := by
    intro h0; apply hμ0; rw [← h2, h0, zero_pow two_ne_zero]
  have ha1 : A.valuation (P₂.evalAt An.param) = 1 := by
    have : A.valuation (P₂.evalAt An.param) ^ 2 * A.valuation (P₂.evalAt An.param) =
        A.valuation (P₂.evalAt An.param) ^ 2 * 1 := by rw [mul_one, ← pow_succ, h3, h2]
    exact mul_left_cancel₀ (pow_ne_zero 2 ha0) this
  apply ne_of_lt hμlt
  rw [← h2, ha1, one_pow]

end VertAux

open VertAux in

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    {ιV ιE : Type*} [Fintype ιV] [Fintype ιE] (Fbar : ιV → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : ιE → Annulus A F) (src tgt : ιE → ιV)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : ιE → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : ιE ⊕ ιE,
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
    (hgenus : genusFF L F + Fintype.card ιV =
      (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + Fintype.card ιE + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (G : Divisor L F)
    (k : ℕ) (hk : 0 < k) (g : F) (hg : g ≠ 0)
    (hkG : ∀ P : Place L F, P.ord g = (k : ℤ) *
      G P)
    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F)
    (hU : (⨆ a, U a) = ⊤) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) =
        G P)
    (hcoc : ∀ a b (x : M.X), x ∈ U a → x ∈ U b →
      ∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
        h a = h b * (1 + algebraMap L F ((t : A) : L) * r)) :
    ∃ c : ιV → L, (∀ i, c i ≠ 0) ∧
      (∀ i a, M.gen i ∈ U a →
        c i • (g / h a ^ k) ∈ (C i).integers ∧ (c i • (g / h a ^ k))⁻¹ ∈ (C i).integers) ∧
      (∀ e', A.valuation (c (src e')) = A.valuation (c (tgt e'))) := by
  classical

  have hπv0 : A.valuation ((π : A) : L) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (fun h0 => hπ0 (Subtype.ext h0))
  have hπv1 : A.valuation ((π : A) : L) < 1 := (A.valuation_lt_one_iff π).mp hπ
  have hwpos : ∀ e, 0 < w e := by
    intro e
    by_contra h0
    have hw0 : w e = 0 := by omega
    obtain ⟨u, hu⟩ := hw e
    rw [hw0, pow_zero, mul_one] at hu
    have : IsUnit (An e).modulus := by rw [hu]; exact u.isUnit
    exact (IsLocalRing.mem_maximalIdeal _).mp (An e).modulus_mem this
  have hmemU : ∀ x : M.X, ∃ a, x ∈ U a := fun x => by
    have hx : x ∈ (⨆ a, U a) := by rw [hU]; exact trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  have hφ0 : ∀ a, g / h a ^ k ≠ 0 := fun a => div_ne_zero hg (pow_ne_zero _ (hh a))
  have hord : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (g / h a ^ k) = 0 := by
    intro a P hP
    rw [div_eq_mul_inv, P.ord_mul hg (inv_ne_zero (pow_ne_zero _ (hh a))), P.ord_inv, ← zpow_natCast,
      P.ord_zpow, hkG P, hdiv a P hP]
    ring

  have hgen_of_nd : ∀ e a, M.nd e ∈ U a → M.gen (src e) ∈ U a ∧ M.gen (tgt e) ∈ U a := fun e a ha =>
    ⟨(M.gen_specializes_nd e).1.mem_open (U a).isOpen ha, (M.gen_specializes_nd e).2.mem_open (U a).isOpen ha⟩
  have hpt_of_nd : ∀ e a (P : Place L F), P ∈ (An e).dom → M.nd e ∈ U a → M.pt P ∈ U a :=
    fun e a P hP ha => (M.pt_specializes_nd e P hP).mem_open (U a).isOpen ha
  have hgen_of_sm : ∀ i (Q : {Q : Place (IsLocalRing.ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) a,
      M.sm i Q ∈ U a → M.gen i ∈ U a := fun i Q a ha => (M.gen_specializes_sm i Q).mem_open (U a).isOpen ha
  have hpt_of_sm : ∀ i (P : Place L F) (hP : P ∈ (C i).dom) a,
      M.sm i ⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hP⟩ ∈ U a → M.pt P ∈ U a :=
    fun i P hP a ha => (M.pt_specializes_sm i P hP).mem_open (U a).isOpen ha

  have htrans : ∀ i a b, M.gen i ∈ U a → M.gen i ∈ U b →
      ∃ u : F, ∃ hu : u ∈ (C i).integers, (C i).residue ⟨u, hu⟩ = 1 ∧ g / h a ^ k = g / h b ^ k * u := by
    intro i a b ha hb
    obtain ⟨t, ht, r, hr, heq⟩ := hcoc b a (M.gen i) hb ha
    rw [M.localRing_gen i] at hr
    have hr' : r ∈ (C i).integers := hr
    have hT : algebraMap L F ((t : A) : L) ∈ (C i).integers := ((C i).algebraMap_mem_iff _).mpr t.2
    have h1 : (1 + algebraMap L F ((t : A) : L) * r) ∈ (C i).integers :=
      add_mem (one_mem _) (mul_mem hT hr')
    refine ⟨(1 + algebraMap L F ((t : A) : L) * r) ^ k, pow_mem h1 k, ?_, ?_⟩
    · have hres1 : (C i).residue ⟨1 + algebraMap L F ((t : A) : L) * r, h1⟩ = 1 := by
        have : (⟨1 + algebraMap L F ((t : A) : L) * r, h1⟩ : ↥(C i).integers) =
            1 + ⟨algebraMap L F ((t : A) : L), hT⟩ * ⟨r, hr'⟩ := rfl
        rw [this, map_add, map_one, map_mul, VertAux.residue_algebraMap_eq_zero (C i) t ht, zero_mul, add_zero]
      have : (⟨(1 + algebraMap L F ((t : A) : L) * r) ^ k, pow_mem h1 k⟩ : ↥(C i).integers) =
          ⟨1 + algebraMap L F ((t : A) : L) * r, h1⟩ ^ k := rfl
      rw [this, map_pow, hres1, one_pow]
    · have hba : h b / h a = 1 + algebraMap L F ((t : A) : L) * r := by
        rw [heq, mul_div_cancel_left₀ _ (hh a)]
      rw [← hba, div_pow]
      field_simp [hh a, hh b]

  choose aV haV using fun i => hmemU (M.gen i)
  have hc' : ∀ i, ∃ c : L, ∃ hc : c • (g / h (aV i) ^ k) ∈ (C i).integers, (C i).residue ⟨_, hc⟩ ≠ 0 :=
    fun i => (C i).exists_smul_mem _ (hφ0 _)
  choose c hcmem hcres using hc'
  have hc0 : ∀ i, c i ≠ 0 := by
    intro i h0
    apply hcres i
    have : (⟨c i • (g / h (aV i) ^ k), hcmem i⟩ : ↥(C i).integers) = 0 :=
      Subtype.ext (by simp [h0])
    rw [this, map_zero]

  have hunit : ∀ i a, M.gen i ∈ U a → ∃ hm : c i • (g / h a ^ k) ∈ (C i).integers,
      (C i).residue ⟨_, hm⟩ = (C i).residue ⟨_, hcmem i⟩ := by
    intro i a ha
    obtain ⟨u, hu, hres, heq⟩ := htrans i a (aV i) ha (haV i)
    have hm : c i • (g / h a ^ k) ∈ (C i).integers := by
      rw [heq, ← smul_mul_assoc]; exact mul_mem (hcmem i) hu
    refine ⟨hm, ?_⟩
    have : (⟨c i • (g / h a ^ k), hm⟩ : ↥(C i).integers) = ⟨c i • (g / h (aV i) ^ k), hcmem i⟩ * ⟨u, hu⟩ :=
      Subtype.ext (by show c i • (g / h a ^ k) = c i • (g / h (aV i) ^ k) * u; rw [heq, smul_mul_assoc])
    rw [this, map_mul, hres, mul_one]
  refine ⟨c, hc0, fun i a ha => ?_, ?_⟩
  · obtain ⟨hm, hres⟩ := hunit i a ha
    exact ⟨hm, VertAux.inv_mem_integers_of_residue_ne_zero (C i) _ hm (by rw [hres]; exact hcres i)⟩

  choose aE haE using fun e => hmemU (M.nd e)
  have hordE : ∀ e, ∀ P ∈ (An e).dom, P.ord (g / h (aE e) ^ k) = 0 :=
    fun e P hP => hord _ P (hpt_of_nd e _ P hP (haE e))
  have hmS : ∀ e, c (src e) • (g / h (aE e) ^ k) ∈ (C (src e)).integers :=
    fun e => (hunit (src e) (aE e) (hgen_of_nd e _ (haE e)).1).1
  have hmT : ∀ e, c (tgt e) • (g / h (aE e) ^ k) ∈ (C (tgt e)).integers :=
    fun e => (hunit (tgt e) (aE e) (hgen_of_nd e _ (haE e)).2).1
  have hresS : ∀ e, (C (src e)).residue ⟨_, hmS e⟩ = (C (src e)).residue ⟨_, hcmem (src e)⟩ :=
    fun e => (hunit (src e) (aE e) (hgen_of_nd e _ (haE e)).1).2
  have hresT : ∀ e, (C (tgt e)).residue ⟨_, hmT e⟩ = (C (tgt e)).residue ⟨_, hcmem (tgt e)⟩ :=
    fun e => (hunit (tgt e) (aE e) (hgen_of_nd e _ (haE e)).2).2
  have hslope : ∀ e,
      (xt e).ord ((C (tgt e)).residue ⟨_, hmT e⟩) = -(xs e).ord ((C (src e)).residue ⟨_, hmS e⟩) ∧
      A.valuation (c (tgt e)) = A.valuation (c (src e)) *
        A.valuation ((An e).modulus : L) ^ (xt e).ord ((C (tgt e)).residue ⟨_, hmT e⟩) := fun e =>
    AlgebraicCurve.Annulus.ord_residue_eq_neg_and_valuation_eq_of_isAttached_of_isAttached A
      (C (src e)) (C (tgt e)) (An e) (An' e) (xs e) (xt e) (hpair e) (hatt e)
      (VertAux.exists_two_radii (An e) (hpair e).2.2.1) _ (hφ0 _) (hordE e) (c (src e)) (c (tgt e))
      (hmS e) (by rw [hresS]; exact hcres _) (hmT e) (by rw [hresT]; exact hcres _)

  set ψ : ∀ i, Fbar i := fun i => (C i).residue ⟨_, hcmem i⟩ with hψ
  set m : ιE → ℤ := fun e => (xt e).ord (ψ (tgt e)) with hm_def
  have hmt : ∀ e, (xt e).ord (ψ (tgt e)) = m e := fun e => rfl
  have hms : ∀ e, (xs e).ord (ψ (src e)) = -m e := by
    intro e
    have h1 := (hslope e).1
    rw [hresS e, hresT e] at h1
    show (xs e).ord (ψ (src e)) = -(xt e).ord (ψ (tgt e))
    simp only [hψ]
    omega
  have hedge : ∀ e, A.valuation (c (tgt e)) = A.valuation (c (src e)) * A.valuation ((π : A) : L) ^ ((w e : ℤ) * m e) := by
    intro e
    have h2 := (hslope e).2
    rw [hresT e] at h2
    obtain ⟨u, hu⟩ := hw e
    have hμ : A.valuation ((An e).modulus : L) = A.valuation ((π : A) : L) ^ (w e) := by
      rw [hu]
      push_cast
      rw [map_mul, map_pow, A.valuation_unit, one_mul]
    rw [h2, hμ, ← zpow_natCast, ← zpow_mul]

  let node : ιE ⊕ ιE → (Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) :=
    Sum.elim (fun e => ⟨src e, xs e⟩) (fun e => ⟨tgt e, xt e⟩)
  let ordN : (Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) → ℤ := fun p => p.2.ord (ψ p.1)
  have hnode_mem : ∀ E : ιE ⊕ ιE, (node E).2 ∈ (C (node E).1).nodes := by
    rintro (e | e)
    · exact (hatt e).1.1
    · exact (hatt e).2.1
  have hkirch : ∀ i, (∑ e ∈ Finset.univ.filter (fun e => src e = i), m e) =
      ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), m e := by
    intro i
    haveI : HasPrincipalDivisors (IsLocalRing.ResidueField A) (Fbar i) := IsCurveOver.hasPrincipalDivisors
    obtain ⟨D, hD, hdeg⟩ :=
      HasPrincipalDivisors.exists_divisor (K := IsLocalRing.ResidueField A) (F := Fbar i) (ψ i) (hcres i)

    have hsupp : D.support ⊆ (C i).nodes := by
      intro Q hQ
      by_contra hQn
      apply Finsupp.mem_support_iff.mp hQ
      rw [hD]
      obtain ⟨b, hb⟩ := hmemU (M.sm i ⟨Q, hQn⟩)
      obtain ⟨hm, hres⟩ := hunit i b (hgen_of_sm i ⟨Q, hQn⟩ b hb)
      rw [show ψ i = (C i).residue ⟨_, hm⟩ from hres.symm]
      refine AlgebraicCurve.ComponentChart.ord_residue_eq_zero_of_forall_ord_eq_zero A (C i) _ hm
        (by rw [hres]; exact hcres i) Q hQn (fun P hP hPQ => ?_)
      rw [AlgebraicCurve.ConstantReduction.ord_smul P (hc0 i)]
      apply hord b P
      apply hpt_of_sm i P hP b
      have : (⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hP⟩ :
          {Q : Place (IsLocalRing.ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) = ⟨Q, hQn⟩ := Subtype.ext hPQ
      rw [this]
      exact hb
    have hsum : ∑ x ∈ (C i).nodes, D x = 0 := by
      rw [← VertAux.degree_eq_sum_of_isRational D (fun v _ => hratBar i v) _ hsupp]
      exact hdeg
    have hsum' : ∑ x ∈ (C i).nodes, ordN ⟨i, x⟩ = 0 := by
      rw [← hsum]
      exact Finset.sum_congr rfl (fun x _ => (hD x).symm)

    have hT : ((C i).nodes.map (Function.Embedding.sigmaMk i)) =
        (Finset.univ.filter (fun E : ιE ⊕ ιE => (node E).1 = i)).image node := by
      ext p
      simp only [Finset.mem_map, Function.Embedding.sigmaMk_apply, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨e, he⟩ := hnodes.1 i x hx
        rcases he with he | he
        · exact ⟨Sum.inl e, by simp [node, he], he⟩
        · exact ⟨Sum.inr e, by simp [node, he], he⟩
      · rintro ⟨E, hE, rfl⟩
        refine ⟨?_, ?_, ?_⟩
        · exact hE ▸ (node E).2
        · subst hE; exact hnode_mem E
        · subst hE; rfl
    have hsig : ∀ E : ιE ⊕ ιE, node E = ⟨(node E).1, (node E).2⟩ := by
      rintro (e | e) <;> rfl
    have hinj : Set.InjOn node ↑(Finset.univ.filter (fun E : ιE ⊕ ιE => (node E).1 = i)) := by
      intro E hE E' hE' hEE'
      have hx : (node E).2 ∈ (C (node E).1).nodes := hnode_mem E
      exact hnodes.2 (node E).1 (node E).2 hx E E' (hsig E) (hEE'.symm.trans (hsig E))
    have hreidx : ∑ x ∈ (C i).nodes, ordN ⟨i, x⟩ =
        ∑ E ∈ Finset.univ.filter (fun E : ιE ⊕ ιE => (node E).1 = i), ordN (node E) := by
      rw [← Finset.sum_image hinj, ← hT, Finset.sum_map]
      rfl
    have hsplit : ∑ E ∈ Finset.univ.filter (fun E : ιE ⊕ ιE => (node E).1 = i), ordN (node E) =
        (∑ e ∈ Finset.univ.filter (fun e => src e = i), -m e) +
          ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), m e := by
      rw [Finset.sum_filter, Fintype.sum_sum_type, Finset.sum_filter, Finset.sum_filter]
      congr 1
      · refine Finset.sum_congr rfl (fun e _ => ?_)
        show (if src e = i then ordN ⟨src e, xs e⟩ else 0) = if src e = i then -m e else 0
        rw [show ordN ⟨src e, xs e⟩ = (xs e).ord (ψ (src e)) from rfl, hms e]
    have h0 : (∑ e ∈ Finset.univ.filter (fun e => src e = i), -m e) +
        ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), m e = 0 := by
      rw [← hsplit, ← hreidx, hsum']
    rw [Finset.sum_neg_distrib] at h0
    linarith

  have hm0 := VertAux.energy src tgt (A.valuation ((π : A) : L)) hπv0 hπv1 w hwpos m
    (fun i => A.valuation (c i)) (fun i => (Valuation.ne_zero_iff _).mpr (hc0 i)) hedge hkirch
  intro e
  have he := hedge e
  rw [hm0 e, mul_zero, zpow_zero, mul_one] at he
  exact he.symm

end S_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel
end P2MW
export P2MW.S_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel (solution)
