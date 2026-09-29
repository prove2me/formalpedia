-- Prove2me | solution 1 for AlgebraicCurve.exists_forall_ord_residue_smul_eq_zero_of_forall_degree_eq_zero_of_semistableCovering
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/93fa0f68-aaf4-55b4-882d-d64e01e62fd6

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Theorems.Thm_WeightedMultigraph_slope_eq_zero_of_gradient_of_harmonic
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_evalAt_ne_zero
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_forall_ord_residue_smul_eq_zero_of_forall_degree_eq_zero_of_semistableCovering
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace HarmonicNodesSol

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_const_smul (v : Place K F) {c : K} (hc : c ≠ 0) {f : F} (hf : f ≠ 0) :
    v.ord (c • f) = v.ord f := by
  rw [Algebra.smul_def, v.ord_mul ((map_ne_zero (algebraMap K F)).mpr hc) hf,
    AlgebraicCurve.Place.ord_algebraMap, zero_add]

theorem degree_eq_finsuppDegree (D : Divisor K F) (h : ∀ P ∈ D.support, Place.IsRational P) :
    Divisor.degree D = Finsupp.degree D := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.degree_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun P hP => ?_
  have h1 : P.deg = 1 := (AlgebraicCurve.Place.isRational_iff_deg_eq_one P).mp (h P hP)
  simp [h1]

theorem evalAt_const_smul (v : Place K F) (hv : v.IsRational) (c : K) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (c • f) = c * v.evalAt f := by
  rw [Algebra.smul_def, AlgebraicCurve.Place.evalAt_mul v hv (v.algebraMap_mem' c) hf,
    AlgebraicCurve.Place.evalAt_algebraMap]

end PlaceFacts

section Log

variable {L : Type*} [Field L] (A : ValuationSubring L)

open Classical in

def lg (x : L) : Additive (A.ValueGroup)ˣ :=
  if hx : x = 0 then 0
  else Additive.ofMul (Units.mk0 (A.valuation x) ((Valuation.ne_zero_iff _).mpr hx))

variable {A}

theorem lg_of_ne_zero {x : L} (hx : x ≠ 0) :
    lg A x = Additive.ofMul (Units.mk0 (A.valuation x) ((Valuation.ne_zero_iff _).mpr hx)) := by
  classical
  rw [lg, dif_neg hx]

theorem toMul_lg_val {x : L} (hx : x ≠ 0) :
    ((Additive.toMul (lg A x) : (A.ValueGroup)ˣ) : A.ValueGroup) = A.valuation x := by
  rw [lg_of_ne_zero hx]
  simp

theorem lg_eq_lg_iff {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) :
    lg A x = lg A y ↔ A.valuation x = A.valuation y := by
  constructor
  · intro h
    rw [← toMul_lg_val hx, ← toMul_lg_val hy, h]
  · intro h
    rw [lg_of_ne_zero hx, lg_of_ne_zero hy]
    congr 1
    ext
    simpa using h

theorem lg_eq_zero_iff {x : L} (hx : x ≠ 0) : lg A x = 0 ↔ A.valuation x = 1 := by
  have h1 : lg A (1 : L) = 0 := by
    rw [lg_of_ne_zero one_ne_zero]
    rw [ofMul_eq_zero]
    ext
    simp
  rw [← h1, lg_eq_lg_iff hx one_ne_zero, map_one]

theorem lg_mul {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : lg A (x * y) = lg A x + lg A y := by
  rw [lg_of_ne_zero hx, lg_of_ne_zero hy, lg_of_ne_zero (mul_ne_zero hx hy), ← ofMul_mul]
  congr 1
  ext
  simp

theorem lg_inv {x : L} (hx : x ≠ 0) : lg A x⁻¹ = -lg A x := by
  have h : lg A (x⁻¹ * x) = 0 := by
    rw [inv_mul_cancel₀ hx, lg_eq_zero_iff one_ne_zero, map_one]
  rw [lg_mul (inv_ne_zero hx) hx] at h
  exact eq_neg_of_add_eq_zero_left h

theorem lg_pow {x : L} (hx : x ≠ 0) (n : ℕ) : lg A (x ^ n) = (n : ℤ) • lg A x := by
  induction n with
  | zero => simp [lg_eq_zero_iff one_ne_zero]
  | succ n ih =>
      rw [pow_succ, lg_mul (pow_ne_zero n hx) hx, ih]
      push_cast
      rw [add_smul, one_smul]

theorem lg_zpow {x : L} (hx : x ≠ 0) (n : ℤ) : lg A (x ^ n) = n • lg A x := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, lg_pow hx]
  | negSucc n =>
      rw [zpow_negSucc, lg_inv (pow_ne_zero _ hx), lg_pow hx, Int.negSucc_eq, neg_smul]
      push_cast
      rfl

theorem lg_eq_zero_of_isUnit {x : L} (hxA : x ∈ A) (h : IsUnit (⟨x, hxA⟩ : A)) : lg A x = 0 := by
  have hx : x ≠ 0 := by
    rintro rfl
    have h0 : (⟨(0 : L), hxA⟩ : A) = 0 := rfl
    rw [h0] at h
    exact not_isUnit_zero h
  rw [lg_eq_zero_iff hx]
  exact (ValuationSubring.valuation_eq_one_iff A _).mp h

theorem lg_ne_zero_of_mem_maximalIdeal {x : A} (hx : x ∈ maximalIdeal A) (hx0 : x ≠ 0) :
    lg A (x : L) ≠ 0 := by
  intro h
  have hx0' : (x : L) ≠ 0 := fun h' => hx0 (Subtype.ext h')
  rw [lg_eq_zero_iff hx0'] at h
  have := (ValuationSubring.valuation_lt_one_iff A x).mp hx
  rw [h] at this
  exact lt_irrefl _ this

theorem lg_unit (u : Aˣ) : lg A ((u : A) : L) = 0 :=
  lg_eq_zero_of_isUnit (u : A).2 u.isUnit

end Log

section EdgeLaw

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fs : Type*} [Field Fs] [Algebra (ResidueField A) Fs]
variable {Ft : Type*} [Field Ft] [Algebra (ResidueField A) Ft]

theorem residue_ne_zero_imp_ne_zero (C : ComponentChart A F Fs) {c : L} {f : F}
    (hc : c • f ∈ C.integers) (hc0 : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hc0
  have h0 : (⟨(0 : L) • f, hc⟩ : C.integers) = 0 := Subtype.ext (zero_smul L f)
  rw [h0, map_zero]

theorem slope_law_lg (An : Annulus A F) (C : ComponentChart A F Fs) (x : Place (ResidueField A) Fs)
    (hatt : An.IsAttached C x) (f : F) (hf0 : f ≠ 0) (hford : ∀ P ∈ An.dom, P.ord f = 0)
    (c : L) (hc : c • f ∈ C.integers) (hc0 : C.residue ⟨c • f, hc⟩ ≠ 0)
    {P : Place L F} (hP : P ∈ An.dom) :
    lg A c + lg A (P.evalAt f) = (x.ord (C.residue ⟨c • f, hc⟩)) • lg A (P.evalAt An.param) := by
  obtain ⟨-, hz, -, hslope⟩ := hatt
  have hcne : c ≠ 0 := residue_ne_zero_imp_ne_zero C hc hc0
  have hford' : ∀ Q ∈ An.dom, Q.ord (c • f) = 0 := fun Q hQ => by
    rw [ord_const_smul Q hcne hf0]; exact hford Q hQ
  obtain ⟨hmem, hunit⟩ := hslope (c • f) hc hc0 hford' P hP
  obtain ⟨hPr, hzP, ⟨hzA, -⟩, hz0, -⟩ := An.mem_dom P hP
  have hfP : f ∈ P.toValuationSubring :=
    (AlgebraicCurve.Place.mem_iff_ord_nonneg P hf0).mpr (by rw [hford P hP])
  have hef0 : P.evalAt f ≠ 0 := AlgebraicCurve.Place.evalAt_ne_zero P hPr hf0 (hford P hP)
  have h := lg_eq_zero_of_isUnit hmem hunit
  rw [evalAt_const_smul P hPr c hfP, lg_mul (mul_ne_zero hcne hef0) (zpow_ne_zero _ hz0),
    lg_mul hcne hef0, lg_zpow hz0, neg_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h

theorem edge_law [IsAlgClosed L] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0)
    (An An' : Annulus A F) (Cs : ComponentChart A F Fs) (Ct : ComponentChart A F Ft)
    (xs : Place (ResidueField A) Fs) (xt : Place (ResidueField A) Ft) (w : ℕ)
    (hdom : An'.dom = An.dom)
    (hzz : An'.param * An.param = algebraMap L F (An.modulus : L))
    (hw : ∃ u : Aˣ, An.modulus = u * π ^ w)
    (hs : An.IsAttached Cs xs) (ht : An'.IsAttached Ct xt)
    (f : F) (hf0 : f ≠ 0) (hford : ∀ P ∈ An.dom, P.ord f = 0)
    (cs : L) (hcs : cs • f ∈ Cs.integers) (hcs0 : Cs.residue ⟨cs • f, hcs⟩ ≠ 0)
    (ct : L) (hct : ct • f ∈ Ct.integers) (hct0 : Ct.residue ⟨ct • f, hct⟩ ≠ 0) :
    xs.ord (Cs.residue ⟨cs • f, hcs⟩) + xt.ord (Ct.residue ⟨ct • f, hct⟩) = 0 ∧
    lg A ct - lg A cs = ((w : ℤ) * xt.ord (Ct.residue ⟨ct • f, hct⟩)) • lg A ((π : A) : L) := by
  set a := xs.ord (Cs.residue ⟨cs • f, hcs⟩) with ha
  set b := xt.ord (Ct.residue ⟨ct • f, hct⟩) with hb
  have hπL : ((π : A) : L) ≠ 0 := fun h => hπ0 (ZeroMemClass.coe_eq_zero.mp h)
  have hπv : A.valuation ((π : A) : L) < 1 := (ValuationSubring.valuation_lt_one_iff A π).mp hπ
  have hlgπ : lg A ((π : A) : L) ≠ 0 := lg_ne_zero_of_mem_maximalIdeal hπ hπ0

  have hford_t : ∀ P ∈ An'.dom, P.ord f = 0 := fun P hP => hford P (hdom ▸ hP)
  have key : ∀ P ∈ An.dom,
      lg A cs - lg A ct = (a + b) • lg A (P.evalAt An.param) - b • lg A (An.modulus : L) := by
    intro P hP
    have hP' : P ∈ An'.dom := hdom ▸ hP
    have h1 := slope_law_lg An Cs xs hs f hf0 hford cs hcs hcs0 hP
    have h2 := slope_law_lg An' Ct xt ht f hf0 hford_t ct hct hct0 hP'
    obtain ⟨hPr, hzP, -, hz0, -⟩ := An.mem_dom P hP
    obtain ⟨-, hz'P, -, hz'0, -⟩ := An'.mem_dom P hP'

    have hprod : P.evalAt An'.param * P.evalAt An.param = (An.modulus : L) := by
      rw [← AlgebraicCurve.Place.evalAt_mul P hPr hz'P hzP, hzz, AlgebraicCurve.Place.evalAt_algebraMap]
    have hlgz' : lg A (P.evalAt An'.param) = lg A (An.modulus : L) - lg A (P.evalAt An.param) := by
      rw [← hprod, lg_mul hz'0 hz0]; abel
    rw [hlgz'] at h2
    rw [← ha] at h1
    rw [← hb] at h2
    have h3 : lg A cs - lg A ct = (lg A cs + lg A (P.evalAt f)) - (lg A ct + lg A (P.evalAt f)) := by
      abel
    rw [h3, h1, h2]
    module

  obtain ⟨u, hu⟩ := hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    have hmax := An.modulus_mem
    rw [hu, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax
    exact hmax u.isUnit
  obtain ⟨w', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hw0

  obtain ⟨r₁, hr₁⟩ := IsAlgClosed.exists_eq_mul_self ((π : A) : L)
  have hr₁0 : r₁ ≠ 0 := by rintro rfl; exact hπL (by rw [hr₁, mul_zero])
  obtain ⟨r₂, hr₂⟩ := IsAlgClosed.exists_eq_mul_self r₁
  have hr₂0 : r₂ ≠ 0 := by rintro rfl; exact hr₁0 (by rw [hr₂, mul_zero])
  have hvr₁ : A.valuation r₁ < 1 := by
    by_contra h
    have h2 := one_le_mul (not_lt.mp h) (not_lt.mp h)
    rw [← map_mul, ← hr₁] at h2
    exact absurd hπv (not_lt.mpr h2)
  have hvr₂ : A.valuation r₂ < 1 := by
    by_contra h
    have h2 := one_le_mul (not_lt.mp h) (not_lt.mp h)
    rw [← map_mul, ← hr₂] at h2
    exact absurd hvr₁ (not_lt.mpr h2)
  have hr₁A : r₁ ∈ A := A.mem_of_valuation_le_one _ hvr₁.le
  have hr₂A : r₂ ∈ A := A.mem_of_valuation_le_one _ hvr₂.le
  have hr₁m : (⟨r₁, hr₁A⟩ : A) ∈ maximalIdeal A := (ValuationSubring.valuation_lt_one_iff A _).mpr hvr₁
  have hr₂m : (⟨r₂, hr₂A⟩ : A) ∈ maximalIdeal A := (ValuationSubring.valuation_lt_one_iff A _).mpr hvr₂
  have hlgr₂ : lg A r₂ ≠ 0 := by
    rw [Ne, lg_eq_zero_iff hr₂0]
    exact hvr₂.ne
  have hlgr₁ : lg A r₁ = lg A r₂ + lg A r₂ := by rw [← lg_mul hr₂0 hr₂0, ← hr₂]

  have hadm₁ : ∃ m ∈ maximalIdeal A, (An.modulus : L) = ((⟨r₁, hr₁A⟩ : A) : L) * m := by
    refine ⟨⟨r₁, hr₁A⟩ * (u : A) * π ^ w', ?_, ?_⟩
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hr₁m)
    · rw [hu]
      push_cast
      rw [pow_succ, hr₁]
      ring
  have hadm₂ : ∃ m ∈ maximalIdeal A, (An.modulus : L) = ((⟨r₂, hr₂A⟩ : A) : L) * m := by
    refine ⟨⟨r₂, hr₂A⟩ * ⟨r₁, hr₁A⟩ * (u : A) * π ^ w', ?_, ?_⟩
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hr₂m))
    · rw [hu]
      push_cast
      rw [pow_succ, hr₁, hr₂]
      ring
  obtain ⟨P₁, ⟨hP₁, hzP₁⟩, -⟩ :=
    An.existsUnique_evalAt_eq ⟨r₁, hr₁A⟩ hr₁m (by exact hr₁0) hadm₁
  obtain ⟨P₂, ⟨hP₂, hzP₂⟩, -⟩ :=
    An.existsUnique_evalAt_eq ⟨r₂, hr₂A⟩ hr₂m (by exact hr₂0) hadm₂
  have k₁ := key P₁ hP₁
  have k₂ := key P₂ hP₂
  rw [hzP₁] at k₁
  rw [hzP₂] at k₂
  change lg A cs - lg A ct = (a + b) • lg A r₁ - b • lg A (An.modulus : L) at k₁
  change lg A cs - lg A ct = (a + b) • lg A r₂ - b • lg A (An.modulus : L) at k₂
  have hab : a + b = 0 := by
    have h : (a + b) • lg A r₂ = 0 := by
      have h' : (a + b) • lg A r₁ - b • lg A (An.modulus : L) =
          (a + b) • lg A r₂ - b • lg A (An.modulus : L) := k₁.symm.trans k₂
      rw [hlgr₁] at h'
      have h'' : (a + b) • (lg A r₂ + lg A r₂) - (a + b) • lg A r₂ = 0 := by
        rw [sub_eq_zero]; exact sub_left_injective h'
      rw [← h'']
      module
    exact (IsAddTorsionFree.zsmul_eq_zero_iff_left (n := a + b) hlgr₂).mp h
  refine ⟨hab, ?_⟩

  have hlgmod : lg A (An.modulus : L) = ((w' + 1 : ℕ) : ℤ) • lg A ((π : A) : L) := by
    rw [hu]
    push_cast
    have hu0 : ((u : A) : L) ≠ 0 := fun h => (u.isUnit.ne_zero) (ZeroMemClass.coe_eq_zero.mp h)
    rw [lg_mul hu0 (pow_ne_zero _ hπL), lg_unit, zero_add, lg_pow hπL]
    push_cast
    rfl
  have hba : a = -b := by omega
  rw [hlgmod, hba] at k₂
  have : lg A ct - lg A cs = -(lg A cs - lg A ct) := by abel
  rw [this, k₂]
  module

theorem isUnit_evalAt_of_ord_eq_zero (An : Annulus A F) (C : ComponentChart A F Fs)
    (x : Place (ResidueField A) Fs)
    (hatt : An.IsAttached C x) (f : F) (hf0 : f ≠ 0) (hford : ∀ P ∈ An.dom, P.ord f = 0)
    (c : L) (hc : c • f ∈ C.integers) (hc0 : C.residue ⟨c • f, hc⟩ ≠ 0)
    (hord : x.ord (C.residue ⟨c • f, hc⟩) = 0)
    {P : Place L F} (hP : P ∈ An.dom) :
    ∃ h : P.evalAt (c • f) ∈ A, IsUnit (⟨_, h⟩ : A) := by
  obtain ⟨-, hz, -, hslope⟩ := hatt
  have hcne : c ≠ 0 := residue_ne_zero_imp_ne_zero C hc hc0
  have hford' : ∀ Q ∈ An.dom, Q.ord (c • f) = 0 := fun Q hQ => by
    rw [ord_const_smul Q hcne hf0]; exact hford Q hQ
  obtain ⟨hmem, hunit⟩ := hslope (c • f) hc hc0 hford' P hP
  have key : ∀ (s t : L), s = t → ∀ (hs : s ∈ A), IsUnit (⟨s, hs⟩ : A) →
      ∃ ht : t ∈ A, IsUnit (⟨t, ht⟩ : A) := by
    rintro s t rfl hs hu
    exact ⟨hs, hu⟩
  refine key _ _ ?_ hmem hunit
  rw [hord, neg_zero, zpow_zero, mul_one]

end EdgeLaw

section Width

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem width_pos (An : Annulus A F) (π : A) (w : ℕ) (hw : ∃ u : Aˣ, An.modulus = u * π ^ w) :
    0 < w := by
  obtain ⟨u, hu⟩ := hw
  refine Nat.pos_of_ne_zero ?_
  rintro rfl
  rw [pow_zero, mul_one] at hu
  have hmax := An.modulus_mem
  rw [hu, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmax
  exact hmax u.isUnit

end Width

section DivisorFacts

theorem mapDomain_apply_eq_zero_of_forall_ne {α β : Type*} (φ : α → β) (D : α →₀ ℤ) (b : β)
    (h : ∀ a ∈ D.support, φ a ≠ b) : Finsupp.mapDomain φ D b = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  exact Finset.sum_eq_zero fun a ha => by
    show (Finsupp.single (φ a) (D a)) b = 0
    rw [Finsupp.single_apply, if_neg (h a ha)]

end DivisorFacts

section ChartFacts

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem sum_nodes_ord_residue_eq_neg_degree [HasPrincipalDivisors (ResidueField A) Fbar]
    (hratBar : ∀ Q : Place (ResidueField A) Fbar, Q.IsRational)
    (C : ComponentChart A F Fbar) (f : F) (hf0 : f ≠ 0)
    (c : L) (hc : c • f ∈ C.integers) (hc0 : C.residue ⟨c • f, hc⟩ ≠ 0)
    (Ei : Divisor L F) (hEi : ∀ P ∈ C.dom, Ei P = P.ord f) (hEi' : ∀ P, P ∉ C.dom → Ei P = 0) :
    ∑ x ∈ C.nodes, x.ord (C.residue ⟨c • f, hc⟩) = -Finsupp.degree Ei := by
  classical
  set fbar := C.residue ⟨c • f, hc⟩ with hfbar
  have hcne : c ≠ 0 := residue_ne_zero_imp_ne_zero C hc hc0
  obtain ⟨Dbar, hDbar, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) fbar hc0
  have hM : ∀ Q, Q ∉ C.nodes → Finsupp.mapDomain C.placeMap Ei Q = Q.ord fbar :=
    C.mapDomain_placeMap ⟨c • f, hc⟩ hc0 Ei
      (fun P hP => by rw [hEi P hP]; exact (ord_const_smul P hcne hf0).symm) hEi'
  have hM0 : ∀ Q ∈ C.nodes, Finsupp.mapDomain C.placeMap Ei Q = 0 := by
    intro Q hQ
    refine mapDomain_apply_eq_zero_of_forall_ne _ _ _ fun P hP => ?_
    have hPdom : P ∈ C.dom := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hP) (hEi' P h)
    intro h
    exact C.placeMap_not_mem_nodes P hPdom (h ▸ hQ)
  have hDbar_eq : Dbar = Finsupp.mapDomain C.placeMap Ei +
      ∑ x ∈ C.nodes, Finsupp.single x (x.ord fbar) := by
    ext Q
    rw [Finsupp.add_apply, Finsupp.finsetSum_apply, hDbar Q]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    by_cases hQ : Q ∈ C.nodes
    · rw [if_pos hQ, hM0 Q hQ, zero_add]
    · rw [if_neg hQ, hM Q hQ, add_zero]
  have hdeg' : Finsupp.degree Dbar = 0 := by
    rw [← degree_eq_finsuppDegree Dbar (fun Q _ => hratBar Q)]
    exact hdeg
  rw [hDbar_eq, map_add, Finsupp.degree_mapDomain, map_sum] at hdeg'
  simp only [Finsupp.degree_single] at hdeg'
  linarith

end ChartFacts

section Reindex

theorem sum_nodes_eq_sum_ends {n m : ℕ} {ι : Fin n → Type*} (nodes : ∀ j, Finset (ι j))
    (src tgt : Fin m → Fin n) (xs : ∀ e, ι (src e)) (xt : ∀ e, ι (tgt e))
    (hxs : ∀ e, xs e ∈ nodes (src e)) (hxt : ∀ e, xt e ∈ nodes (tgt e))
    (hex : ∀ i, ∀ x ∈ nodes i, ∃ e,
      (⟨src e, xs e⟩ : Σ j, ι j) = ⟨i, x⟩ ∨ (⟨tgt e, xt e⟩ : Σ j, ι j) = ⟨i, x⟩)
    (huniq : ∀ i, ∀ x ∈ nodes i, ∀ E E' : Fin m ⊕ Fin m,
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
      Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ →
        E = E')
    (G : (Σ j, ι j) → ℤ) (i : Fin n) :
    ∑ x ∈ nodes i, G ⟨i, x⟩ =
      (∑ e ∈ Finset.univ.filter (fun e => src e = i), G ⟨src e, xs e⟩) +
        ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), G ⟨tgt e, xt e⟩ := by
  classical
  set φ : Fin m ⊕ Fin m → Σ j, ι j :=
    Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, ι j)) (fun e => ⟨tgt e, xt e⟩) with hφ
  set N : Finset (Σ j, ι j) := Finset.univ.sigma nodes with hN
  set Gi : (Σ j, ι j) → ℤ := fun σ => if σ.1 = i then G σ else 0 with hGi
  have hmaps : ∀ E ∈ (Finset.univ : Finset (Fin m ⊕ Fin m)), φ E ∈ N := by
    rintro (e | e) -
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hxs e⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hxt e⟩
  have hinj : Set.InjOn φ ↑(Finset.univ : Finset (Fin m ⊕ Fin m)) := by
    intro E hE E' _ h
    have hmem : (φ E).2 ∈ nodes (φ E).1 := (Finset.mem_sigma.mp (hmaps E hE)).2
    exact huniq (φ E).1 (φ E).2 hmem E E' rfl (by rw [← h])
  have hsurj : Set.SurjOn φ ↑(Finset.univ : Finset (Fin m ⊕ Fin m)) ↑N := by
    rintro ⟨j, x⟩ hσ
    have hx : x ∈ nodes j := (Finset.mem_sigma.mp (Finset.mem_coe.mp hσ)).2
    obtain ⟨e, h | h⟩ := hex j x hx
    · exact ⟨Sum.inl e, by simp, h⟩
    · exact ⟨Sum.inr e, by simp, h⟩
  have h1 : ∑ E, Gi (φ E) = ∑ σ ∈ N, Gi σ :=
    Finset.sum_nbij φ hmaps hinj hsurj (fun _ _ => rfl)
  have h2 : ∑ σ ∈ N, Gi σ = ∑ x ∈ nodes i, G ⟨i, x⟩ := by
    rw [hN, Finset.sum_sigma]
    rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)]
    · exact Finset.sum_congr rfl fun x _ => by simp [Gi]
    · exact Finset.sum_eq_zero fun x _ => by simp [Gi, hji]
  have h3 : ∑ E, Gi (φ E) =
      (∑ e ∈ Finset.univ.filter (fun e => src e = i), G ⟨src e, xs e⟩) +
        ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), G ⟨tgt e, xt e⟩ := by
    rw [Fintype.sum_sum_type, Finset.sum_filter, Finset.sum_filter]
    rfl
  rw [← h2, ← h1, h3]

end Reindex

end HarmonicNodesSol

open HarmonicNodesSol in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (F : Type*) [Field F] [Algebra L F]
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
    :
    ∀ f : F, f ≠ 0 → (∀ e, ∀ P ∈ (An e).dom, P.ord f = 0) →
      ∀ E : Fin n → Divisor L F, (∀ i, ∀ P ∈ (C i).dom, E i P = P.ord f) →
        (∀ i, ∀ P, P ∉ (C i).dom → E i P = 0) →
        (∀ i, Divisor.degree (E i) = 0) →
        ∃ c : Fin n → L, (∀ i, c i ≠ 0) ∧
          (∀ i, ∃ h : c i • f ∈ (C i).integers, (C i).residue ⟨c i • f, h⟩ ≠ 0 ∧
            ∀ x ∈ (C i).nodes, x.ord ((C i).residue ⟨c i • f, h⟩) = 0) ∧
          (∀ e, A.valuation (c (src e)) = A.valuation (c (tgt e))) ∧
          (∀ e, ∀ P ∈ (An e).dom, ∃ h : P.evalAt (c (src e) • f) ∈ A, IsUnit (⟨_, h⟩ : A)) := by
  intro f hf0 hford E hE hE' hdeg
  classical

  choose c hc hc0 using fun i => (C i).exists_smul_mem f hf0
  have hcne : ∀ i, c i ≠ 0 := fun i => residue_ne_zero_imp_ne_zero (C i) (hc i) (hc0 i)

  have hdegE : ∀ i, Finsupp.degree (E i) = 0 := by
    intro i
    rw [← degree_eq_finsuppDegree (E i) (fun P hP => hratF i P ?_), hdeg i]
    by_contra h
    exact (Finsupp.mem_support_iff.mp hP) (hE' i P h)

  obtain ⟨ordAt, hordAt⟩ : ∃ o : (Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) → ℤ,
      ∀ j x, o ⟨j, x⟩ = x.ord ((C j).residue ⟨c j • f, hc j⟩) :=
    ⟨fun σ => σ.2.ord ((C σ.1).residue ⟨c σ.1 • f, hc σ.1⟩), fun _ _ => rfl⟩
  have hnodesum : ∀ i, ∑ x ∈ (C i).nodes, ordAt ⟨i, x⟩ = 0 := by
    intro i
    have h := sum_nodes_ord_residue_eq_neg_degree (hratBar i) (C i) f hf0 (c i) (hc i) (hc0 i)
      (E i) (hE i) (hE' i)
    rw [hdegE i, neg_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => hordAt i x

  have hedge : ∀ e, ordAt ⟨src e, xs e⟩ + ordAt ⟨tgt e, xt e⟩ = 0 ∧
      lg A (c (tgt e)) - lg A (c (src e)) =
        ((w e : ℤ) * ordAt ⟨tgt e, xt e⟩) • lg A ((π : A) : L) := by
    intro e
    have h := edge_law π hπ hπ0 (An e) (An' e) (C (src e)) (C (tgt e)) (xs e) (xt e) (w e)
      (hpair e).1 (hpair e).2.2.2 (hw e) (hatt e).1 (hatt e).2 f hf0 (hford e)
      (c (src e)) (hc (src e)) (hc0 (src e)) (c (tgt e)) (hc (tgt e)) (hc0 (tgt e))
    rw [← hordAt (src e) (xs e), ← hordAt (tgt e) (xt e)] at h
    exact h

  have hends : ∀ i, ∑ x ∈ (C i).nodes, ordAt ⟨i, x⟩ =
      (∑ e ∈ Finset.univ.filter (fun e => src e = i), ordAt ⟨src e, xs e⟩) +
        ∑ e ∈ Finset.univ.filter (fun e => tgt e = i), ordAt ⟨tgt e, xt e⟩ := fun i =>
    sum_nodes_eq_sum_ends (fun j => (C j).nodes) src tgt xs xt (fun e => (hatt e).1.1)
      (fun e => (hatt e).2.1) hnodes.1 hnodes.2 ordAt i
  have hslope0 : ∀ e, ordAt ⟨tgt e, xt e⟩ = 0 := by
    refine WeightedMultigraph.slope_eq_zero_of_gradient_of_harmonic src tgt w
      (fun e => width_pos (An e) π (w e) (hw e)) (lg A ((π : A) : L))
      (lg_ne_zero_of_mem_maximalIdeal hπ hπ0) (fun i => lg A (c i))
      (fun e => ordAt ⟨tgt e, xt e⟩) (fun e => (hedge e).2) (fun i => ?_)
    have h1 := hnodesum i
    rw [hends i] at h1
    have h2 : ∑ e ∈ Finset.univ.filter (fun e => src e = i), ordAt ⟨src e, xs e⟩ =
        -∑ e ∈ Finset.univ.filter (fun e => src e = i), ordAt ⟨tgt e, xt e⟩ := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun e _ => by linarith [(hedge e).1]
    rw [h2] at h1
    linarith
  have hslope0' : ∀ e, ordAt ⟨src e, xs e⟩ = 0 := fun e => by
    linarith [(hedge e).1, hslope0 e]

  have hnodes0 : ∀ i, ∀ x ∈ (C i).nodes, x.ord ((C i).residue ⟨c i • f, hc i⟩) = 0 := by
    intro i x hx
    rw [← hordAt i x]
    obtain ⟨e, h | h⟩ := hnodes.1 i x hx
    · rw [← h]; exact hslope0' e
    · rw [← h]; exact hslope0 e

  refine ⟨c, hcne, fun i => ⟨hc i, hc0 i, fun x hx => hnodes0 i x hx⟩, fun e => ?_, fun e P hP => ?_⟩
  ·
    have h := (hedge e).2
    rw [hslope0 e, mul_zero, zero_smul, sub_eq_zero] at h
    exact ((lg_eq_lg_iff (hcne (tgt e)) (hcne (src e))).mp h).symm
  ·
    have hx0 : (xs e).ord ((C (src e)).residue ⟨c (src e) • f, hc (src e)⟩) = 0 := by
      rw [← hordAt]; exact hslope0' e
    exact isUnit_evalAt_of_ord_eq_zero (An e) (C (src e)) (xs e) (hatt e).1 f hf0 (hford e)
      (c (src e)) (hc (src e)) (hc0 (src e)) hx0 hP

end

end S_AlgebraicCurve_exists_forall_ord_residue_smul_eq_zero_of_forall_degree_eq_zero_of_semistableCovering
end P2MW
export P2MW.S_AlgebraicCurve_exists_forall_ord_residue_smul_eq_zero_of_forall_degree_eq_zero_of_semistableCovering (solution)
