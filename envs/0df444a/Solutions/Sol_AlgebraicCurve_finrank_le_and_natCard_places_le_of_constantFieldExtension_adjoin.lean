-- Prove2me | solution 1 for AlgebraicCurve.finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/44d00469-9cc7-55e5-894e-d696722ba769

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_linearIndependent_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped IntermediateField

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_inv HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver Place.exists_comap_algebraMap_eq_of_constantFieldExtension linearIndependent_of_constantFieldExtension Place.exists_toValuationSubring_eq_comap_ringHom Place.mem_iff_ord_nonneg"
namespace ConstantFieldAdjoin
p2m_open "AlgebraicCurve"

section Main

theorem linearIndependent_pow_of_transcendental {k A : Type*} [Field k] [Ring A] [Algebra k A]
    {Y : A} (hY : Transcendental k Y) (N : ℕ) :
    LinearIndependent k (fun n : Fin N => Y ^ (n : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha m
  have hinj := transcendental_iff_injective.mp hY
  have hpoly : Polynomial.aeval Y (∑ n : Fin N, Polynomial.monomial (n : ℕ) (a n)) = 0 := by
    rw [map_sum]
    simpa [Polynomial.aeval_monomial, Algebra.smul_def] using ha
  have hzero : (∑ n : Fin N, Polynomial.monomial (n : ℕ) (a n)) = 0 :=
    hinj (by rw [hpoly, map_zero])
  have hcoeff := congrArg (fun p : Polynomial k => p.coeff (m : ℕ)) hzero
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single m (fun n _ hn => if_neg (fun h => hn (Fin.ext h))) (by simp)] at hcoeff
  simpa using hcoeff

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
variable {F : Type*} [Field F] [Algebra k F]
variable {K' : Type*} [Field K'] [Algebra k K']
variable {L : Type*} [Field L] [Algebra K' L] (t : L) (E : IntermediateField K'⟮t⟯ L)
variable [Algebra F E] [Algebra k E] [IsScalarTower k K' E] [IsScalarTower k F E]

theorem exists_mul_aeval_eq (l : K'⟮t⟯) :
    ∃ p q : Polynomial K', Polynomial.aeval t q ≠ 0 ∧ (l : L) * Polynomial.aeval t q = Polynomial.aeval t p := by
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K' (l : L)).mp l.2
  by_cases hs : Polynomial.aeval t s = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [hrs, hs, div_zero, zero_mul, map_zero]
  · refine ⟨r, s, hs, ?_⟩
    rw [hrs, div_mul_cancel₀ _ hs]

set_option maxHeartbeats 1600000 in

theorem finrank_le_finrank (y : F) (hy : Transcendental k y) [FiniteDimensional k⟮y⟯ F]
    (hyt : (algebraMap F E y : L) = t)
    (hfg' : ∃ x : E, Transcendental K' x ∧ FiniteDimensional K'⟮x⟯ E)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤)
    [FiniteDimensional K'⟮t⟯ E] :
    Module.finrank k⟮y⟯ F ≤ Module.finrank K'⟮t⟯ E := by
  classical
  set d := Module.finrank k⟮y⟯ F with hd
  let b := Module.finBasisOfFinrankEq k⟮y⟯ F hd.symm

  suffices hli : LinearIndependent K'⟮t⟯ (fun i : Fin d => algebraMap F E (b i)) by
    simpa using hli.fintype_card_le_finrank
  rw [Fintype.linearIndependent_iff]
  intro l hl

  have hpq : ∀ i, ∃ p q : Polynomial K', Polynomial.aeval t q ≠ 0 ∧
      ((l i : K'⟮t⟯) : L) * Polynomial.aeval t q = Polynomial.aeval t p := fun i => exists_mul_aeval_eq t (l i)
  choose p q hq hpq using hpq
  set Q : Polynomial K' := ∏ i, q i with hQ
  have hQ0 : Polynomial.aeval t Q ≠ 0 := by
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hq i
  let P : Fin d → Polynomial K' := fun i => p i * ∏ j ∈ Finset.univ.erase i, q j
  have hP : ∀ i, ((l i : K'⟮t⟯) : L) * Polynomial.aeval t Q = Polynomial.aeval t (P i) := by
    intro i
    rw [hQ, ← Finset.mul_prod_erase Finset.univ q (Finset.mem_univ i), map_mul, ← mul_assoc, hpq i,
      ← map_mul]

  have hrelL : ∑ i, ((l i : K'⟮t⟯) : L) * (algebraMap F E (b i) : L) = 0 := by
    have := congrArg (fun e : E => (e : L)) hl
    simpa [IntermediateField.smul_def, smul_eq_mul] using this
  have hrelQ : ∑ i, Polynomial.aeval t (P i) * (algebraMap F E (b i) : L) = 0 := by
    have := congrArg (fun z : L => Polynomial.aeval t Q * z) hrelL
    simp only [mul_zero, Finset.mul_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hP i]; ring

  set N : ℕ := (Finset.univ.sup fun i => (P i).natDegree) + 1 with hN
  have hdeg : ∀ i, (P i).natDegree < N := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (P i).natDegree) (Finset.mem_univ i))

  have htn : ∀ n : ℕ, ((algebraMap F E (y ^ n) : E) : L) = t ^ n := by
    intro n
    rw [map_pow]
    push_cast
    rw [hyt]
  have hrel2 : ∑ pr : Fin N × Fin d,
      (P pr.2).coeff (pr.1 : ℕ) • ((algebraMap F E (y ^ (pr.1 : ℕ) * b pr.2) : E) : L) = 0 := by
    rw [← hrelQ, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.aeval_eq_sum_range' (hdeg i), Finset.sum_mul, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, MulMemClass.coe_mul, htn, smul_mul_assoc]

  let Y : k⟮y⟯ := ⟨y, IntermediateField.mem_adjoin_simple_self k y⟩
  have hYt : Transcendental k Y := by
    have hinj : Function.Injective (algebraMap k⟮y⟯ F) := (algebraMap k⟮y⟯ F).injective
    rw [← transcendental_algebraMap_iff hinj]
    exact hy
  have hli1 : LinearIndependent k (fun pr : Fin N × Fin d => (Y ^ (pr.1 : ℕ)) • b pr.2) :=
    linearIndependent_smul (linearIndependent_pow_of_transcendental hYt N) b.linearIndependent
  have hfam : (fun pr : Fin N × Fin d => y ^ (pr.1 : ℕ) * b pr.2) =
      (fun pr : Fin N × Fin d => (Y ^ (pr.1 : ℕ)) • b pr.2) := by
    funext pr
    rw [IntermediateField.smul_def]
    rfl
  have hLD := AlgebraicCurve.linearIndependent_of_constantFieldExtension k F K' E
    ⟨y, hy, inferInstance⟩ hfg' hgen (b := fun pr : Fin N × Fin d => y ^ (pr.1 : ℕ) * b pr.2)
    (by rw [hfam]; exact hli1)
  have hLD' : LinearIndependent K'
      (fun pr : Fin N × Fin d => ((algebraMap F E (y ^ (pr.1 : ℕ) * b pr.2) : E) : L)) :=
    hLD.map' ((E.val.restrictScalars K').toLinearMap)
      (LinearMap.ker_eq_bot.mpr fun a b h => Subtype.ext h)
  have hcoeff : ∀ pr : Fin N × Fin d, (P pr.2).coeff (pr.1 : ℕ) = 0 :=
    Fintype.linearIndependent_iff.mp hLD' _ hrel2

  intro i
  have hPi : P i = 0 := by
    ext n
    rw [Polynomial.coeff_zero]
    rcases lt_or_ge n N with hn | hn
    · exact hcoeff (⟨n, hn⟩, i)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i) hn)
  have := hP i
  rw [hPi, map_zero, mul_eq_zero] at this
  rcases this with h | h
  · exact_mod_cast h
  · exact absurd h hQ0

theorem natCard_places_le (y : F) (hy : Transcendental k y) [FiniteDimensional k⟮y⟯ F]
    [AlgebraicCurve.IsCurveOver k F]
    (hfg' : ∃ x : E, Transcendental K' x ∧ FiniteDimensional K'⟮x⟯ E)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤)
    (u : F) (hu : u ≠ 0) :
    (Finite {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ∧
      Nat.card {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ≤
        Nat.card {P : AlgebraicCurve.Place k F // 0 < P.ord u}) ∧
      (Finite {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ∧
      Nat.card {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ≤
        Nat.card {P : AlgebraicCurve.Place k F // P.ord u < 0}) := by
  classical
  have hu' : algebraMap F E u ≠ 0 := (map_ne_zero _).mpr hu

  have hcomap : ∀ P : AlgebraicCurve.Place K' E, P.ord (algebraMap F E u) ≠ 0 →
      ∃ v : AlgebraicCurve.Place k F,
        v.toValuationSubring = P.toValuationSubring.comap (algebraMap F E) := by
    intro P hP
    refine AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom (K := k) y (algebraMap F E)
      P.toValuationSubring (fun a => ?_) ?_
    · rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k K' E]
      exact P.algebraMap_mem' _
    · rcases lt_or_gt_of_ne hP with h | h
      · exact ⟨u, fun hmem => by
          have := (AlgebraicCurve.Place.mem_iff_ord_nonneg P hu').mp hmem; omega⟩
      · refine ⟨u⁻¹, fun hmem => ?_⟩
        rw [map_inv₀] at hmem
        have := (AlgebraicCurve.Place.mem_iff_ord_nonneg P (inv_ne_zero hu')).mp hmem
        rw [AlgebraicCurve.Place.ord_inv] at this
        omega

  have huniq : ∀ (v : AlgebraicCurve.Place k F) (P₁ P₂ : AlgebraicCurve.Place K' E),
      P₁.toValuationSubring.comap (algebraMap F E) = v.toValuationSubring →
      P₂.toValuationSubring.comap (algebraMap F E) = v.toValuationSubring → P₁ = P₂ := by
    intro v P₁ P₂ h₁ h₂
    obtain ⟨P', -, -, hP'⟩ :=
      AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension k F K' E
        ⟨y, hy, inferInstance⟩ hfg' hgen v
    rw [hP' P₁ h₁, hP' P₂ h₂]

  have hsign_pos : ∀ (P : AlgebraicCurve.Place K' E) (v : AlgebraicCurve.Place k F),
      v.toValuationSubring = P.toValuationSubring.comap (algebraMap F E) →
      (0 < P.ord (algebraMap F E u) ↔ 0 < v.ord u) := by
    intro P v hv
    have h1 : algebraMap F E u ∈ P.toValuationSubring ↔ u ∈ v.toValuationSubring := by
      rw [hv, ValuationSubring.mem_comap]
    have h2 : (algebraMap F E u)⁻¹ ∈ P.toValuationSubring ↔ u⁻¹ ∈ v.toValuationSubring := by
      rw [hv, ValuationSubring.mem_comap, map_inv₀]
    rw [AlgebraicCurve.Place.mem_iff_ord_nonneg P hu', AlgebraicCurve.Place.mem_iff_ord_nonneg v hu] at h1
    rw [AlgebraicCurve.Place.mem_iff_ord_nonneg P (inv_ne_zero hu'),
      AlgebraicCurve.Place.mem_iff_ord_nonneg v (inv_ne_zero hu),
      AlgebraicCurve.Place.ord_inv, AlgebraicCurve.Place.ord_inv] at h2
    constructor
    · intro h; by_contra h'; have := h2.mpr (by omega); omega
    · intro h; by_contra h'; have := h2.mp (by omega); omega
  have hsign_neg : ∀ (P : AlgebraicCurve.Place K' E) (v : AlgebraicCurve.Place k F),
      v.toValuationSubring = P.toValuationSubring.comap (algebraMap F E) →
      (P.ord (algebraMap F E u) < 0 ↔ v.ord u < 0) := by
    intro P v hv
    have h1 : algebraMap F E u ∈ P.toValuationSubring ↔ u ∈ v.toValuationSubring := by
      rw [hv, ValuationSubring.mem_comap]
    rw [AlgebraicCurve.Place.mem_iff_ord_nonneg P hu', AlgebraicCurve.Place.mem_iff_ord_nonneg v hu] at h1
    constructor
    · intro h; by_contra h'; have := h1.mpr (by omega); omega
    · intro h; by_contra h'; have := h1.mp (by omega); omega

  obtain ⟨D, hD, -⟩ := AlgebraicCurve.HasPrincipalDivisors.exists_divisor (K := k) u hu
  have hfin_pos : Finite {P : AlgebraicCurve.Place k F // 0 < P.ord u} := by
    apply Finite.of_injective (fun P => (⟨P.1, by
      rw [Finsupp.mem_support_iff, hD]; exact P.2.ne'⟩ : D.support))
    intro P₁ P₂ h; exact Subtype.ext (congrArg (fun z : D.support => (z : AlgebraicCurve.Place k F)) h)
  have hfin_neg : Finite {P : AlgebraicCurve.Place k F // P.ord u < 0} := by
    apply Finite.of_injective (fun P => (⟨P.1, by
      rw [Finsupp.mem_support_iff, hD]; exact P.2.ne⟩ : D.support))
    intro P₁ P₂ h; exact Subtype.ext (congrArg (fun z : D.support => (z : AlgebraicCurve.Place k F)) h)
  constructor
  · let f : {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} →
        {P : AlgebraicCurve.Place k F // 0 < P.ord u} := fun P =>
      ⟨(hcomap P.1 P.2.ne').choose,
        (hsign_pos P.1 _ (hcomap P.1 P.2.ne').choose_spec).mp P.2⟩
    suffices hf : Function.Injective f from
      ⟨Finite.of_injective f hf, Nat.card_le_card_of_injective f hf⟩
    intro P₁ P₂ h
    apply Subtype.ext
    have h' := congrArg (fun z : {P : AlgebraicCurve.Place k F // 0 < P.ord u} => z.1) h
    exact huniq _ P₁.1 P₂.1 (hcomap P₁.1 P₁.2.ne').choose_spec.symm
      (by rw [show (hcomap P₁.1 P₁.2.ne').choose = (hcomap P₂.1 P₂.2.ne').choose from h']
          exact (hcomap P₂.1 P₂.2.ne').choose_spec.symm)
  · let f : {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} →
        {P : AlgebraicCurve.Place k F // P.ord u < 0} := fun P =>
      ⟨(hcomap P.1 P.2.ne).choose,
        (hsign_neg P.1 _ (hcomap P.1 P.2.ne).choose_spec).mp P.2⟩
    suffices hf : Function.Injective f from
      ⟨Finite.of_injective f hf, Nat.card_le_card_of_injective f hf⟩
    intro P₁ P₂ h
    apply Subtype.ext
    have h' := congrArg (fun z : {P : AlgebraicCurve.Place k F // P.ord u < 0} => z.1) h
    exact huniq _ P₁.1 P₂.1 (hcomap P₁.1 P₁.2.ne).choose_spec.symm
      (by rw [show (hcomap P₁.1 P₁.2.ne).choose = (hcomap P₂.1 P₂.2.ne).choose from h']
          exact (hcomap P₂.1 P₂.2.ne).choose_spec.symm)

omit [IsAlgClosed k] [CharZero k] in

theorem finiteDimensional_adjoin_of_coe_eq [FiniteDimensional K'⟮t⟯ E] (x : E) (hx : (x : L) = t) :
    FiniteDimensional K'⟮x⟯ E := by
  let f : E →ₐ[K'] L := E.val.restrictScalars K'
  have hmap : (K'⟮x⟯).map f = K'⟮t⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    congr 1
    rw [Set.singleton_eq_singleton_iff]
    exact hx
  let e : K'⟮x⟯ ≃ₐ[K'] K'⟮t⟯ := (IntermediateField.equivMap K'⟮x⟯ f).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ z : K'⟮x⟯, ((e z : K'⟮t⟯) : L) = ((z : E) : L) := fun z => rfl
  refine Module.Finite.of_equiv_equiv (A₁ := K'⟮t⟯) (B₁ := E) (A₂ := K'⟮x⟯) (B₂ := E)
    e.symm.toRingEquiv (RingEquiv.refl E) ?_
  refine RingHom.ext fun l => Subtype.ext ?_
  change (((e.symm l : K'⟮x⟯) : E) : L) = ((algebraMap K'⟮t⟯ E l : E) : L)
  rw [← he (e.symm l), AlgEquiv.apply_symm_apply]
  rfl

theorem adjoin_adjoin_subset {K' : Type*} [Field K'] {L : Type*} [Field L] [Algebra K' L] (S : Set L) (t : L)
    (ht : t ∈ IntermediateField.adjoin K' S) :
    ((IntermediateField.adjoin K'⟮t⟯ S : IntermediateField K'⟮t⟯ L) : Set L) ⊆
      ((IntermediateField.adjoin K' S : IntermediateField K' L) : Set L) := by
  have h1 : ((IntermediateField.adjoin K'⟮t⟯ S : IntermediateField K'⟮t⟯ L) : Set L) =
      (IntermediateField.restrictScalars K' (IntermediateField.adjoin K'⟮t⟯ S) : Set L) := rfl
  rw [h1, IntermediateField.restrictScalars_adjoin]
  have hle : IntermediateField.adjoin K' ((K'⟮t⟯ : Set L) ∪ S) ≤ IntermediateField.adjoin K' S := by
    rw [IntermediateField.adjoin_le_iff]
    apply Set.union_subset
    · have : K'⟮t⟯ ≤ IntermediateField.adjoin K' S := IntermediateField.adjoin_simple_le_iff.mpr ht
      exact SetLike.coe_subset_coe.mpr this
    · exact IntermediateField.subset_adjoin _ _
  exact SetLike.coe_subset_coe.mpr hle

omit [IsAlgClosed k] [CharZero k] in

theorem adjoin_range_eq_top
    (hEle : (E : Set L) ⊆
      ((IntermediateField.adjoin K' (Set.range fun u : F => (algebraMap F E u : L)) :
        IntermediateField K' L) : Set L)) :
    IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤ := by
  let f : E →ₐ[K'] L := E.val.restrictScalars K'
  set A := IntermediateField.adjoin K' (Set.range (algebraMap F E)) with hA
  have hmapA : A.map f = IntermediateField.adjoin K' (Set.range fun u : F => (algebraMap F E u : L)) := by
    rw [hA, IntermediateField.adjoin_map, ← Set.range_comp]
    rfl
  rw [eq_top_iff]
  intro e _
  have he : (e : L) ∈ A.map f := by
    rw [hmapA]; exact hEle e.2
  obtain ⟨a, ha, hae⟩ := (IntermediateField.mem_map A).mp he
  have : a = e := Subtype.ext hae
  rw [← this]; exact ha

end Main

end AlgebraicCurve.ConstantFieldAdjoin

end

open scoped IntermediateField in
theorem solution
    {k : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    {F : Type*} [Field F] [Algebra k F] [AlgebraicCurve.IsCurveOver k F]
    (y : F) (hy : Transcendental k y)
    [FiniteDimensional (IntermediateField.adjoin k ({y} : Set F)) F]
    {K' : Type*} [Field K'] [Algebra k K']
    {L : Type*} [Field L] [Algebra K' L] (t : L) (ht : Transcendental K' t)
    (E : IntermediateField (IntermediateField.adjoin K' ({t} : Set L)) L)
    [FiniteDimensional (IntermediateField.adjoin K' ({t} : Set L)) E]
    [Algebra F E] [Algebra k E] [IsScalarTower k K' E] [IsScalarTower k F E]
    (hyt : (algebraMap F E y : L) = t)
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F E)) = ⊤) :
    Module.finrank (IntermediateField.adjoin k ({y} : Set F)) F ≤
        Module.finrank (IntermediateField.adjoin K' ({t} : Set L)) E ∧
      ∀ u : F, u ≠ 0 →
        (Finite {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // 0 < P.ord (algebraMap F E u)} ≤
            Nat.card {P : AlgebraicCurve.Place k F // 0 < P.ord u}) ∧
        (Finite {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ∧
          Nat.card {P : AlgebraicCurve.Place K' E // P.ord (algebraMap F E u) < 0} ≤
            Nat.card {P : AlgebraicCurve.Place k F // P.ord u < 0}) := by

  have hx : Transcendental K' (algebraMap F E y) := by
    haveI : IsScalarTower K' E L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    rw [← transcendental_algebraMap_iff (R := K') (A := L) (algebraMap E L).injective]
    change Transcendental K' ((algebraMap F E y : E) : L)
    rw [hyt]
    exact ht
  have hfg' : ∃ x : E, Transcendental K' x ∧ FiniteDimensional K'⟮x⟯ E :=
    ⟨algebraMap F E y, hx,
      AlgebraicCurve.ConstantFieldAdjoin.finiteDimensional_adjoin_of_coe_eq t E _ hyt⟩
  exact ⟨AlgebraicCurve.ConstantFieldAdjoin.finrank_le_finrank t E y hy hyt hfg' hgen,
    fun u hu => AlgebraicCurve.ConstantFieldAdjoin.natCard_places_le t E y hy hfg' hgen u hu⟩

end S_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin
end P2MW
export P2MW.S_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin (solution)
