-- Prove2me | solution 1 for AlgebraicCurve.finite_and_card_torsion_le_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c7a6eeb5-a623-58d5-9c21-4152197687d9

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_exists_D_ne_zero
import Theorems.Thm_AlgebraicCurve_CartierB_linearIndependent_of_cartier_fixed
import Theorems.Thm_AlgebraicCurve_pDigits_existsUnique
import Theorems.Thm_AlgebraicCurve_cartierOperator_existsUnique
import Theorems.Thm_AlgebraicCurve_isRegularDiff_dlog_of_dvd_ord
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finite_and_card_torsion_le_pow_finrank
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place Divisor Divisor.degZero Divisor.principal Pic0 Pic0.mk Pic0.mk_surjective Pic0.torsion Pic0.mem_torsion regularDiffs mem_regularDiffs_of_isRegularDiff exists_D_ne_zero CartierB.linearIndependent_of_cartier_fixed pDigits_existsUnique cartierOperator_existsUnique isRegularDiff_dlog_of_dvd_ord"
p2m_open "AlgebraicCurve"

namespace PayoffDev

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem charP_F (p : ℕ) [CharP K p] : CharP F p :=
  charP_of_injective_algebraMap (algebraMap K F).injective p

private theorem nsmul_eq_cast_smul {M : Type*} [AddCommGroup M] [Module F M] (n : ℕ) (ω : M) :
    n • ω = (n : F) • ω := (Nat.cast_smul_eq_nsmul F n ω).symm

private theorem pkill (p : ℕ) [Fact p.Prime] [CharP K p] {M : Type*} [AddCommGroup M]
    [Module F M] (ω : M) : p • ω = 0 := by
  haveI : CharP F p := charP_F (K := K) p
  rw [nsmul_eq_cast_smul (F := F), CharP.cast_eq_zero F p, zero_smul]

private theorem D_pow_char (p : ℕ) [Fact p.Prime] [CharP K p] (a : F) :
    D K F (a ^ p) = 0 := by
  rw [Derivation.leibniz_pow, pkill (K := K) (F := F) (M := Ω[F⁄K]) p]

private theorem natCast_pow_char (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ) :
    ((m : F)) ^ p = (m : F) := by
  haveI : CharP F p := charP_F (K := K) p
  induction m with
  | zero => rw [Nat.cast_zero, zero_pow (Fact.out : p.Prime).pos.ne']
  | succ k ih => rw [Nat.cast_succ, add_pow_char, ih, one_pow]

private theorem dlog_mul {g h : F} (hg : g ≠ 0) (hh : h ≠ 0) :
    (g * h)⁻¹ • D K F (g * h) = g⁻¹ • D K F g + h⁻¹ • D K F h := by
  rw [Derivation.leibniz, smul_add, mul_inv_rev, smul_smul, smul_smul]
  have e1 : h⁻¹ * g⁻¹ * g = h⁻¹ := by
    rw [mul_assoc, inv_mul_cancel₀ hg, mul_one]
  have e2 : h⁻¹ * g⁻¹ * h = g⁻¹ := by
    rw [mul_comm h⁻¹ g⁻¹, mul_assoc, inv_mul_cancel₀ hh, mul_one]
  rw [e1, e2, add_comm]

private theorem dlog_inv {g : F} (hg : g ≠ 0) :
    (g⁻¹)⁻¹ • D K F g⁻¹ = -(g⁻¹ • D K F g) := by
  have h1 : D K F (g * g⁻¹) = 0 := by
    rw [mul_inv_cancel₀ hg, Derivation.map_one_eq_zero]
  rw [Derivation.leibniz] at h1
  rw [inv_inv]
  exact eq_neg_of_add_eq_zero_left h1

private theorem dlog_fixed (p : ℕ) [Fact p.Prime] (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (η : Ω[F⁄K]), C (f ^ p • η) = f • C η)
    (hdlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f) (g : F) :
    C (g⁻¹ • D K F g) = g⁻¹ • D K F g := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 :=
    ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  have hq0 : q ≠ 0 := by have := (Fact.out : (q + 1).Prime).one_lt; omega
  simp only [Nat.add_sub_cancel] at hdlog
  have hgp : g⁻¹ ^ (q + 1) * g ^ q = g⁻¹ := by
    rcases eq_or_ne g 0 with rfl | hg
    · rw [inv_zero, zero_pow hq0, mul_zero]
    · have h1 : g⁻¹ ^ q * g ^ q = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hg, one_pow]
      calc g⁻¹ ^ (q + 1) * g ^ q = g⁻¹ * (g⁻¹ ^ q * g ^ q) := by ring
        _ = g⁻¹ := by rw [h1, mul_one]
  have key : g⁻¹ • D K F g = g⁻¹ ^ (q + 1) • (g ^ q • D K F g) := by
    rw [smul_smul, hgp]
  rw [key, hsemi, hdlog, ← key]

private theorem exists_pow_eq_of_D_eq_zero [IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {r : F} (hr : D K F r = 0) : ∃ s : F, r = s ^ p := by
  haveI : CharP F p := charP_F (K := K) p
  obtain ⟨t, hdt⟩ := exists_D_ne_zero (K := K) (F := F)
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 :=
    ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  subst hq
  obtain ⟨a, ha, hau⟩ := pDigits_existsUnique (q + 1) x hdt r

  have hDr : (∑ i : Fin (q + 1), a i ^ (q + 1) * ((i : ℕ) : F) * t ^ ((i : ℕ) - 1)) • D K F t
      = 0 := by
    have e1 : ∀ i : Fin (q + 1), D K F (a i ^ (q + 1) * t ^ (i : ℕ))
        = (a i ^ (q + 1) * ((i : ℕ) : F) * t ^ ((i : ℕ) - 1)) • D K F t := by
      intro i
      rw [Derivation.leibniz, D_pow_char (q + 1), smul_zero, add_zero,
        Derivation.leibniz_pow, nsmul_eq_cast_smul (F := F), smul_smul, smul_smul]
    calc (∑ i : Fin (q + 1), a i ^ (q + 1) * ((i : ℕ) : F) * t ^ ((i : ℕ) - 1)) • D K F t
        = ∑ i : Fin (q + 1), D K F (a i ^ (q + 1) * t ^ (i : ℕ)) := by
          rw [Finset.sum_smul]
          exact Finset.sum_congr rfl fun i _ => (e1 i).symm
      _ = D K F r := by rw [← map_sum, ← ha]
      _ = 0 := hr
  have hc0 : (∑ i : Fin (q + 1), a i ^ (q + 1) * ((i : ℕ) : F) * t ^ ((i : ℕ) - 1)) = 0 := by
    by_contra hc
    apply hdt
    have h2 := congrArg
      (fun ω => (∑ i : Fin (q + 1), a i ^ (q + 1) * ((i : ℕ) : F) * t ^ ((i : ℕ) - 1))⁻¹ • ω) hDr
    simpa [smul_smul, inv_mul_cancel₀ hc] using h2

  set b : Fin (q + 1) → F :=
    Fin.snoc (fun j : Fin q => (((j : ℕ) + 1 : ℕ) : F) * a j.succ) 0 with hb
  have hbexp : (0 : F) = ∑ i : Fin (q + 1), b i ^ (q + 1) * t ^ (i : ℕ) := by
    have e2 : ∑ i : Fin (q + 1), b i ^ (q + 1) * t ^ (i : ℕ)
        = ∑ j : Fin q, ((((j : ℕ) + 1 : ℕ) : F) * a j.succ) ^ (q + 1) * t ^ (j : ℕ) := by
      rw [Fin.sum_univ_castSucc]
      simp only [hb, Fin.snoc_castSucc, Fin.snoc_last]
      rw [zero_pow (Fact.out : (q + 1).Prime).pos.ne', zero_mul, add_zero]
      exact Finset.sum_congr rfl fun j _ => by rw [Fin.val_castSucc]
    have e3 : ∑ i : Fin (q + 1), a i ^ (q + 1) * ((i : ℕ) : F) * t ^ ((i : ℕ) - 1)
        = ∑ j : Fin q, ((((j : ℕ) + 1 : ℕ) : F) * a j.succ) ^ (q + 1) * t ^ (j : ℕ) := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hjv : ((j.succ : ℕ) : F) = (((j : ℕ) + 1 : ℕ) : F) := by
        rw [Fin.val_succ]
      have hjs : ((j.succ : ℕ)) - 1 = (j : ℕ) := by
        rw [Fin.val_succ]
        omega
      rw [hjv, hjs, mul_pow, natCast_pow_char (K := K) (q + 1)]
      ring
    rw [e2, ← e3, hc0]
  have hzexp : (0 : F) = ∑ i : Fin (q + 1), (0 : F) ^ (q + 1) * t ^ (i : ℕ) := by
    simp [zero_pow (Fact.out : (q + 1).Prime).pos.ne']
  have hbz : b = fun _ : Fin (q + 1) => (0 : F) := by
    obtain ⟨c, hc, hcu⟩ := pDigits_existsUnique (q + 1) x hdt (0 : F)
    rw [hcu b hbexp, hcu (fun _ => (0 : F)) hzexp]

  have hah : ∀ j : Fin q, a j.succ = 0 := by
    intro j
    have h3 : (((j : ℕ) + 1 : ℕ) : F) * a j.succ = 0 := by
      have := congrFun hbz (Fin.castSucc j)
      simpa [hb, Fin.snoc_castSucc] using this
    have h4 : (((j : ℕ) + 1 : ℕ) : F) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff F (q + 1)]
      intro hdvd
      have hle := Nat.le_of_dvd (Nat.succ_pos _) hdvd
      have hlt : (j : ℕ) + 1 < q + 1 := Nat.succ_lt_succ j.isLt
      omega
    exact (mul_eq_zero.mp h3).resolve_left h4
  refine ⟨a 0, ?_⟩
  rw [ha, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one]
  rw [Finset.sum_eq_zero fun j _ => by
    rw [hah j, zero_pow (Fact.out : (q + 1).Prime).pos.ne', zero_mul]]
  rw [add_zero]

private theorem nsmul_mod {M : Type*} [AddCommGroup M] (p : ℕ) (hkill : ∀ ω : M, p • ω = 0)
    (n : ℕ) (ω : M) : n • ω = (n % p) • ω := by
  conv_lhs => rw [← Nat.div_add_mod n p]
  rw [add_nsmul, mul_comm, mul_nsmul, hkill, zero_add]

private theorem neg_eq_pred_nsmul {M : Type*} [AddCommGroup M] (p : ℕ) (hp : 0 < p)
    (hkill : ∀ ω : M, p • ω = 0) (ω : M) : -ω = (p - 1) • ω := by
  have h1 : (p - 1) • ω + ω = 0 := by
    have h2 : (p - 1) • ω + 1 • ω = p • ω := by
      rw [← add_nsmul, Nat.sub_add_cancel hp]
    rw [one_nsmul] at h2
    rw [h2, hkill]
  exact (eq_neg_of_add_eq_zero_left h1).symm

private theorem finite_and_card_le_of_rawIndep_le {M : Type*} [AddCommGroup M]
    (p n : ℕ) (hp : p.Prime) (hkill : ∀ ω : M, p • ω = 0) (S : Set M)
    (hind : ∀ (m : ℕ) (w : Fin m → M), (∀ i, w i ∈ S) →
      (∀ c : Fin m → ℕ, (∑ i, c i • w i) = 0 → ∀ i, p ∣ c i) → m ≤ n) :
    S.Finite ∧ Nat.card S ≤ p ^ n := by
  classical
  set P : ℕ → Prop := fun m => ∃ w : Fin m → M, (∀ i, w i ∈ S) ∧
    (∀ c : Fin m → ℕ, (∑ i, c i • w i) = 0 → ∀ i, p ∣ c i) with hP
  have hP0 : P 0 := ⟨fun i => i.elim0, fun i => i.elim0, fun c _ i => i.elim0⟩
  have hPle : ∀ m, P m → m ≤ n := fun m ⟨w, hw, hraw⟩ => hind m w hw hraw
  set m0 : ℕ := Nat.findGreatest P n with hm0
  have hPm0 : P m0 := Nat.findGreatest_spec (Nat.zero_le n) hP0
  obtain ⟨w, hwS, hwraw⟩ := hPm0

  have hspan : ∀ s ∈ S, ∃ e : Fin m0 → Fin p, s = ∑ i, (e i : ℕ) • w i := by
    intro s hs
    by_contra hnot

    have hPsucc : P (m0 + 1) := by
      refine ⟨Fin.snoc w s, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · rw [Fin.snoc_last]; exact hs
        · intro j; rw [Fin.snoc_castSucc]; exact hwS j
      · intro c hc
        have hsum : (∑ j : Fin m0, c (Fin.castSucc j) • w j) + c (Fin.last m0) • s = 0 := by
          rw [← hc, Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
        by_cases hlast : p ∣ c (Fin.last m0)
        ·
          have hkillLast : c (Fin.last m0) • s = 0 := by
            obtain ⟨k, hk⟩ := hlast
            rw [hk, mul_comm, mul_nsmul, hkill]
          rw [hkillLast, add_zero] at hsum
          have hdvd := hwraw (fun j => c (Fin.castSucc j)) hsum
          intro i
          refine Fin.lastCases hlast (fun j => hdvd j) i
        ·
          exfalso
          apply hnot
          obtain ⟨d, hd⟩ : ∃ d : ℕ, (c (Fin.last m0) * d) % p = 1 := by
            haveI : Fact p.Prime := ⟨hp⟩
            refine ⟨c (Fin.last m0) ^ (p - 2), ?_⟩
            have hz : ((c (Fin.last m0) : ZMod p)) ≠ 0 := by
              rw [Ne, ZMod.natCast_eq_zero_iff]
              exact hlast
            have hfl : (c (Fin.last m0) : ZMod p) ^ (p - 1) = 1 :=
              ZMod.pow_card_sub_one_eq_one hz
            have hcast : ((c (Fin.last m0) * c (Fin.last m0) ^ (p - 2) : ℕ) : ZMod p)
                = ((1 : ℕ) : ZMod p) := by
              push_cast
              have h2 : p - 1 = (p - 2) + 1 := by
                have := hp.two_le
                omega
              rw [← hfl, h2, pow_succ, mul_comm]
            have h3 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcast
            rwa [Nat.mod_eq_of_lt hp.one_lt] at h3
          have hs2 : (c (Fin.last m0) * d) • s = s := by
            rw [nsmul_mod p hkill, hd, one_nsmul]
          have hcls : c (Fin.last m0) • s
              = -(∑ j : Fin m0, c (Fin.castSucc j) • w j) :=
            eq_neg_of_add_eq_zero_right hsum
          have hs3 : s = (d * (p - 1)) • (∑ j : Fin m0, c (Fin.castSucc j) • w j) := by
            calc s = (c (Fin.last m0) * d) • s := hs2.symm
              _ = (d * c (Fin.last m0)) • s := by rw [mul_comm]
              _ = d • (c (Fin.last m0) • s) := mul_smul d (c (Fin.last m0)) s
              _ = d • (-(∑ j : Fin m0, c (Fin.castSucc j) • w j)) := by rw [hcls]
              _ = d • ((p - 1) • (∑ j : Fin m0, c (Fin.castSucc j) • w j)) := by
                    rw [← neg_eq_pred_nsmul p hp.pos hkill]
              _ = (d * (p - 1)) • (∑ j : Fin m0, c (Fin.castSucc j) • w j) :=
                    (mul_smul d (p - 1) _).symm
          refine ⟨fun j => ⟨(d * (p - 1) * c (Fin.castSucc j)) % p,
            Nat.mod_lt _ hp.pos⟩, ?_⟩
          rw [hs3, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_smul, nsmul_mod p hkill]
    have hle : m0 + 1 ≤ n := hPle _ hPsucc
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self m0) hle hPsucc

  have hcoord : ∀ s : ↥S, ∃ e : Fin m0 → Fin p, (s : M) = ∑ i, (e i : ℕ) • w i :=
    fun s => hspan s.1 s.2
  choose f hf using hcoord
  have hfinj : Function.Injective f := by
    intro s s' hss
    apply Subtype.ext
    rw [hf s, hss, ← hf s']
  haveI hfinS : Finite ↥S := Finite.of_injective f hfinj
  refine ⟨Set.finite_coe_iff.mp hfinS, ?_⟩
  calc Nat.card S ≤ Nat.card (Fin m0 → Fin p) := Nat.card_le_card_of_injective f hfinj
    _ = p ^ m0 := by simp [Nat.card_eq_fintype_card]
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.pos (hPle _ ⟨w, hwS, hwraw⟩)

variable (K F) in

private def dlogSet (p : ℕ) : Set Ω[F⁄K] :=
  {ω | ∃ g : F, g ≠ 0 ∧ (∀ v : Place K F, (p : ℤ) ∣ v.ord g) ∧ ω = g⁻¹ • D K F g}

private theorem finite_and_card_torsion_le_pow_finrank_X [IsCurveOver K F] (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectField K]
    [FiniteDimensional K (regularDiffs K F)]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (η : Ω[F⁄K]), C (f ^ p • η) = f • C η)
    (hdlog : ∀ f : F, C (f ^ (p - 1) • D K F f) = D K F f) :
    Finite (Pic0.torsion K F p) ∧
      Nat.card (Pic0.torsion K F p) ≤ p ^ Module.finrank K (regularDiffs K F) := by
  haveI : CharP F p := charP_F (K := K) p
  classical

  have hScard : (dlogSet K F p).Finite ∧
      Nat.card (dlogSet K F p) ≤ p ^ Module.finrank K (regularDiffs K F) := by
    refine finite_and_card_le_of_rawIndep_le p _ Fact.out
      (pkill (K := K) (F := F) (M := Ω[F⁄K]) p) _ ?_
    intro m w hwS hraw
    have hfix : ∀ i, C (w i) = w i := by
      intro i
      obtain ⟨g, hg0, hdvd, hwi⟩ := hwS i
      rw [hwi]
      exact dlog_fixed p C hsemi hdlog g
    have hLI : LinearIndependent K w :=
      CartierB.linearIndependent_of_cartier_fixed p C hsemi hfix hraw
    have hmem : ∀ i, w i ∈ regularDiffs K F := by
      intro i
      obtain ⟨g, hg0, hdvd, hwi⟩ := hwS i
      rw [hwi]
      exact mem_regularDiffs_of_isRegularDiff (isRegularDiff_dlog_of_dvd_ord p x hdvd)
    have hLI' : LinearIndependent K
        (fun i => (⟨w i, hmem i⟩ : regularDiffs K F)) := by
      apply LinearIndependent.of_comp (regularDiffs K F).subtype
      exact hLI
    simpa using hLI'.fintype_card_le_finrank

  have hchoice : ∀ c : Pic0.torsion K F p, ∃ g : F, g ≠ 0 ∧
      (∀ v : Place K F, (p : ℤ) ∣ v.ord g) ∧
      ∃ Dd : Divisor.degZero (K := K) (F := F), Pic0.mk Dd = (c : Pic0 K F) ∧
        ∀ v : Place K F, v.ord g = (p : ℤ) * (Dd : Divisor K F) v := by
    intro c
    obtain ⟨Dd, hDd⟩ := Pic0.mk_surjective (c : Pic0 K F)
    have htor : (p : ℤ) • (c : Pic0 K F) = 0 := Pic0.mem_torsion.mp c.2
    have hz : Pic0.mk ((p : ℤ) • Dd) = 0 := by
      have h5 : Pic0.mk ((p : ℤ) • Dd) = (p : ℤ) • Pic0.mk Dd :=
        map_zsmul (QuotientAddGroup.mk'
          ((Divisor.principal (K := K) (F := F)).addSubgroupOf
            (Divisor.degZero (K := K) (F := F)))) (p : ℤ) Dd
      rw [h5, hDd, htor]
    have hmem2 : (p : ℤ) • Dd ∈
        (Divisor.principal (K := K) (F := F)).addSubgroupOf
          (Divisor.degZero (K := K) (F := F)) :=
      (QuotientAddGroup.eq_zero_iff _).mp hz
    rw [AddSubgroup.mem_addSubgroupOf] at hmem2
    obtain ⟨g, hg0, hgord⟩ := hmem2
    refine ⟨g, hg0, fun v => ⟨(Dd : Divisor K F) v, ?_⟩, Dd, hDd, fun v => ?_⟩
    · have h6 := hgord v
      have h7 : (((p : ℤ) • Dd : Divisor.degZero (K := K) (F := F)) : Divisor K F) v
          = (p : ℤ) * (Dd : Divisor K F) v := by
        have : (((p : ℤ) • Dd : Divisor.degZero (K := K) (F := F)) : Divisor K F)
            = (p : ℤ) • (Dd : Divisor K F) := rfl
        rw [this, Finsupp.smul_apply, smul_eq_mul]
      rw [← h6, h7]
    · have h6 := hgord v
      have h7 : (((p : ℤ) • Dd : Divisor.degZero (K := K) (F := F)) : Divisor K F) v
          = (p : ℤ) * (Dd : Divisor K F) v := by
        have : (((p : ℤ) • Dd : Divisor.degZero (K := K) (F := F)) : Divisor K F)
            = (p : ℤ) • (Dd : Divisor K F) := rfl
        rw [this, Finsupp.smul_apply, smul_eq_mul]
      rw [← h6, h7]
  choose gfun hgne hgdvd Dfun hDmk hDord using hchoice

  have hJmem : ∀ c : Pic0.torsion K F p,
      (gfun c)⁻¹ • D K F (gfun c) ∈ dlogSet K F p :=
    fun c => ⟨gfun c, hgne c, hgdvd c, rfl⟩
  set J : Pic0.torsion K F p → ↥(dlogSet K F p) :=
    fun c => ⟨(gfun c)⁻¹ • D K F (gfun c), hJmem c⟩ with hJdef
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).pos.ne'
  have hJinj : Function.Injective J := by
    intro c c' hcc
    have heq : (gfun c)⁻¹ • D K F (gfun c) = (gfun c')⁻¹ • D K F (gfun c') :=
      congrArg Subtype.val hcc
    have hg1 : gfun c ≠ 0 := hgne c
    have hg2 : gfun c' ≠ 0 := hgne c'
    have hr0 : gfun c * (gfun c')⁻¹ ≠ 0 := mul_ne_zero hg1 (inv_ne_zero hg2)
    have hdlogr : (gfun c * (gfun c')⁻¹)⁻¹ • D K F (gfun c * (gfun c')⁻¹) = 0 := by
      rw [dlog_mul hg1 (inv_ne_zero hg2), dlog_inv hg2, heq]
      exact add_neg_cancel _
    have hDr : D K F (gfun c * (gfun c')⁻¹) = 0 := by
      by_contra hne
      apply hne
      have h8 := congrArg (fun ω => (gfun c * (gfun c')⁻¹) • ω) hdlogr
      simp only [smul_smul, mul_inv_cancel₀ hr0, one_smul, smul_zero] at h8
      exact h8
    obtain ⟨s, hs⟩ := exists_pow_eq_of_D_eq_zero p x hDr
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [zero_pow (Fact.out : p.Prime).pos.ne'] at hs
      exact hr0 hs
    have hkey : ∀ v : Place K F,
        ((Dfun c : Divisor K F) - (Dfun c' : Divisor K F)) v = v.ord s := by
      intro v
      have h1 : v.ord (gfun c * (gfun c')⁻¹) = v.ord (gfun c) - v.ord (gfun c') := by
        rw [v.ord_mul hg1 (inv_ne_zero hg2), v.ord_inv]
        ring
      have h2 : v.ord (gfun c * (gfun c')⁻¹) = (p : ℤ) * v.ord s := by
        rw [hs, ← zpow_natCast, v.ord_zpow]
      have h9 : (p : ℤ) * ((Dfun c : Divisor K F) v - (Dfun c' : Divisor K F) v)
          = (p : ℤ) * v.ord s := by
        rw [mul_sub, ← hDord c v, ← hDord c' v, ← h1, h2]
      have h10 := mul_left_cancel₀ hp0 h9
      rw [Finsupp.sub_apply]
      exact h10
    have hprin : ((Dfun c - Dfun c' : Divisor.degZero (K := K) (F := F)) : Divisor K F)
        ∈ Divisor.principal (K := K) (F := F) := by
      refine ⟨s, hs0, fun v => ?_⟩
      have hco : ((Dfun c - Dfun c' : Divisor.degZero (K := K) (F := F)) : Divisor K F)
          = (Dfun c : Divisor K F) - (Dfun c' : Divisor K F) := rfl
      rw [hco]
      exact hkey v
    have hsub0 : Pic0.mk (Dfun c - Dfun c') = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hprin)
    have hmkeq : Pic0.mk (Dfun c) = Pic0.mk (Dfun c') := by
      have h11 : Pic0.mk (Dfun c) - Pic0.mk (Dfun c') = 0 := by
        have h12 : Pic0.mk (Dfun c) - Pic0.mk (Dfun c')
            = Pic0.mk (Dfun c - Dfun c') :=
          (map_sub (QuotientAddGroup.mk'
            ((Divisor.principal (K := K) (F := F)).addSubgroupOf
              (Divisor.degZero (K := K) (F := F)))) _ _).symm
        rw [h12]
        exact hsub0
      exact sub_eq_zero.mp h11
    have h13 : (c : Pic0 K F) = (c' : Pic0 K F) := by
      rw [← hDmk c, ← hDmk c', hmkeq]
    exact Subtype.ext h13

  obtain ⟨hSfin, hSle⟩ := hScard
  haveI := hSfin.to_subtype
  have hfin : Finite (Pic0.torsion K F p) := Finite.of_injective J hJinj
  refine ⟨hfin, ?_⟩
  calc Nat.card (Pic0.torsion K F p) ≤ Nat.card (dlogSet K F p) :=
        Nat.card_le_card_of_injective J hJinj
    _ ≤ p ^ Module.finrank K (regularDiffs K F) := hSle

private theorem finite_and_card_torsion_le_pow_finrank_unconditional_X [IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    [FiniteDimensional K (regularDiffs K F)]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    Finite (Pic0.torsion K F p) ∧
      Nat.card (Pic0.torsion K F p) ≤ p ^ Module.finrank K (regularDiffs K F) := by
  obtain ⟨C, ⟨h1, h2, h3⟩, -⟩ := cartierOperator_existsUnique (K := K) p x
  exact finite_and_card_torsion_le_pow_finrank_X p x C h1 h3

end PayoffDev

end AlgebraicCurve

universe u v

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    [FiniteDimensional K (AlgebraicCurve.regularDiffs K F)]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    Finite (AlgebraicCurve.Pic0.torsion K F p) ∧
      Nat.card (AlgebraicCurve.Pic0.torsion K F p) ≤
        p ^ Module.finrank K (AlgebraicCurve.regularDiffs K F) :=
  AlgebraicCurve.PayoffDev.finite_and_card_torsion_le_pow_finrank_unconditional_X p x

end

end S_AlgebraicCurve_finite_and_card_torsion_le_pow_finrank
end P2MW
export P2MW.S_AlgebraicCurve_finite_and_card_torsion_le_pow_finrank (solution)
