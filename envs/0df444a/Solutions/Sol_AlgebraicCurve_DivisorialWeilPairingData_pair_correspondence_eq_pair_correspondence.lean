-- Prove2me | solution 1 for AlgebraicCurve.DivisorialWeilPairingData.pair_correspondence_eq_pair_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/7d6629e8-24cf-5620-9fa4-5a741e68b3df

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_pullback
import Theorems.Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward
import Theorems.Thm_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul
import Theorems.Thm_AlgebraicCurve_Place_module_finite_residueField_restrict
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_pair_correspondence_eq_pair_correspondence
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_pair_correspondence_eq_pair_correspondence.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver Place.deg_eq_one_of_isAlgClosed_of_finite IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue Place Divisor HasPrincipalDivisors Pic0 Pic0.mk Pic0.torsion Pic0.mem_torsion Divisor.pushforward Divisor.pushforward_apply Divisor.pullback_apply_eq_ord algebraAlong isScalarTower_along isIntegral_along FundamentalIdentityAlong FiniteAlong NormFormulaAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.correspondence Divisor.correspondence_apply Pic0.correspondence Pic0.correspondence_mk Place.ord_restrictAlong Divisor.pullbackAlong_apply Place.fiberAlong Place.mem_fiberAlong DivisorialWeilPairingData WeilDatum WeilDatum.pairing Divisor.evalFun Divisor.evalFun_pullback Divisor.evalFun_algebraMap_pushforward Pic0.torsion.exists_forall_ord_eq_mul Place.module_finite_residueField_restrict Place.isRational_iff_deg_eq_one"
namespace WC8Sol
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

private theorem isRational_engine [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [IsAlgClosed K] [IsCurveOver K F] (w : Place K F') :
    w.IsRational := by
  haveI h1 : Module.Finite (w.restrict F).ResidueField w.ResidueField :=
    Place.module_finite_residueField_restrict K F F' w
  haveI h2 : Module.Finite K (w.restrict F).ResidueField :=
    IsCurveOver.finiteResidue (w.restrict F)
  haveI h3 : Module.Finite K w.ResidueField :=
    Module.Finite.trans (w.restrict F).ResidueField w.ResidueField
  exact (Place.isRational_iff_deg_eq_one w).mpr (Place.deg_eq_one_of_isAlgClosed_of_finite w)

private theorem hratF [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)

section UsetSec

open scoped Classical

private def Uset [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (S : Finset (Place K F)) : Finset (Place K F) :=
  (S.biUnion fun v' => Place.fiberAlong ψ hψ v').image fun w => w.restrictAlong φ hφ

private theorem mem_Uset_of [HasPrincipalDivisors K F'] {φ ψ : F →ₐ[K] F'}
    {hφ : φ.toRingHom.IsIntegral} {hψ : ψ.toRingHom.IsIntegral}
    {S : Finset (Place K F)} {w : Place K F'} (hw : w.restrictAlong ψ hψ ∈ S) :
    w.restrictAlong φ hφ ∈ Uset φ ψ hφ hψ S :=
  Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨_, hw, Place.mem_fiberAlong.mpr rfl⟩)

end UsetSec

private def normAlong (u : F →ₐ[K] F') (g : F') : F :=
  letI := algebraAlong u
  Algebra.norm F g

private theorem ord_map_eq [HasPrincipalDivisors K F'] (u : F →ₐ[K] F')
    (hu : u.toRingHom.IsIntegral) {n : ℕ} {a : F} {A : Divisor K F}
    (ha : ∀ v : Place K F, v.ord a = n * A v) (w : Place K F') :
    w.ord (u a) = n * (Divisor.pullbackAlong u hu A) w := by
  letI := algebraAlong u
  haveI := isScalarTower_along u
  haveI := isIntegral_along u hu
  have h1 := Divisor.pullback_apply_eq_ord (K := K) (F' := F')
    (f := a) (D := (n : ℤ) • A)
    (fun v => by rw [Finsupp.smul_apply, smul_eq_mul, ← ha v]) w
  have h2 : u a = algebraMap F F' a := rfl
  rw [h2, ← h1, map_zsmul, Finsupp.smul_apply, smul_eq_mul]
  rfl

private theorem map_ne_zero' (u : F →ₐ[K] F') {a : F} (ha : a ≠ 0) : u a ≠ 0 :=
  fun h => ha (u.toRingHom.injective (by rw [map_zero]; exact h))

private theorem ord_norm_eq [HasPrincipalDivisors K F'] (u : F →ₐ[K] F')
    (hu : u.toRingHom.IsIntegral) (hfin : FiniteAlong K u)
    (hN : NormFormulaAlong K u hfin) {n : ℕ} {g : F'} (hg : g ≠ 0) {D' : Divisor K F'}
    (hD' : ∀ w : Place K F', w.ord g = n * D' w) (v : Place K F) :
    v.ord (normAlong u g) = n * (Divisor.pushforwardAlong u hu D') v := by
  letI := algebraAlong u
  haveI := isScalarTower_along u
  haveI := isIntegral_along u hu
  haveI : Module.Finite F F' := hfin
  have h1 := hN g hg ((n : ℤ) • D')
    (fun w => by rw [Finsupp.smul_apply, smul_eq_mul, ← hD' w]) v
  have h2 : normAlong u g = Algebra.norm F g := rfl
  rw [h2, ← h1, map_zsmul, Finsupp.smul_apply, smul_eq_mul]
  rfl

private theorem normAlong_ne_zero (u : F →ₐ[K] F') (hfin : FiniteAlong K u)
    {g : F'} (hg : g ≠ 0) : normAlong u g ≠ 0 := by
  letI := algebraAlong u
  haveI : Module.Finite F F' := hfin
  exact Algebra.norm_ne_zero_iff.mpr hg

private theorem pullbackAlong_eq_zero [HasPrincipalDivisors K F'] {u : F →ₐ[K] F'}
    {hu : u.toRingHom.IsIntegral} {A : Divisor K F} {w : Place K F'}
    (hA : A (w.restrictAlong u hu) = 0) :
    Divisor.pullbackAlong u hu A w = 0 := by
  rw [Divisor.pullbackAlong_apply, hA, mul_zero]

private theorem correspondence_apply_eq_zero [HasPrincipalDivisors K F']
    {φ ψ : F →ₐ[K] F'} {hφ : φ.toRingHom.IsIntegral} {hψ : ψ.toRingHom.IsIntegral}
    {A : Divisor K F} {v : Place K F}
    (h : ∀ w : Place K F', w.restrictAlong ψ hψ = v → A (w.restrictAlong φ hφ) = 0) :
    Divisor.correspondence φ ψ hφ hψ A v = 0 := by
  rw [Divisor.correspondence_apply]
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI := isIntegral_along ψ hψ
  classical
  have happ := Divisor.pushforward_apply (K := K) (F := F) (F' := F')
    (Divisor.pullbackAlong φ hφ A) v
  have hz : ∀ w ∈ (Divisor.pullbackAlong φ hφ A).support,
      (if w.restrict F = v then (Divisor.pullbackAlong φ hφ A) w * (w.inertiaDeg F : ℤ)
        else 0) = 0 := by
    intro w hw
    by_cases hwv : w.restrict F = v
    · exfalso
      have hA0 : A (w.restrictAlong φ hφ) = 0 := h w hwv
      exact Finsupp.mem_support_iff.mp hw (pullbackAlong_eq_zero hA0)
    · rw [if_neg hwv]
  show Divisor.pushforward F (Divisor.pullbackAlong φ hφ A) v = 0
  rw [happ]
  exact Finset.sum_eq_zero hz

end AlgebraicCurve.WC8Sol

open AlgebraicCurve.WC8Sol in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    {F' : Type*} [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFIφ : FundamentalIdentityAlong K φ hφ) (hfinψ : FiniteAlong K ψ)
    (hNψ : NormFormulaAlong K ψ hfinψ)
    (hFIψ : FundamentalIdentityAlong K ψ hψ) (hfinφ : FiniteAlong K φ)
    (hNφ : NormFormulaAlong K φ hfinφ)
    {n : ℕ} [NeZero n] (e : DivisorialWeilPairingData K F n)
    (x y : Pic0 K F) (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0)
    (hcx : (n : ℤ) • Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x = 0)
    (hcy : (n : ℤ) • Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y = 0) :
    e.pair ⟨Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x, Pic0.mem_torsion.mpr hcx⟩
        ⟨y, Pic0.mem_torsion.mpr hy⟩
      = e.pair ⟨x, Pic0.mem_torsion.mpr hx⟩
          ⟨Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y, Pic0.mem_torsion.mpr hcy⟩ := by
  classical

  obtain ⟨DB, hDBmk, hDBrat, -⟩ := e.move ⟨y, Pic0.mem_torsion.mpr hy⟩ ∅
  obtain ⟨b, hb0, hbord⟩ :=
    Pic0.torsion.exists_forall_ord_eq_mul ⟨y, Pic0.mem_torsion.mpr hy⟩ DB hDBmk
  obtain ⟨DA, hDAmk, hDArat, hDAavoid⟩ := e.move ⟨x, Pic0.mem_torsion.mpr hx⟩
    (Uset φ ψ hφ hψ (DB : Divisor K F).support ∪ (DB : Divisor K F).support)
  obtain ⟨a, ha0, haord⟩ :=
    Pic0.torsion.exists_forall_ord_eq_mul ⟨x, Pic0.mem_torsion.mpr hx⟩ DA hDAmk
  have hDAmk' : Pic0.mk DA = x := hDAmk
  have hDBmk' : Pic0.mk DB = y := hDBmk

  have havoidU : ∀ v ∈ (DA : Divisor K F).support,
      v ∉ Uset φ ψ hφ hψ (DB : Divisor K F).support := fun v hv h =>
    hDAavoid v hv (Finset.mem_union_left _ h)
  have havoidB : ∀ v ∈ (DA : Divisor K F).support,
      v ∉ (DB : Divisor K F).support := fun v hv h =>
    hDAavoid v hv (Finset.mem_union_right _ h)

  have hkey : ∀ w : Place K F', w.restrictAlong ψ hψ ∈ (DB : Divisor K F).support →
      (DA : Divisor K F) (w.restrictAlong φ hφ) = 0 := by
    intro w hw
    by_contra hne
    exact havoidU _ (Finsupp.mem_support_iff.mpr hne) (mem_Uset_of hw)

  have hkey' : ∀ w : Place K F', (DA : Divisor K F) (w.restrictAlong φ hφ) ≠ 0 →
      (w.restrictAlong ψ hψ).ord b = 0 := by
    intro w hA
    rw [hbord]
    by_cases hB : (DB : Divisor K F) (w.restrictAlong ψ hψ) = 0
    · rw [hB, mul_zero]
    · exact absurd (hkey w (Finsupp.mem_support_iff.mpr hB)) hA

  set TA : Divisor K F := Divisor.correspondence φ ψ hφ hψ (DA : Divisor K F) with hTA
  set TB : Divisor K F := Divisor.correspondence ψ φ hψ hφ (DB : Divisor K F) with hTB
  have hordL1 : ∀ v : Place K F, v.ord (normAlong ψ (φ a)) = n * TA v := by
    intro v
    rw [hTA, Divisor.correspondence_apply]
    exact ord_norm_eq ψ hψ hfinψ hNψ (map_ne_zero' φ ha0)
      (fun w => ord_map_eq φ hφ haord w) v
  have hordR2 : ∀ v : Place K F, v.ord (normAlong φ (ψ b)) = n * TB v := by
    intro v
    rw [hTB, Divisor.correspondence_apply]
    exact ord_norm_eq φ hφ hfinφ hNφ (map_ne_zero' ψ hb0)
      (fun w => ord_map_eq ψ hψ hbord w) v
  have hdisjL : ∀ v : Place K F, TA v = 0 ∨ (DB : Divisor K F) v = 0 := by
    intro v
    by_cases hB : (DB : Divisor K F) v = 0
    · exact Or.inr hB
    · refine Or.inl (correspondence_apply_eq_zero fun w hwv => hkey w ?_)
      rw [hwv]
      exact Finsupp.mem_support_iff.mpr hB
  have hdisjR : ∀ v : Place K F, (DA : Divisor K F) v = 0 ∨ TB v = 0 := by
    intro v
    by_cases hA : (DA : Divisor K F) v = 0
    · exact Or.inl hA
    · refine Or.inr (correspondence_apply_eq_zero fun w hwv => ?_)
      by_contra hBne
      refine havoidU _ (Finsupp.mem_support_iff.mpr hA) ?_
      rw [← hwv]
      exact mem_Uset_of (Finsupp.mem_support_iff.mpr hBne)
  refine Eq.trans (b := WeilDatum.pairing (K := K) (F := F) (n := n)
    ⟨TA, (DB : Divisor K F), normAlong ψ (φ a), b,
      normAlong_ne_zero ψ hfinψ (map_ne_zero' φ ha0), hb0,
      hordL1, hbord, hdisjL, fun v _ => hratF v⟩) ?_ ?_

  · set dL : WeilDatum K F n :=
      ⟨TA, (DB : Divisor K F), normAlong ψ (φ a), b,
        normAlong_ne_zero ψ hfinψ (map_ne_zero' φ ha0), hb0,
        hordL1, hbord, hdisjL, fun v _ => hratF v⟩ with hdL
    have hclassL : dL.classLeft
        = ⟨Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x, Pic0.mem_torsion.mpr hcx⟩ := by
      refine Subtype.ext ?_
      show Pic0.mk _ = Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x
      rw [← hDAmk', Pic0.correspondence_mk]
      exact congrArg Pic0.mk (Subtype.ext rfl)
    have hclassR : dL.classRight = ⟨y, Pic0.mem_torsion.mpr hy⟩ := by
      refine Subtype.ext ?_
      show Pic0.mk _ = y
      rw [← hDBmk']
      exact congrArg Pic0.mk (Subtype.ext rfl)
    have h := e.compatible dL
    rw [hclassL, hclassR] at h
    exact h

  · set dR : WeilDatum K F n :=
      ⟨(DA : Divisor K F), TB, a, normAlong φ (ψ b),
        ha0, normAlong_ne_zero φ hfinφ (map_ne_zero' ψ hb0),
        haord, hordR2, hdisjR, fun v _ => hratF v⟩ with hdR
    have hclassL' : dR.classLeft = ⟨x, Pic0.mem_torsion.mpr hx⟩ := by
      refine Subtype.ext ?_
      show Pic0.mk _ = x
      rw [← hDAmk']
      exact congrArg Pic0.mk (Subtype.ext rfl)
    have hclassR' : dR.classRight
        = ⟨Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y, Pic0.mem_torsion.mpr hcy⟩ := by
      refine Subtype.ext ?_
      show Pic0.mk _ = Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y
      rw [← hDBmk', Pic0.correspondence_mk]
      exact congrArg Pic0.mk (Subtype.ext rfl)
    have hpair : WeilDatum.pairing (K := K) (F := F) (n := n)
        ⟨TA, (DB : Divisor K F), normAlong ψ (φ a), b,
          normAlong_ne_zero ψ hfinψ (map_ne_zero' φ ha0), hb0,
          hordL1, hbord, hdisjL, fun v _ => hratF v⟩ = dR.pairing := by

      show Divisor.evalFun (normAlong ψ (φ a)) (DB : Divisor K F)
            / Divisor.evalFun b TA
          = Divisor.evalFun a TB / Divisor.evalFun (normAlong φ (ψ b)) (DA : Divisor K F)

      have hE4 : Divisor.evalFun (normAlong ψ (φ a)) (DB : Divisor K F)
          = Divisor.evalFun (φ a) (Divisor.pullbackAlong ψ hψ (DB : Divisor K F)) := by
        letI := algebraAlong ψ
        haveI := isScalarTower_along ψ
        haveI := isIntegral_along ψ hψ
        haveI : Module.Finite F F' := hfinψ
        haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
        haveI : Algebra.IsSeparable F F' := inferInstance
        exact (Divisor.evalFun_pullback (map_ne_zero' φ ha0) (DB : Divisor K F)
          (fun v _ => hratF v) (fun v _ w _ => isRational_engine (F := F) w)
          (fun v hv w hw => by
            have h1 : w.restrictAlong ψ hψ = v := Place.mem_fiberAlong.mp hw
            have h0 : (DA : Divisor K F) (w.restrictAlong φ hφ) = 0 := by
              apply hkey
              rw [h1]; exact hv
            rw [ord_map_eq φ hφ haord w, pullbackAlong_eq_zero h0, mul_zero])).symm

      have hE12 : Divisor.evalFun b TA
          = Divisor.evalFun (normAlong φ (ψ b)) (DA : Divisor K F) := by
        have hE1 : Divisor.evalFun b TA
            = Divisor.evalFun (ψ b) (Divisor.pullbackAlong φ hφ (DA : Divisor K F)) := by
          rw [hTA, Divisor.correspondence_apply]
          letI := algebraAlong ψ
          haveI := isScalarTower_along ψ
          haveI := isIntegral_along ψ hψ
          haveI : Module.Finite F F' := hfinψ
          exact (Divisor.evalFun_algebraMap_pushforward hb0
            (Divisor.pullbackAlong φ hφ (DA : Divisor K F))
            (fun w _ => isRational_engine (F := F) w) (fun w _ => hratF (w.restrict F))
            (fun w hw => by
              have hAne : (DA : Divisor K F) (w.restrictAlong φ hφ) ≠ 0 := fun hA =>
                Finsupp.mem_support_iff.mp hw (pullbackAlong_eq_zero hA)
              exact hkey' w hAne)).symm
        have hE2 : Divisor.evalFun (ψ b) (Divisor.pullbackAlong φ hφ (DA : Divisor K F))
            = Divisor.evalFun (normAlong φ (ψ b)) (DA : Divisor K F) := by
          letI := algebraAlong φ
          haveI := isScalarTower_along φ
          haveI := isIntegral_along φ hφ
          haveI : Module.Finite F F' := hfinφ
          haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
          haveI : Algebra.IsSeparable F F' := inferInstance
          exact Divisor.evalFun_pullback (map_ne_zero' ψ hb0) (DA : Divisor K F)
            (fun v _ => hratF v) (fun v _ w _ => isRational_engine (F := F) w)
            (fun v hv w hw => by
              have h1 : w.restrictAlong φ hφ = v := Place.mem_fiberAlong.mp hw
              have hvne : (DA : Divisor K F) (w.restrictAlong φ hφ) ≠ 0 := by
                rw [h1]; exact Finsupp.mem_support_iff.mp hv
              rw [Place.ord_restrictAlong ψ hψ w b, hkey' w hvne, mul_zero])
        rw [hE1, hE2]

      have hE3 : Divisor.evalFun a TB
          = Divisor.evalFun (φ a) (Divisor.pullbackAlong ψ hψ (DB : Divisor K F)) := by
        rw [hTB, Divisor.correspondence_apply]
        letI := algebraAlong φ
        haveI := isScalarTower_along φ
        haveI := isIntegral_along φ hφ
        haveI : Module.Finite F F' := hfinφ
        exact (Divisor.evalFun_algebraMap_pushforward ha0
          (Divisor.pullbackAlong ψ hψ (DB : Divisor K F))
          (fun w _ => isRational_engine (F := F) w) (fun w _ => hratF (w.restrict F))
          (fun w hw => by
            have hBne : (DB : Divisor K F) (w.restrictAlong ψ hψ) ≠ 0 := fun hB0 =>
              Finsupp.mem_support_iff.mp hw (pullbackAlong_eq_zero hB0)
            have h2 : (DA : Divisor K F) (w.restrict F) = 0 :=
              hkey w (Finsupp.mem_support_iff.mpr hBne)
            rw [haord, h2, mul_zero])).symm
      rw [hE4, hE12, hE3]
    rw [hpair]
    have h := e.compatible dR
    rw [hclassL', hclassR'] at h
    exact h.symm

end

end S_AlgebraicCurve_DivisorialWeilPairingData_pair_correspondence_eq_pair_correspondence
end P2MW
export P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_pair_correspondence_eq_pair_correspondence (solution)
