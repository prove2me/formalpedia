-- Prove2me | solution 1 for AlgebraicCurve.exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c539c19d-6aac-53d9-b52b-008fa6df29fe

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
import Theorems.Thm_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice
import Theorems.Thm_AlgebraicCurve_Place_continuous_restrictAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C"
p2m_attr_erase "simp" "ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice.AlgebraicCurve"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along Place.restrictInclusion Place.restrictResidueMap_residue Place.algebraMap_residueField_eq Place Place.FiniteResidue HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.algebraMap_mem' Differential.pullbackAlong Differential.pullbackAlong_D Differential.pullbackAlong_smul IsCurveOver IsCurveOver.instNontrivialKaehler Place.evalAt regularDifferentials mem_regularDifferentials_iff Place.ord_dCoordFn Place.chartRead_apply Place.readDifferential_apply abelJacobiVec pathPeriodLattice Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice Place.continuous_restrictAlong"
namespace AbelJacobiPullbackProof
p2m_open "AlgebraicCurve"

section Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pos_of_not_isUnit (v : Place K F) {a : v.toValuationSubring} (ha : a ≠ 0)
    (hu : ¬IsUnit a) : 0 < v.ord (a : F) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hn : n ≠ 0 := by
    rintro rfl
    exact hu (by rw [pow_zero, mul_one]; exact u.isUnit)
  have hcoe : (((u : v.toValuationSubring) * π ^ n : v.toValuationSubring) : F) =
      ((u : v.toValuationSubring) : F) * (π : F) ^ (n : ℤ) := by
    rw [zpow_natCast, Subring.coe_mul, SubmonoidClass.coe_pow]
  rw [hcoe, v.ord_unit_smul_zpow u hπ]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) u.inv_mul
      simpa [hu] using this
    have h2 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← h2]
    exact SetLike.coe_mem _
  have ha : (⟨f⁻¹, hinv⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    exact inv_ne_zero hf0 (by simpa using congrArg Subtype.val h)
  have := ord_pos_of_not_isUnit v ha hu
  rw [show ((⟨f⁻¹, hinv⟩ : v.toValuationSubring) : F) = f⁻¹ from rfl, v.ord_inv] at this
  omega

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  exact absurd (ord_neg_of_not_mem v hf) (not_lt.2 h)

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  by_cases hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring)
  · have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    exact le_of_eq this.symm
  · exact (ord_pos_of_not_isUnit v (fun h0 => hf0 (by simpa using congrArg Subtype.val h0)) hu).le

theorem finite_setOf_not_mem [HasPrincipalDivisors K F] (f : F) :
    {w : Place K F | f ∉ w.toValuationSubring}.Finite := by
  by_cases hf0 : f = 0
  · subst hf0
    convert Set.finite_empty
    ext w
    simp
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h := ord_neg_of_not_mem w hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h.ne

theorem finite_setOf_ord_ne_zero [HasPrincipalDivisors K F] {f : F} (hf0 : f ≠ 0) :
    {w : Place K F | w.ord f ≠ 0}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h : w.ord f ≠ 0 := hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h

theorem isRational_of_isAlgClosed [IsAlgClosed K] (w : Place K F) [w.FiniteResidue] :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem residue_algebraMap (w : Place K F) (a : K) :
    IsLocalRing.residue w.toValuationSubring
        (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.ResidueField a := by
  have h : (⟨algebraMap K F a, w.algebraMap_mem' a⟩ : w.toValuationSubring) =
      algebraMap K w.toValuationSubring a := Subtype.ext (w.coe_algebraMap a).symm
  rw [h]
  exact (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField a).symm

theorem evalAt_algebraMap (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

theorem evalAt_zero (w : Place K F) : w.evalAt (0 : F) = 0 := by
  simpa using evalAt_algebraMap w (0 : K)

theorem evalAt_add (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f + g) = w.evalAt f + w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (add_mem hf hg), map_add, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_add]
  rfl

theorem evalAt_mul (w : Place K F) (hw : w.IsRational) {f g : F}
    (hf : f ∈ w.toValuationSubring) (hg : g ∈ w.toValuationSubring) :
    w.evalAt (f * g) = w.evalAt f * w.evalAt g := by
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw (mul_mem hf hg), map_mul, w.algebraMap_evalAt hw hf,
    w.algebraMap_evalAt hw hg, ← map_mul]
  rfl

theorem evalAt_eq_zero_of_ord_pos (v : Place K F) {f : F} (h : 0 < v.ord f) : v.evalAt f = 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v h.le
  have hnu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    change v.ord f = 0 at this
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2
      (mem_nonunits_iff.2 hnu))
  rw [v.evalAt_of_mem hf, hres, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem evalAt_ne_zero_of_ord_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (h : v.ord f = 0) : v.evalAt f ≠ 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v h.ge
  have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra hu
    have := ord_pos_of_not_isUnit v (a := ⟨f, hf⟩)
      (fun h0 => hf0 (by simpa using congrArg Subtype.val h0)) hu
    change 0 < v.ord f at this
    omega
  intro h0
  have h1 := v.algebraMap_evalAt hv hf
  rw [h0, map_zero] at h1
  have h2 : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu
  exact h2 h1.symm

theorem ord_algebraMap (v : Place K F) (a : K) : v.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hu : IsUnit (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring) := by
      refine IsUnit.of_mul_eq_one ⟨algebraMap K F a⁻¹, v.algebraMap_mem' a⁻¹⟩ ?_
      ext
      simp [ha]
    have := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this

theorem differentialCoeff_mem (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {η : Ω[F⁄K]} (hη : η ∈ regularDifferentials K F) :
    v.differentialCoeff η ∈ v.toValuationSubring := by
  obtain ⟨f, hf, hfe⟩ := (mem_regularDifferentials_iff (K := K) (F := F)).1 hη v
  rwa [v.differentialCoeff_unique hfe]

theorem dCoordFn_mem (v : Place K F) : v.dCoordFn ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (by rw [v.ord_dCoordFn]; exact zero_le_one)

theorem dCoordFn_ne_zero (v : Place K F) : v.dCoordFn ≠ 0 := by
  intro h
  have := v.ord_dCoordFn
  rw [h, v.ord_zero] at this
  exact zero_ne_one this

end Algebra

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (f : F) : f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') : 0 < w.ramificationIndexAlong φ := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem evalAt_restrictAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hw : w.IsRational) (hv : (w.restrictAlong φ hφ).IsRational) (f : F) :
    (w.restrictAlong φ hφ).evalAt f = w.evalAt (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  change (w.restrict F).evalAt f = w.evalAt (algebraMap F F' f)
  by_cases hf : f ∈ (w.restrict F).toValuationSubring
  · have hf' : algebraMap F F' f ∈ w.toValuationSubring := hf
    apply w.algebraMap_residueField_injective
    rw [w.algebraMap_evalAt hw hf']
    have h1 : (⟨algebraMap F F' f, hf'⟩ : w.toValuationSubring) =
        Place.restrictInclusion F w ⟨f, hf⟩ := rfl
    rw [h1, ← Place.restrictResidueMap_residue, ← (w.restrict F).algebraMap_evalAt hv hf,
      ← Place.algebraMap_residueField_eq, ← IsScalarTower.algebraMap_apply]
  · have hf' : algebraMap F F' f ∉ w.toValuationSubring := hf
    rw [Place.evalAt, dif_neg hf, Place.evalAt, dif_neg hf']

end Along

theorem isOpen_setOf_mem {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [T2Space (Place ℂ F)] (f : F) :
    IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring} := by
  have h : {w : Place ℂ F | f ∈ w.toValuationSubring} =
      {w : Place ℂ F | f ∉ w.toValuationSubring}ᶜ := by
    ext w; simp
  rw [h]
  exact (finite_setOf_not_mem (K := ℂ) f).isClosed.isOpen_compl

section Compatible

def ChartCompatible (F : Type*) [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
    [ChartedSpace ℂ (Place ℂ F)] : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

variable {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]

theorem isRational (w : Place ℂ F) : w.IsRational := isRational_of_isAlgClosed w

theorem chartRead_center (P : Place ℂ F) (f : F) :
    P.chartRead f (extChartAt 𝓘(ℂ, ℂ) P P) = P.evalAt f := by
  rw [Place.chartRead_apply, extChartAt_to_inv]

theorem enat_map_eq_coe {o : ℕ∞} {k : ℤ} (h : o.map (fun n : ℕ => (n : ℤ)) = (k : WithTop ℤ)) :
    o ≠ ⊤ ∧ ((o.toNat : ℕ) : ℤ) = k := by
  induction o using ENat.recTopCoe with
  | top => simp at h
  | coe m =>
    simp only [ENat.map_coe, WithTop.coe_eq_coe] at h
    exact ⟨ENat.coe_ne_top m, by simpa using h⟩

theorem analyticOrderAt_chartRead_sub (hF : ChartCompatible F) (w : Place ℂ F) {f : F}
    (hf : f ∈ w.toValuationSubring) (t : ℂ) (hne : f - algebraMap ℂ F t ≠ 0) :
    (analyticOrderAt (fun z => w.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) w w)).map
        (fun n : ℕ => (n : ℤ)) = ((w.ord (f - algebraMap ℂ F t) : ℤ) : WithTop ℤ) := by
  obtain ⟨-, hord⟩ := hF (f - algebraMap ℂ F t) hne w
  have hreg : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) w w),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) w).symm z).toValuationSubring := by
    have := (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) w).preimage_mem_nhds
      (t := {w' : Place ℂ F | f ∈ w'.toValuationSubring})
      (by rw [extChartAt_to_inv]; exact (isOpen_setOf_mem f).mem_nhds hf)
    exact this
  have hEq : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) (f - algebraMap ℂ F t))
      =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) w w)] fun z => w.chartRead f z - t := by
    filter_upwards [hreg] with z hz
    rw [Place.chartRead_apply, sub_eq_add_neg, ← map_neg,
      evalAt_add _ (isRational _) hz (Place.algebraMap_mem' _ _), evalAt_algebraMap]
    ring
  rw [meromorphicOrderAt_congr (hEq.filter_mono nhdsWithin_le_nhds)] at hord
  have hA : AnalyticAt ℂ (fun z => w.chartRead f z - t) (extChartAt 𝓘(ℂ, ℂ) w w) :=
    (AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF w hf).sub analyticAt_const
  rw [hA.meromorphicOrderAt_eq] at hord
  exact hord

theorem chartRead_dCoordFn (hF : ChartCompatible F) (v : Place ℂ F) :
    AnalyticAt ℂ (v.chartRead v.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      v.chartRead v.dCoordFn (extChartAt 𝓘(ℂ, ℂ) v v) = 0 ∧
      deriv (v.chartRead v.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) v v) ≠ 0 := by
  have hA : AnalyticAt ℂ (v.chartRead v.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) v v) :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF v (dCoordFn_mem v)
  have hval : v.chartRead v.dCoordFn (extChartAt 𝓘(ℂ, ℂ) v v) = 0 := by
    rw [chartRead_center]
    exact evalAt_eq_zero_of_ord_pos v (by rw [v.ord_dCoordFn]; exact one_pos)
  have hne : v.dCoordFn - algebraMap ℂ F 0 ≠ 0 := by
    rw [map_zero, sub_zero]; exact dCoordFn_ne_zero v
  have hord := analyticOrderAt_chartRead_sub hF v (dCoordFn_mem v) 0 hne
  rw [map_zero, sub_zero, v.ord_dCoordFn] at hord
  obtain ⟨htop, hk⟩ := enat_map_eq_coe hord
  have h1 : analyticOrderAt (fun z => v.chartRead v.dCoordFn z - 0) (extChartAt 𝓘(ℂ, ℂ) v v) =
      (1 : ℕ) := by
    rw [← ENat.coe_toNat htop]
    congr 1
    exact_mod_cast hk
  have hA0 : AnalyticAt ℂ (fun z => v.chartRead v.dCoordFn z - 0) (extChartAt 𝓘(ℂ, ℂ) v v) :=
    hA.sub analyticAt_const
  obtain ⟨q, hqa, hq0, hfac⟩ := hA0.analyticOrderAt_eq_natCast.1 h1
  set c := extChartAt 𝓘(ℂ, ℂ) v v with hc
  have hfun : (fun z => v.chartRead v.dCoordFn z - 0) =ᶠ[𝓝 c] fun z => (z - c) * q z :=
    hfac.mono fun z hz => by simpa only [pow_one, smul_eq_mul] using hz
  have hd : HasDerivAt (fun z => (z - c) * q z) (1 * q c + (c - c) * deriv q c) c :=
    ((hasDerivAt_id c).sub_const c).mul hqa.differentiableAt.hasDerivAt
  have h2 : deriv (fun z => v.chartRead v.dCoordFn z - 0) c = q c := by
    rw [hfun.deriv_eq, hd.deriv]; ring
  refine ⟨hA, hval, ?_⟩
  rw [show deriv (v.chartRead v.dCoordFn) c = deriv (fun z => v.chartRead v.dCoordFn z - 0) c by
    simp, h2]
  exact hq0

end Compatible

end AlgebraicCurve.AbelJacobiPullbackProof

open AlgebraicCurve.AbelJacobiPullbackProof in

theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (F' : Type*) [Field F'] [Algebra ℂ F']
    (hfg' : ∃ y : F', Transcendental ℂ y ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({y} : Set F')) F')
    [IsCurveOver ℂ F']
    [TopologicalSpace (Place ℂ F')] [ChartedSpace ℂ (Place ℂ F')] [T2Space (Place ℂ F')]
    (hF' : ∀ f : F', f ≠ 0 → ∀ w : Place ℂ F',
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) w).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) w w) = (w.ord f : WithTop ℤ))
    (ψ : F →ₐ[ℂ] F') (hψ : ψ.toRingHom.IsIntegral)
    {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ F)
    (P₀ : Place ℂ F) (W : Place ℂ F') :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r ⊆ (extChartAt 𝓘(ℂ, ℂ) W).target ∧
      ∃ Ψ : Fin n → ℂ → ℂ,
        (∀ i, ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r,
          HasDerivAt (Ψ i) (W.readDifferential (Differential.pullbackAlong ψ (b i)) u) u) ∧
        ∀ u ∈ Metric.ball (extChartAt 𝓘(ℂ, ℂ) W W) r,
          abelJacobiVec b P₀ (((extChartAt 𝓘(ℂ, ℂ) W).symm u).restrictAlong ψ hψ) -
              abelJacobiVec b P₀ (W.restrictAlong ψ hψ) -
              (fun i => Ψ i u - Ψ i (extChartAt 𝓘(ℂ, ℂ) W W)) ∈ pathPeriodLattice b := by
  haveI : Nontrivial Ω[F⁄ℂ] := IsCurveOver.instNontrivialKaehler (K := ℂ) (F := F)
  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := by
    obtain ⟨x, hx, hfd⟩ := hfg
    haveI := AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
    exact AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hFc : ChartCompatible F := hF
  have hF'c : ChartCompatible F' := hF'
  have hrat : ∀ v : Place ℂ F, v.IsRational := fun v => isRational v
  have hrat' : ∀ w : Place ℂ F', w.IsRational := fun w => isRational w
  set cW := extChartAt 𝓘(ℂ, ℂ) W W with hcW
  set σW := (extChartAt 𝓘(ℂ, ℂ) W).symm with hσW

  set RW : Place ℂ F := W.restrictAlong ψ hψ with hRW
  set πW : F := RW.dCoordFn with hπW
  set ξ : ℂ := extChartAt 𝓘(ℂ, ℂ) RW RW with hξ
  set Rr : ℂ → ℂ := RW.chartRead πW with hRr
  haveI := hgen RW
  have hπWmem : πW ∈ RW.toValuationSubring := dCoordFn_mem RW
  have hψπW : ψ πW ∈ W.toValuationSubring := (mem_restrictAlong_iff ψ hψ W πW).1 hπWmem
  set h : Fin n → F := fun i => RW.differentialCoeff (b i) with hh
  have hhmem : ∀ i, h i ∈ RW.toValuationSubring := fun i => differentialCoeff_mem RW (hb i)
  have hψh : ∀ i, ψ (h i) ∈ W.toValuationSubring := fun i =>
    (mem_restrictAlong_iff ψ hψ W (h i)).1 (hhmem i)
  have hbi : ∀ i, b i = h i • KaehlerDifferential.D ℂ F πW := fun i => by
    rw [hπW, ← RW.dCoord_eq_D_dCoordFn, hh, RW.differentialCoeff_smul_dCoord]
  have hpullψ : ∀ i, Differential.pullbackAlong ψ (b i) =
      ψ (h i) • KaehlerDifferential.D ℂ F' (ψ πW) := fun i => by
    rw [hbi i, Differential.pullbackAlong_smul, Differential.pullbackAlong_D]
  obtain ⟨hRran, hRrξ, hRrd⟩ := chartRead_dCoordFn hFc RW
  have hRrξ' : Rr ξ = 0 := hRrξ
  have hS : HasStrictDerivAt Rr (deriv Rr ξ) ξ := hRran.hasStrictDerivAt
  set L : ℂ → ℂ := hS.localInverse Rr (deriv Rr ξ) ξ hRrd with hL
  have hLan : AnalyticAt ℂ L (Rr ξ) := hRran.analyticAt_localInverse hRrd
  have hleft : ∀ᶠ x in 𝓝 ξ, L (Rr x) = x := hS.eventually_left_inverse hRrd

  obtain ⟨rR, hrR, htarR, Φ, hΦd, hΦAJ⟩ :=
    AlgebraicCurve.exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice F hfg hF b hb P₀ RW
  obtain ⟨s, hs, hsball⟩ : ∃ s > 0, ∀ x ∈ Metric.ball ξ s,
      x ∈ Metric.ball ξ rR ∧ L (Rr x) = x ∧ AnalyticAt ℂ Rr x :=
    Metric.eventually_nhds_iff_ball.1
      ((show ∀ᶠ x in 𝓝 ξ, x ∈ Metric.ball ξ rR from Metric.ball_mem_nhds ξ hrR).and
        (hleft.and hRran.eventually_analyticAt))

  have hcontψ : Continuous fun w : Place ℂ F' => w.restrictAlong ψ hψ :=
    AlgebraicCurve.Place.continuous_restrictAlong F F' hF hF' ψ hψ
  set Qψ : ℂ → Place ℂ F := fun u => (σW u).restrictAlong ψ hψ with hQψ
  have hσWc : σW cW = W := by rw [hσW, hcW, extChartAt_to_inv]
  have hQψc : Qψ cW = RW := by simp only [hQψ, hσWc, hRW]
  have hQψcont : ContinuousAt Qψ cW :=
    hcontψ.continuousAt.comp (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) W)
  set Ξ : ℂ → ℂ := fun u => extChartAt 𝓘(ℂ, ℂ) RW (Qψ u) with hΞ
  set qW : ℂ → ℂ := W.chartRead (ψ πW) with hqW
  have hqWan : AnalyticAt ℂ qW cW :=
    AlgebraicCurve.Place.analyticAt_evalAt_extChartAt_symm_of_mem F' hF' W hψπW
  have hqWc : qW cW = 0 := by
    rw [hqW, hcW, chartRead_center, ← evalAt_restrictAlong ψ hψ W (hrat' W) (hrat _) πW]
    exact evalAt_eq_zero_of_ord_pos _ (by rw [Place.ord_dCoordFn]; exact one_pos)

  have e1 : ∀ᶠ u in 𝓝 cW, u ∈ (extChartAt 𝓘(ℂ, ℂ) W).target := extChartAt_target_mem_nhds W
  have e4 : ∀ᶠ u in 𝓝 cW, Qψ u ∈ (extChartAt 𝓘(ℂ, ℂ) RW).source ∩
      extChartAt 𝓘(ℂ, ℂ) RW ⁻¹' Metric.ball ξ s := by
    refine hQψcont.preimage_mem_nhds ?_
    rw [hQψc]
    exact (isOpen_extChartAt_preimage' (I := 𝓘(ℂ, ℂ)) RW Metric.isOpen_ball).mem_nhds
      ⟨mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) RW, Metric.mem_ball_self hs⟩
  have hkeyσ : ∀ u, Qψ u ∈ (extChartAt 𝓘(ℂ, ℂ) RW).source →
      (extChartAt 𝓘(ℂ, ℂ) RW).symm (Ξ u) = Qψ u := fun u hu =>
    (extChartAt 𝓘(ℂ, ℂ) RW).left_inv hu
  have hkeyread : ∀ u, Qψ u ∈ (extChartAt 𝓘(ℂ, ℂ) RW).source → ∀ f : F,
      RW.chartRead f (Ξ u) = W.chartRead (ψ f) u := by
    intro u hu f
    rw [Place.chartRead_apply, hkeyσ u hu, hQψ]
    exact evalAt_restrictAlong ψ hψ (σW u) (hrat' _) (hrat _) f
  have e6 : ∀ᶠ u in 𝓝 cW, Ξ u = L (qW u) := by
    filter_upwards [e4] with u hu
    obtain ⟨hsrc, hΞs⟩ := hu
    have h1 := (hsball (Ξ u) hΞs).2.1
    rw [← h1, hRr, hkeyread u hsrc πW]
  have e5 : AnalyticAt ℂ (L ∘ qW) cW :=
    hLan.comp_of_eq hqWan (by rw [hqWc, hRrξ'])
  have e7 : ∀ᶠ u in 𝓝 cW, AnalyticAt ℂ Ξ u := by
    filter_upwards [e6.eventually_nhds, e5.eventually_analyticAt] with u hu han
    exact han.congr (hu.mono fun y hy => by rw [Function.comp_apply, hy])
  have e8 : ∀ᶠ u in 𝓝 cW, ∀ i,
      W.readDifferential (Differential.pullbackAlong ψ (b i)) u =
        W.chartRead (ψ (h i)) u * deriv qW u := by
    refine Filter.eventually_all.2 fun i => ?_
    have h1 := (AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
      F' hfg' hF' W hψπW (ψ (h i))).2 (hψh i)
    rw [← hpullψ i] at h1
    exact h1

  obtain ⟨ρ, hρ, hall⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e4.and (e7.and e8)))
  set Ψ : Fin n → ℂ → ℂ := fun i u => Φ i (Ξ u) with hΨ
  have hΞc : Ξ cW = ξ := by simp only [hΞ, hQψc, hξ]
  have hΞs : ∀ u ∈ Metric.ball cW ρ, Ξ u ∈ Metric.ball ξ s := fun u hu => (hall u hu).2.1.2
  have hΞr : ∀ u ∈ Metric.ball cW ρ, Ξ u ∈ Metric.ball ξ rR := fun u hu =>
    (hsball _ (hΞs u hu)).1
  have hsrcR : ∀ u ∈ Metric.ball cW ρ, Qψ u ∈ (extChartAt 𝓘(ℂ, ℂ) RW).source := fun u hu =>
    (hall u hu).2.1.1
  have hRrΞ : ∀ u ∈ Metric.ball cW ρ, Rr (Ξ u) = qW u := fun u hu => by
    rw [hRr, hkeyread u (hsrcR u hu) πW]
  refine ⟨ρ, hρ, fun u hu => (hall u hu).1, Ψ, ?_, ?_⟩
  ·
    intro i u hu
    have hΞan : AnalyticAt ℂ Ξ u := (hall u hu).2.2.1
    have hΞd : HasDerivAt Ξ (deriv Ξ u) u := hΞan.differentiableAt.hasDerivAt
    have hΦ' : HasDerivAt (Φ i) (RW.readDifferential (b i) (Ξ u)) (Ξ u) :=
      hΦd i (Ξ u) (hΞr u hu)
    have hcomp : HasDerivAt (Φ i ∘ Ξ) (RW.readDifferential (b i) (Ξ u) * deriv Ξ u) u :=
      hΦ'.comp u hΞd
    have hRrd' : HasDerivAt qW (deriv Rr (Ξ u) * deriv Ξ u) u := by
      have h1 : HasDerivAt (Rr ∘ Ξ) (deriv Rr (Ξ u) * deriv Ξ u) u :=
        (hsball _ (hΞs u hu)).2.2.differentiableAt.hasDerivAt.comp u hΞd
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hu] with y hy
      rw [Function.comp_apply, hRrΞ y hy]
    have hprod : RW.readDifferential (b i) (Ξ u) * deriv Ξ u =
        W.readDifferential (Differential.pullbackAlong ψ (b i)) u := by
      rw [Place.readDifferential_apply, hkeyread u (hsrcR u hu) (RW.differentialCoeff (b i)),
        mul_assoc, ← hRrd'.deriv, ← (hall u hu).2.2.2 i]
    rw [hprod] at hcomp
    exact hcomp
  ·
    intro u hu
    have h1 := hΦAJ (Ξ u) (hΞr u hu)
    rw [hkeyσ u (hsrcR u hu)] at h1
    have h2 : (fun i => Ψ i u - Ψ i cW) = fun i => Φ i (Ξ u) - Φ i ξ := by
      funext i; simp only [hΨ, hΞc]
    rw [h2]
    exact h1

end

end S_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice
end P2MW
export P2MW.S_AlgebraicCurve_exists_ball_abelJacobiVec_restrictAlong_sub_sub_mem_pathPeriodLattice (solution)
