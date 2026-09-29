-- Prove2me | solution 1 for AlgebraicCurve.Place.readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/36d2407f-6f8b-59d0-8a03-d884e66f6e2f

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_Place_analyticAt_evalAt_extChartAt_symm_of_mem
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv.AlgebraicCurve"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.FiniteResidue Place.ord_zero HasPrincipalDivisors HasPrincipalDivisors.exists_divisor Place.FiniteResidue.finite Place.algebraMap_mem' IsCurveOver Place.evalAt Place.ord_dCoordFn Place.dCoord_eq_D_dCoordFn Place.chartRead_apply Place.readDifferential_apply Place.analyticAt_evalAt_extChartAt_symm_of_mem dCoordGenerates_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional localUnitDerivativeRegular_of_isCurveOver"
namespace ReadDifferentialProof
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

theorem ord_pos_of_residue_eq_zero (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0) (hf0 : f ≠ 0) :
    0 < v.ord f := by
  have ha : (⟨f, hf⟩ : v.toValuationSubring) ≠ 0 := by
    intro h
    apply hf0
    have := congrArg Subtype.val h
    exact this
  have hu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    rw [IsLocalRing.residue_eq_zero_iff] at hres
    exact (IsLocalRing.mem_maximalIdeal _).1 hres
  have key := ord_pos_of_not_isUnit v ha hu
  exact key

theorem ord_neg_of_not_mem (v : Place K F) {f : F} (hf : f ∉ v.toValuationSubring) :
    v.ord f < 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf (zero_mem _)
  have hinv : f⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have hu : ¬IsUnit (⟨f⁻¹, hinv⟩ : v.toValuationSubring) := by
    intro h
    obtain ⟨u, hu⟩ := h
    apply hf
    have : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val = f := by
      have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).val * f⁻¹ = 1 := by
        have := congrArg (fun a : v.toValuationSubring => (a : F)) (u.inv_mul)
        simpa [hu] using this
      have := congrArg (· * f) h1
      simpa [inv_mul_cancel_right₀ hf0, mul_assoc, inv_mul_cancel₀ hf0] using this
    rw [← this]
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

theorem finite_setOf_not_mem [HasPrincipalDivisors K F] {f : F} (hf0 : f ≠ 0) :
    {w : Place K F | f ∉ w.toValuationSubring}.Finite := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  refine (D.support.finite_toSet).subset fun w hw => ?_
  have h := ord_neg_of_not_mem w hw
  rw [← hD w] at h
  simpa [Finsupp.mem_support_iff] using h.ne

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

theorem evalAt_algebraMap' (w : Place K F) (a : K) : w.evalAt (algebraMap K F a) = a := by
  rw [w.evalAt_of_mem (w.algebraMap_mem' a), residue_algebraMap, w.residueInv_algebraMap]

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

theorem evalAt_sub_algebraMap (w : Place K F) (hw : w.IsRational) {f : F}
    (hf : f ∈ w.toValuationSubring) (a : K) :
    w.evalAt (f - algebraMap K F a) = w.evalAt f - a := by
  have hfa : f - algebraMap K F a ∈ w.toValuationSubring := sub_mem hf (w.algebraMap_mem' a)
  apply w.algebraMap_residueField_injective
  rw [w.algebraMap_evalAt hw hfa, map_sub, w.algebraMap_evalAt hw hf, ← residue_algebraMap w a,
    ← map_sub]
  rfl

theorem residue_sub_evalAt_eq_zero (w : Place K F) (hw : w.IsRational) {f : F}
    (hf : f ∈ w.toValuationSubring) :
    IsLocalRing.residue w.toValuationSubring
        (⟨f - algebraMap K F (w.evalAt f), sub_mem hf (w.algebraMap_mem' _)⟩ :
          w.toValuationSubring) = 0 := by
  have hfa : f - algebraMap K F (w.evalAt f) ∈ w.toValuationSubring :=
    sub_mem hf (w.algebraMap_mem' _)
  rw [← w.algebraMap_evalAt hw hfa, evalAt_sub_algebraMap w hw hf, sub_self, map_zero]

theorem exists_eq_algebraMap_add_mul (v : Place K F) (hv : v.IsRational) {π : F}
    (hπ : v.ord π = 1) {g : F} (hg : g ∈ v.toValuationSubring) :
    ∃ r ∈ v.toValuationSubring, g = algebraMap K F (v.evalAt g) + π * r := by
  have hg' : g - algebraMap K F (v.evalAt g) ∈ v.toValuationSubring :=
    sub_mem hg (v.algebraMap_mem' _)
  by_cases h0 : g - algebraMap K F (v.evalAt g) = 0
  · exact ⟨0, zero_mem _, by rw [mul_zero, add_zero]; exact sub_eq_zero.1 h0⟩
  have hord : 0 < v.ord (g - algebraMap K F (v.evalAt g)) :=
    ord_pos_of_residue_eq_zero v hg' (residue_sub_evalAt_eq_zero v hv hg) h0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ
  refine ⟨π⁻¹ * (g - algebraMap K F (v.evalAt g)), mem_of_ord_nonneg v ?_, ?_⟩
  · rw [v.ord_mul (inv_ne_zero hπ0) h0, v.ord_inv, hπ]
    omega
  · rw [← mul_assoc, mul_inv_cancel₀ hπ0, one_mul, add_sub_cancel]

theorem D_eq_differentialCoeff_smul (v : Place K F) [v.DCoordGenerates] (x : F) :
    KaehlerDifferential.D K F x =
      v.differentialCoeff (KaehlerDifferential.D K F x) • KaehlerDifferential.D K F v.dCoordFn := by
  rw [← Place.dCoord_eq_D_dCoordFn]
  exact (v.differentialCoeff_smul_dCoord _).symm

theorem differentialCoeff_D_algebraMap_add_mul (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] (a : K) (r : F) :
    v.differentialCoeff (KaehlerDifferential.D K F (algebraMap K F a + v.dCoordFn * r)) =
      v.dCoordFn * v.differentialCoeff (KaehlerDifferential.D K F r) + r := by
  apply v.differentialCoeff_unique
  rw [map_add, Derivation.map_algebraMap, zero_add, Derivation.leibniz, add_smul, ← smul_smul,
    Place.dCoord_eq_D_dCoordFn, ← D_eq_differentialCoeff_smul v r]

theorem differentialCoeff_D_one_sub (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (r : F) :
    v.differentialCoeff (KaehlerDifferential.D K F (1 - r)) =
      -v.differentialCoeff (KaehlerDifferential.D K F r) := by
  rw [map_sub, Derivation.map_one_eq_zero, zero_sub, ← neg_one_smul F (KaehlerDifferential.D K F r),
    v.differentialCoeff_smul, neg_one_mul]

theorem differentialCoeff_D_mem [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ w : Place K F, w.DCoordGenerates] (v : Place K F) {r : F}
    (hr : r ∈ v.toValuationSubring) :
    v.differentialCoeff (KaehlerDifferential.D K F r) ∈ v.toValuationSubring := by
  have key : ∀ a : v.toValuationSubring, IsUnit a →
      v.differentialCoeff (KaehlerDifferential.D K F (a : F)) ∈ v.toValuationSubring := by
    intro a ha
    obtain ⟨u, rfl⟩ := ha
    have hu0 : ((u : v.toValuationSubring) : F) ≠ 0 := by
      simp [ne_eq, ZeroMemClass.coe_eq_zero]
    rcases localUnitDerivativeRegular_of_isCurveOver v _ hu0 (v.ord_coe_unit u) with h | h
    · rw [h]
      exact zero_mem _
    · exact mem_of_ord_nonneg v h
  by_cases hunit : IsUnit (⟨r, hr⟩ : v.toValuationSubring)
  · exact key ⟨r, hr⟩ hunit
  · have h1 := key (1 - ⟨r, hr⟩) (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      (mem_nonunits_iff.2 hunit))
    have hcoe : (((1 - ⟨r, hr⟩ : v.toValuationSubring) : v.toValuationSubring) : F) = 1 - r :=
      rfl
    rw [hcoe, differentialCoeff_D_one_sub] at h1
    simpa using neg_mem h1

theorem dCoordFn_mem (v : Place K F) : v.dCoordFn ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (by rw [Place.ord_dCoordFn]; exact zero_le_one)

theorem dCoordFn_ne_zero (v : Place K F) : v.dCoordFn ≠ 0 := by
  intro h
  have := Place.ord_dCoordFn v
  rw [h, Place.ord_zero] at this
  exact zero_ne_one this

end Algebra

section Complex

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

variable (F) in

def ChartCompatible : Prop :=
  ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
    MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) ∧
    meromorphicOrderAt
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
        (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)

theorem eventually_ne_nhdsWithin (v : Place ℂ F) :
    ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v), (extChartAt 𝓘(ℂ, ℂ) v).symm z ≠ v := by
  have htgt : ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v), z ∈ (extChartAt 𝓘(ℂ, ℂ) v).target :=
    eventually_nhdsWithin_of_eventually_nhds (extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) v)
  filter_upwards [htgt, self_mem_nhdsWithin] with z hz hne
  intro h
  apply hne
  have := (extChartAt 𝓘(ℂ, ℂ) v).right_inv hz
  rw [h] at this
  exact this.symm

def defect (v : Place ℂ F) (x : F) : ℂ → ℂ := fun z =>
  deriv (v.chartRead x) z - v.readDifferential (KaehlerDifferential.D ℂ F x) z

theorem defect_apply (v : Place ℂ F) (x : F) (z : ℂ) :
    defect v x z = deriv (v.chartRead x) z -
      v.chartRead (v.differentialCoeff (KaehlerDifferential.D ℂ F x)) z *
        deriv (v.chartRead v.dCoordFn) z := rfl

theorem readDifferential_smul_D_eq [IsCurveOver ℂ F] (v : Place ℂ F) [v.DCoordGenerates]
    (h : F) {g : F} {z : ℂ}
    (hh : h ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring)
    (hc : v.differentialCoeff (KaehlerDifferential.D ℂ F g) ∈
      ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring)
    (hz : defect v g z = 0) :
    v.readDifferential (h • KaehlerDifferential.D ℂ F g) z =
      v.chartRead h z * deriv (v.chartRead g) z := by
  rw [defect_apply, sub_eq_zero] at hz
  rw [Place.readDifferential_apply, v.differentialCoeff_smul, hz]
  simp only [Place.chartRead_apply]
  rw [evalAt_mul _ (isRational_of_isAlgClosed _) hh hc, mul_assoc]

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)]

theorem eventually_mem_nhds (v : Place ℂ F) {f : F} (hf : f ∈ v.toValuationSubring) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring := by
  by_cases hf0 : f = 0
  · exact Filter.Eventually.of_forall fun z => by rw [hf0]; exact zero_mem _
  have hopen : IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring} := by
    have h := (finite_setOf_not_mem (K := ℂ) hf0).isClosed.isOpen_compl
    convert h using 1
    ext w
    simp
  have hmem : (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v) ∈
      {w : Place ℂ F | f ∈ w.toValuationSubring} := by
    rw [extChartAt_to_inv]
    exact hf
  exact (continuousAt_extChartAt_symm v).preimage_mem_nhds (hopen.mem_nhds hmem)

theorem eventually_mem_nhdsWithin (v : Place ℂ F) (f : F) :
    ∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring := by
  by_cases hf0 : f = 0
  · exact Filter.Eventually.of_forall fun z => by rw [hf0]; exact zero_mem _
  have hopen : IsOpen {w : Place ℂ F | f ∈ w.toValuationSubring ∨ w = v} := by
    have hfin : {w : Place ℂ F | f ∈ w.toValuationSubring ∨ w = v}ᶜ.Finite :=
      (finite_setOf_not_mem (K := ℂ) hf0).subset fun w hw => by
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or] at hw
        exact hw.1
    have h := hfin.isClosed.isOpen_compl
    rwa [compl_compl] at h
  have hmem : (extChartAt 𝓘(ℂ, ℂ) v).symm (extChartAt 𝓘(ℂ, ℂ) v v) ∈
      {w : Place ℂ F | f ∈ w.toValuationSubring ∨ w = v} := by
    rw [extChartAt_to_inv]
    exact Or.inr rfl
  have h1 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
      f ∈ ((extChartAt 𝓘(ℂ, ℂ) v).symm z).toValuationSubring ∨
        (extChartAt 𝓘(ℂ, ℂ) v).symm z = v :=
    (continuousAt_extChartAt_symm v).preimage_mem_nhds (hopen.mem_nhds hmem)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds h1, eventually_ne_nhdsWithin v]
    with z hz hne
  exact hz.resolve_right hne

theorem analyticAt_chartRead (hF : ChartCompatible F) (v : Place ℂ F) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    AnalyticAt ℂ (v.chartRead f) (extChartAt 𝓘(ℂ, ℂ) v v) :=
  Place.analyticAt_evalAt_extChartAt_symm_of_mem F hF v hf

theorem analyticOrderAt_chartRead_dCoordFn (hF : ChartCompatible F) (v : Place ℂ F) :
    analyticOrderAt (v.chartRead v.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) v v) = 1 := by
  have han := analyticAt_chartRead hF v (dCoordFn_mem v)
  have hord := (hF v.dCoordFn (dCoordFn_ne_zero v) v).2
  rw [Place.ord_dCoordFn] at hord
  change meromorphicOrderAt (v.chartRead v.dCoordFn) _ = _ at hord
  rw [han.meromorphicOrderAt_eq] at hord
  cases h : analyticOrderAt (v.chartRead v.dCoordFn) (extChartAt 𝓘(ℂ, ℂ) v v)
  · rw [h] at hord
    simp at hord
  · rename_i n
    rw [h] at hord
    simp only [ENat.map_coe] at hord
    have h1 : (n : ℤ) = 1 := by exact_mod_cast hord
    have hn : n = 1 := by exact_mod_cast h1
    rw [hn]
    rfl

variable [Algebra.EssFiniteType ℂ F] [∀ w : Place ℂ F, w.DCoordGenerates]

theorem analyticAt_defect (hF : ChartCompatible F) (v : Place ℂ F) {g : F}
    (hg : g ∈ v.toValuationSubring) :
    AnalyticAt ℂ (defect v g) (extChartAt 𝓘(ℂ, ℂ) v v) := by
  have h1 := (analyticAt_chartRead hF v hg).deriv
  have h2 := analyticAt_chartRead hF v (differentialCoeff_D_mem v hg)
  have h3 := (analyticAt_chartRead hF v (dCoordFn_mem v)).deriv
  exact h1.sub (h2.mul h3)

theorem defect_eventuallyEq_mul (hF : ChartCompatible F) (v : Place ℂ F) (a : ℂ) {r : F}
    (hr : r ∈ v.toValuationSubring) :
    defect v (algebraMap ℂ F a + v.dCoordFn * r) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) v v)]
      fun z => v.chartRead v.dCoordFn z * defect v r z := by
  have hπ := dCoordFn_mem v
  have hcr := differentialCoeff_D_mem v hr

  have eπ := eventually_mem_nhds v hπ
  have er := eventually_mem_nhds v hr
  have ecr := eventually_mem_nhds v hcr

  have hRg : v.chartRead (algebraMap ℂ F a + v.dCoordFn * r) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) v v)]
      fun z => a + v.chartRead v.dCoordFn z * v.chartRead r z := by
    filter_upwards [eπ, er] with z hzπ hzr
    simp only [Place.chartRead_apply]
    rw [evalAt_add _ (isRational_of_isAlgClosed _) (Place.algebraMap_mem' _ a) (mul_mem hzπ hzr),
      evalAt_algebraMap', evalAt_mul _ (isRational_of_isAlgClosed _) hzπ hzr]
  have hRc : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
      v.chartRead (v.differentialCoeff
          (KaehlerDifferential.D ℂ F (algebraMap ℂ F a + v.dCoordFn * r))) z =
        v.chartRead v.dCoordFn z *
            v.chartRead (v.differentialCoeff (KaehlerDifferential.D ℂ F r)) z +
          v.chartRead r z := by
    filter_upwards [eπ, er, ecr] with z hzπ hzr hzc
    simp only [Place.chartRead_apply]
    rw [differentialCoeff_D_algebraMap_add_mul,
      evalAt_add _ (isRational_of_isAlgClosed _) (mul_mem hzπ hzc) hzr,
      evalAt_mul _ (isRational_of_isAlgClosed _) hzπ hzc]

  have aπ := (analyticAt_chartRead hF v hπ).eventually_analyticAt
  have ar := (analyticAt_chartRead hF v hr).eventually_analyticAt
  have hderiv : deriv (v.chartRead (algebraMap ℂ F a + v.dCoordFn * r)) =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) v v)]
      fun z => deriv (v.chartRead v.dCoordFn) z * v.chartRead r z +
        v.chartRead v.dCoordFn z * deriv (v.chartRead r) z := by
    filter_upwards [hRg.deriv, aπ, ar] with z hz hzπ hzr
    rw [hz]
    exact ((hzπ.differentiableAt.hasDerivAt.mul hzr.differentiableAt.hasDerivAt).const_add
      a).deriv
  filter_upwards [hderiv, hRc] with z h1 h2
  simp only [defect_apply]
  rw [h1, h2]
  ring

theorem defect_eventuallyEq_pow_mul (hF : ChartCompatible F) (v : Place ℂ F) (N : ℕ) {g : F}
    (hg : g ∈ v.toValuationSubring) :
    ∃ E : ℂ → ℂ, AnalyticAt ℂ E (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      defect v g =ᶠ[𝓝 (extChartAt 𝓘(ℂ, ℂ) v v)]
        fun z => v.chartRead v.dCoordFn z ^ N * E z := by
  induction N generalizing g with
  | zero =>
    refine ⟨defect v g, analyticAt_defect hF v hg, Filter.Eventually.of_forall fun z => ?_⟩
    simp only [pow_zero, one_mul]
  | succ N ih =>
    obtain ⟨r, hr, hgr⟩ :=
      exists_eq_algebraMap_add_mul v (isRational_of_isAlgClosed v) (Place.ord_dCoordFn v) hg
    obtain ⟨E, hE, hΔr⟩ := ih hr
    refine ⟨E, hE, ?_⟩
    have hstep := defect_eventuallyEq_mul hF v (v.evalAt g) hr
    rw [← hgr] at hstep
    filter_upwards [hstep, hΔr] with z h1 h2
    rw [h1, h2, pow_succ]
    ring

theorem defect_eventuallyEq_zero (hF : ChartCompatible F) (v : Place ℂ F) {g : F}
    (hg : g ∈ v.toValuationSubring) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v), defect v g z = 0 := by
  have hΔ := analyticAt_defect hF v hg
  apply analyticOrderAt_eq_top.1
  rw [ENat.eq_top_iff_forall_ge]
  intro N
  obtain ⟨E, hE, hΔE⟩ := defect_eventuallyEq_pow_mul hF v N hg
  obtain ⟨u, hu, -, hπu⟩ :=
    ((analyticAt_chartRead hF v (dCoordFn_mem v)).analyticOrderAt_eq_natCast).1
      (analyticOrderAt_chartRead_dCoordFn hF v)
  refine (natCast_le_analyticOrderAt hΔ).2 ⟨fun z => u z ^ N * E z, (hu.pow N).mul hE, ?_⟩
  filter_upwards [hΔE, hπu] with z h1 h2
  rw [h1, h2]
  simp only [pow_one, smul_eq_mul]
  rw [mul_pow]
  ring

end Complex

end AlgebraicCurve.ReadDifferentialProof

open AlgebraicCurve.ReadDifferentialProof in

theorem solution (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    (v : Place ℂ F) {g : F} (hg : g ∈ v.toValuationSubring) (h : F) :
    (∀ᶠ z in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) v v),
        v.readDifferential (h • KaehlerDifferential.D ℂ F g) z =
          v.chartRead h z * deriv (v.chartRead g) z) ∧
    (h ∈ v.toValuationSubring → ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) v v),
        v.readDifferential (h • KaehlerDifferential.D ℂ F g) z =
          v.chartRead h z * deriv (v.chartRead g) z) := by
  obtain ⟨x, htr, hfd⟩ := hfg
  haveI : Algebra.EssFiniteType ℂ F :=
    essFiniteType_of_transcendental_of_finiteDimensional htr hfd
  haveI : ∀ w : Place ℂ F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hF' : ChartCompatible F := hF
  have hzero := defect_eventuallyEq_zero hF' v hg
  have hc := eventually_mem_nhds v (differentialCoeff_D_mem v hg)
  refine ⟨?_, fun hh => ?_⟩
  · filter_upwards [eventually_mem_nhdsWithin v h, eventually_nhdsWithin_of_eventually_nhds hc,
      eventually_nhdsWithin_of_eventually_nhds hzero] with z h1 h2 h3
    exact readDifferential_smul_D_eq v h h1 h2 h3
  · filter_upwards [eventually_mem_nhds v hh, hc, hzero] with z h1 h2 h3
    exact readDifferential_smul_D_eq v h h1 h2 h3

end

end S_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv
end P2MW
export P2MW.S_AlgebraicCurve_Place_readDifferential_smul_D_eventuallyEq_chartRead_mul_deriv (solution)
