-- Prove2me | solution 1 for AlgebraicCurve.abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7d952903-9e94-5298-9895-711eca3e6c8b

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import Theorems.Thm_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal.AlgebraicCurve"
open scoped Manifold ContDiff Topology

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.IsPrincipal HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver HasCanonicalDivisor Place.evalAt regularDifferentials abelJacobiDiv pathPeriodLattice eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice"
namespace AbelNecessityProof
p2m_open "AlgebraicCurve"

theorem sub_mem_of_eventually_sub_mem {X M : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [AddCommGroup M] (L : AddSubgroup M) (φ : X → M)
    (h : ∀ x₀ : X, ∀ᶠ x in 𝓝 x₀, φ x - φ x₀ ∈ L) (x y : X) : φ x - φ y ∈ L := by
  let S : Set X := {x | φ x - φ y ∈ L}
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [h x] with x' hx'
    have : φ x' - φ y = (φ x' - φ x) + (φ x - φ y) := by abel
    show φ x' - φ y ∈ L
    rw [this]
    exact L.add_mem hx' hx
  have hclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    filter_upwards [h x] with x' hx' hxS
    apply hx
    have : φ x - φ y = (φ x' - φ y) - (φ x' - φ x) := by abel
    show φ x - φ y ∈ L
    rw [this]
    exact L.sub_mem hxS hx'
  have hy : y ∈ S := by
    show φ y - φ y ∈ L
    rw [sub_self]
    exact L.zero_mem
  have hS : S = Set.univ := by
    rcases isClopen_iff.1 ⟨hclosed, hopen⟩ with h0 | h1
    · exact absurd (h0 ▸ hy : y ∈ (∅ : Set X)) (Set.notMem_empty y)
    · exact h1
  have hx : x ∈ S := by rw [hS]; exact Set.mem_univ x
  exact hx

section Algebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_algebraMap (v : Place K F) {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F a, v.algebraMap_mem' a⟩, ⟨algebraMap K F a⁻¹, v.algebraMap_mem' a⁻¹⟩,
      Subtype.ext (by simp [ha]), Subtype.ext (by simp [ha])⟩
  have := v.ord_coe_unit u
  exact this

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · have h1 : (-f) = algebraMap K F (-1) * f := by simp
    rw [h1, v.ord_mul (by simp) hf, ord_algebraMap v (by simp), zero_add]

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

theorem ord_one_sub_eq_zero_of_pos (v : Place K F) {f : F} (h : 0 < v.ord f) :
    v.ord (1 - f) = 0 := by
  have hf : f ∈ v.toValuationSubring := mem_of_ord_nonneg v h.le
  have hnu : ¬IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    rintro ⟨u, hu⟩
    have := v.ord_coe_unit u
    rw [hu] at this
    exact absurd this (ne_of_gt h)
  obtain ⟨u, hu⟩ :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (mem_nonunits_iff.2 hnu)
  have := v.ord_coe_unit u
  rw [hu] at this
  exact this

theorem ord_sub_one_of_neg (v : Place K F) {f : F} (h : v.ord f < 0) :
    v.ord (f - 1) = v.ord f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h
  have hinv : 0 < v.ord f⁻¹ := by rw [v.ord_inv]; omega
  have h1 : f - 1 = f * (1 - f⁻¹) := by field_simp
  have hne : (1 - f⁻¹) ≠ 0 := by
    intro h0
    have := ord_one_sub_eq_zero_of_pos v hinv
    rw [h0] at this
    have h2 : (1 : F) = f⁻¹ := sub_eq_zero.1 h0
    rw [← h2] at hinv
    simp at hinv
  rw [h1, v.ord_mul hf0 hne, ord_one_sub_eq_zero_of_pos v hinv, add_zero]

theorem max_ord_sub_one_eq (v : Place K F) (f : F) :
    max (v.ord (f - 1)) 0 = max (v.ord (f⁻¹ - 1)) 0 := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  rcases eq_or_ne f 1 with rfl | hf1
  · simp
  have hsub : f - 1 ≠ 0 := sub_ne_zero.2 hf1
  have hkey : v.ord (f⁻¹ - 1) = v.ord (f - 1) - v.ord f := by
    have h1 : f⁻¹ - 1 = -(f - 1) * f⁻¹ := by field_simp; ring
    rw [h1, v.ord_mul (neg_ne_zero.2 hsub) (inv_ne_zero hf0), ord_neg, v.ord_inv]
    ring
  rw [hkey]
  rcases lt_trichotomy (v.ord f) 0 with hlt | heq | hgt
  · rw [ord_sub_one_of_neg v hlt]
    simp only [sub_self]
    rw [max_eq_right hlt.le, max_self]
  · rw [heq, sub_zero]
  · have h0 : v.ord (f - 1) = 0 := by
      rw [← ord_neg, neg_sub]
      exact ord_one_sub_eq_zero_of_pos v hgt
    rw [h0]
    simp only [zero_sub, max_self]
    rw [max_eq_right]
    omega

variable [HasPrincipalDivisors K F]

open Classical in

def zeroDivisor (g : F) : Divisor K F :=
  if hg : g = 0 then 0 else (HasPrincipalDivisors.exists_divisor (K := K) g hg).choose ⊔ 0

theorem zeroDivisor_apply (g : F) (v : Place K F) :
    zeroDivisor (K := K) g v = max (v.ord g) 0 := by
  classical
  unfold zeroDivisor
  split_ifs with hg
  · subst hg
    simp
  · rw [Finsupp.sup_apply, (HasPrincipalDivisors.exists_divisor (K := K) g hg).choose_spec.1 v]
    rfl

end Algebra

end AlgebraicCurve.AbelNecessityProof

open AlgebraicCurve.AbelNecessityProof in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Fin n → ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (D : Divisor ℂ F) (hD : Divisor.IsPrincipal D) :
    abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) := by
  obtain ⟨f, hf0, hDf⟩ := hD
  set b' : Fin n → Ω[F⁄ℂ] := fun i => (b i : Ω[F⁄ℂ]) with hb'
  set Λ := pathPeriodLattice b' with hΛ
  set AJ := abelJacobiDiv b' P₀ with hAJ

  let Z : F → ℂ → Divisor ℂ F := fun g t => zeroDivisor (g - algebraMap ℂ F t)
  have hZ : ∀ (g : F) (t : ℂ) (v : Place ℂ F),
      Z g t v = max (v.ord (g - algebraMap ℂ F t)) 0 := fun g t v => zeroDivisor_apply _ _

  have hconst : ∀ (g : F) (t s : ℂ), AJ (Z g t) - AJ (Z g s) ∈ Λ := fun g =>
    sub_mem_of_eventually_sub_mem Λ.toAddSubgroup (fun t => AJ (Z g t)) fun t₀ =>
      eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice F hfg hF b P₀ g (Z g) (hZ g) t₀

  have hD1 : D = Z f 0 - Z f⁻¹ 0 := by
    ext v
    rw [Finsupp.sub_apply, hZ, hZ, hDf v, map_zero, sub_zero, sub_zero, v.ord_inv]
    rcases le_total 0 (v.ord f) with h | h
    · rw [max_eq_left h, max_eq_right (by omega)]
      ring
    · rw [max_eq_right h, max_eq_left (by omega)]
      ring
  have hD2 : Z f 1 = Z f⁻¹ 1 := by
    ext v
    rw [hZ, hZ, map_one]
    exact max_ord_sub_one_eq v f
  have hsplit : AJ D = -(AJ (Z f 1) - AJ (Z f 0)) + (AJ (Z f⁻¹ 1) - AJ (Z f⁻¹ 0)) := by
    rw [hD1, map_sub, hD2]
    abel
  show AJ D ∈ Λ
  rw [hsplit]
  exact Λ.add_mem (Λ.neg_mem (hconst f 1 0)) (hconst f⁻¹ 1 0)

end

end S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal
end P2MW
export P2MW.S_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal (solution)
