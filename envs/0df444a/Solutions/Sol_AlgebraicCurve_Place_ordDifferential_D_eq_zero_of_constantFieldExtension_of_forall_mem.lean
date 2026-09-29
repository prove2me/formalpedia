-- Prove2me | solution 1 for AlgebraicCurve.Place.ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/22154d20-3d67-55c3-b21d-1580d9a28ea5

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_localUnitDerivativeRegular_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

open AlgebraicCurve

namespace W7XNewPlaces

section Toolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem one_le_ord_of_mem_of_inv_not_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∉ v.toValuationSubring) : 1 ≤ v.ord f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have h0 := ord_nonneg_of_mem v h1
  by_contra hlt
  have hz : v.ord f = 0 := by omega
  apply h2
  have hmul : ((u : v.toValuationSubring) : F) *
      (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [hu, hz, zpow_zero, mul_one, ← eq_inv_of_mul_eq_one_right hmul]
  exact SetLike.coe_mem _

theorem mem_iff_ord_nonneg (f : F) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  refine ⟨ord_nonneg_of_mem v, fun h => ?_⟩
  by_contra hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hmem
  have := one_le_ord_of_mem_of_inv_not_mem v hinv (by simpa using hmem)
  rw [v.ord_inv] at this
  omega

theorem irreducible_unifElt :
    Irreducible (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

theorem coe_unifElt :
    ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)
      = v.uniformizer := rfl

theorem uniformizer_mem : v.uniformizer ∈ v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose.2

theorem ord_eq_zero_of_isUnit {a : v.toValuationSubring} (ha : IsUnit a) : v.ord (a : F) = 0 := by
  obtain ⟨u, rfl⟩ := ha
  exact v.ord_coe_unit u

theorem mem_maximalIdeal_of_not_isUnit {a : v.toValuationSubring} (ha : ¬IsUnit a) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem not_isUnit_of_mem_maximalIdeal {a : v.toValuationSubring}
    (ha : a ∈ IsLocalRing.maximalIdeal v.toValuationSubring) : ¬IsUnit a := by
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha

theorem mul_uniformizer_mem_maximalIdeal {d : F} (hd : d ∈ v.toValuationSubring) :
    (⟨d * v.uniformizer, mul_mem hd (uniformizer_mem v)⟩ : v.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [(irreducible_unifElt v).maximalIdeal_eq, Ideal.mem_span_singleton']
  exact ⟨⟨d, hd⟩, Subtype.ext rfl⟩

end Toolkit

section BasisD

open scoped Polynomial
open KaehlerDifferential TensorProduct IntermediateField

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem finiteDimensional_adjoin_of_transcendental {L F : Type*} [Field L] [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {f : F} (hf : Transcendental L f) :
    FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F := by
  classical
  obtain ⟨x, -, hxfin⟩ := hF
  set Ex := IntermediateField.adjoin L ({x} : Set F) with hEx
  set Ef := IntermediateField.adjoin L ({f} : Set F) with hEf
  haveI := hxfin
  haveI halgx : Algebra.IsAlgebraic (Algebra.adjoin L ({x} : Set F)) F := by
    haveI : Algebra.IsAlgebraic Ex F := Algebra.IsAlgebraic.of_finite Ex F
    exact Algebra.IsAlgebraic.trans (Algebra.adjoin L ({x} : Set F)) Ex F
  have htr : Algebra.trdeg L F ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk L ({x} : Set F)
    simpa using h
  have hind : AlgebraicIndependent L ((↑) : ({f} : Set F) → F) := by
    haveI : Subsingleton ({f} : Set F) := Set.subsingleton_coe _ |>.mpr (Set.subsingleton_singleton)
    exact (algebraicIndependent_singleton_iff (⟨f, Set.mem_singleton f⟩ : ({f} : Set F))).mpr hf
  have hB : IsTranscendenceBasis L ((↑) : ({f} : Set F) → F) :=
    hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  haveI halg : Algebra.IsAlgebraic Ef F := by
    have h := hB.isAlgebraic_field
    rwa [Subtype.range_coe] at h
  let bx := Module.finBasis Ex F
  let T : Set F := insert x (Set.range bx)
  haveI : Finite T := ((Set.finite_range bx).insert x).to_subtype
  have hT : ∀ t ∈ T, IsIntegral Ef t := fun t _ => (Algebra.IsAlgebraic.isAlgebraic t).isIntegral
  haveI hfin : FiniteDimensional Ef (IntermediateField.adjoin Ef T) :=
    IntermediateField.finiteDimensional_adjoin hT
  have htop : IntermediateField.adjoin Ef T = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hyL : y ∈ IntermediateField.adjoin L T := by
      rw [← bx.sum_repr y]
      refine sum_mem fun i _ => ?_
      rw [Algebra.smul_def]
      refine mul_mem ?_ (IntermediateField.subset_adjoin L T (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
      exact IntermediateField.adjoin.mono L _ _
        (Set.singleton_subset_iff.mpr (Set.mem_insert x _)) (bx.repr y i).2
    have hle : IntermediateField.adjoin L T ≤ (IntermediateField.adjoin Ef T).restrictScalars L :=
      IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin Ef T)
    exact hle hyL
  rw [htop] at hfin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := Ef) (E := F)).toLinearEquiv

variable (K : Type*) [Field K]

noncomputable def polyBasis : Module.Basis (Fin 1) K[X] Ω[K[X]⁄K] :=
  (Module.Basis.singleton (Fin 1) K[X]).map (KaehlerDifferential.polynomialEquiv K).symm

theorem polyBasis_zero : polyBasis K 0 = D K K[X] Polynomial.X := by
  simp [polyBasis]

noncomputable def ratFuncBasis : Module.Basis (Fin 1) (RatFunc K) Ω[(RatFunc K)⁄K] :=
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc K) (nonZeroDivisors K[X])
  ((polyBasis K).baseChange (RatFunc K)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] (RatFunc K))

theorem ratFuncBasis_zero : ratFuncBasis K 0 = D K (RatFunc K) RatFunc.X := by
  haveI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc K) (nonZeroDivisors K[X])
  simp only [ratFuncBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, polyBasis_zero,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
    RatFunc.algebraMap_X]

variable {F : Type*} [Field F] [Algebra K F]

noncomputable def towerBasis [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] : Module.Basis (Fin 1) F Ω[F⁄K] :=
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  ((ratFuncBasis K).baseChange F).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (RatFunc K) F)

theorem towerBasis_zero [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] :
    towerBasis K (F := F) 0 = D K F (algebraMap (RatFunc K) F RatFunc.X) := by
  haveI : Algebra.FormallyEtale (RatFunc K) F := Algebra.FormallyEtale.of_isSeparable _ _
  simp only [towerBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply, ratFuncBasis_zero,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

theorem exists_basis_D (F : Type*) [Field F] [Algebra K F] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {t : F} (ht : Transcendental K t) :
    ∃ b : Module.Basis (Fin 1) F (Ω[F⁄K]), b 0 = D K F t := by
  haveI hfin : FiniteDimensional K⟮t⟯ F := finiteDimensional_adjoin_of_transcendental hfg ht
  haveI : CharZero K⟮t⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮t⟯).injective
  haveI : Algebra.IsSeparable K⟮t⟯ F := Algebra.IsSeparable.of_integral K⟮t⟯ F
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  refine ⟨towerBasis K, ?_⟩
  rw [towerBasis_zero]
  show D K F (algebraMap K⟮t⟯ F (e RatFunc.X)) = D K F t
  congr 1
  exact RatFunc.algEquivOfTranscendental_X t ht

theorem D_ne_zero_of_transcendental (F : Type*) [Field F] [Algebra K F] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {t : F} (ht : Transcendental K t) : D K F t ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_basis_D K F hfg ht
  rw [← hb]
  exact b.ne_zero 0

end BasisD

section Coeff

open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

noncomputable def coeffLin (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    Ω[F⁄K] →ₗ[F] F where
  toFun := w.differentialCoeff
  map_add' ω₁ ω₂ := w.differentialCoeff_unique
    (by rw [add_smul, w.differentialCoeff_smul_dCoord, w.differentialCoeff_smul_dCoord])
  map_smul' c ω := by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact w.differentialCoeff_smul c ω

@[scoped simp]
theorem coeffLin_apply (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] (ω : Ω[F⁄K]) :
    coeffLin w ω = w.differentialCoeff ω := rfl

noncomputable def coeffDer (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    Derivation K F F :=
  (coeffLin w).compDer (D K F)

@[scoped simp]
theorem coeffDer_apply (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] (f : F) :
    coeffDer w f = w.differentialCoeff (D K F f) := rfl

theorem coeffDer_uniformizer (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    coeffDer w w.uniformizer = 1 := by
  rw [coeffDer_apply, ← Place.dCoord_eq, w.differentialCoeff_dCoord]

theorem differentialCoeff_D_mem [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [∀ w : Place K F, w.DCoordGenerates] (w : Place K F) {z : F}
    (hz : z ∈ w.toValuationSubring) :
    w.differentialCoeff (D K F z) ∈ w.toValuationSubring := by

  have hunit : ∀ u : F, u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (D K F u) ∈ w.toValuationSubring := by
    intro u hu0 hu
    rcases localUnitDerivativeRegular_of_isCurveOver w u hu0 hu with h | h
    · rw [h]; exact zero_mem _
    · exact (mem_iff_ord_nonneg w _).2 h
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [← coeffDer_apply, map_zero]; exact zero_mem _
  by_cases hzu : w.ord z = 0
  · exact hunit z hz0 hzu
  have h1 : 1 ≤ w.ord z := by have := ord_nonneg_of_mem w hz; omega
  have hzmax : (⟨z, hz⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    mem_maximalIdeal_of_not_isUnit w fun hu => by
      have := ord_eq_zero_of_isUnit w hu; simp only at this; omega
  have hu : IsUnit (1 - (⟨z, hz⟩ : w.toValuationSubring)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hzmax
  have hu0 : (1 - z : F) ≠ 0 := by
    intro h
    apply hu.ne_zero
    exact Subtype.ext h
  have huord : w.ord (1 - z) = 0 := ord_eq_zero_of_isUnit w hu
  have key : w.differentialCoeff (D K F z) = -w.differentialCoeff (D K F (1 - z)) := by
    rw [← coeffDer_apply, ← coeffDer_apply, map_sub, Derivation.map_one_eq_zero, zero_sub,
      neg_neg]
  rw [key]
  exact neg_mem (hunit _ hu0 huord)

end Coeff

section OrdDrop

open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem isUnit_natCast [CharZero K] (w : Place K F) (n : ℕ) (hn : n ≠ 0) :
    IsUnit (⟨((n : ℕ) : F), natCast_mem w.toValuationSubring n⟩ : w.toValuationSubring) := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hne : ((n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hinv_mem : ((n : ℕ) : F)⁻¹ ∈ w.toValuationSubring := by
    have h : ((n : ℕ) : F)⁻¹ = algebraMap K F ((n : K)⁻¹) := by
      rw [map_inv₀, map_natCast]
    rw [h]
    exact w.algebraMap_mem' _
  refine isUnit_iff_exists_inv.2 ⟨⟨((n : ℕ) : F)⁻¹, hinv_mem⟩, ?_⟩
  apply Subtype.ext
  rw [MulMemClass.coe_mul, OneMemClass.coe_one]
  exact mul_inv_cancel₀ hne

theorem coeffDer_of_one_le_ord [CharZero K] [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [∀ w : Place K F, w.DCoordGenerates] (w : Place K F) {α : F} (hα0 : α ≠ 0)
    (hα : 1 ≤ w.ord α) :
    coeffDer w α ≠ 0 ∧ w.ord (coeffDer w α) = w.ord α - 1 := by
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hα0 (irreducible_unifElt w)
  rw [coe_unifElt] at hu
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = w.ord α := ⟨(w.ord α).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hαeq : α = ((u : w.toValuationSubring) : F) * w.uniformizer ^ (m + 1) := by
    rw [hu, ← hn, zpow_natCast]
  set d := coeffDer w ((u : w.toValuationSubring) : F) with hd_def
  have hd_mem : d ∈ w.toValuationSubring :=
    differentialCoeff_D_mem w (u : w.toValuationSubring).2

  set β : F := ((m + 1 : ℕ) : F) * ((u : w.toValuationSubring) : F) + d * w.uniformizer
    with hβ_def
  have hδ : coeffDer w α = w.uniformizer ^ m * β := by
    rw [hαeq, Derivation.leibniz, Derivation.leibniz_pow, coeffDer_uniformizer, hβ_def]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, mul_one]
    ring
  have hβ_mem : β ∈ w.toValuationSubring :=
    add_mem (mul_mem (natCast_mem _ _) (u : w.toValuationSubring).2)
      (mul_mem hd_mem (uniformizer_mem w))
  have hβ_unit : IsUnit (⟨β, hβ_mem⟩ : w.toValuationSubring) := by
    by_contra hnu
    have hmax := mem_maximalIdeal_of_not_isUnit w hnu
    have hprod := mul_uniformizer_mem_maximalIdeal w hd_mem
    have hnu_unit : IsUnit ((⟨((m + 1 : ℕ) : F), natCast_mem w.toValuationSubring _⟩ : w.toValuationSubring)
        * (u : w.toValuationSubring)) :=
      (isUnit_natCast w (m + 1) (Nat.succ_ne_zero m)).mul u.isUnit
    have heq : (⟨((m + 1 : ℕ) : F), natCast_mem w.toValuationSubring _⟩ : w.toValuationSubring)
        * (u : w.toValuationSubring)
        = ⟨β, hβ_mem⟩ - ⟨d * w.uniformizer, mul_mem hd_mem (uniformizer_mem w)⟩ := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, hβ_def]
      ring
    refine not_isUnit_of_mem_maximalIdeal w ?_ hnu_unit
    rw [heq]
    exact sub_mem hmax hprod
  have hβ_ord' := ord_eq_zero_of_isUnit w hβ_unit
  have hβ_ord : w.ord β = 0 := by simpa only using hβ_ord'
  have hβ0 : β ≠ 0 := by
    intro h
    apply hβ_unit.ne_zero
    exact Subtype.ext h
  have hϖ0 : w.uniformizer ^ m ≠ 0 := pow_ne_zero _ w.uniformizer_ne_zero
  refine ⟨by rw [hδ]; exact mul_ne_zero hϖ0 hβ0, ?_⟩
  rw [hδ, w.ord_mul hϖ0 hβ0, hβ_ord, add_zero, ← zpow_natCast, w.ord_zpow, w.ord_uniformizer,
    mul_one, ← hn]
  push_cast
  ring

end OrdDrop

section MainTheorem

open KaehlerDifferential IntermediateField

theorem ordDifferential_D_eq_zero_of_forall_mem (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (w : Place K' F') (hw : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring)
    {x : F} (hx : Transcendental K' (algebraMap F F' x)) :
    w.differentialCoeff (KaehlerDifferential.D K' F' (algebraMap F F' x)) ≠ 0 ∧
      w.ordDifferential (KaehlerDifferential.D K' F' (algebraMap F F' x)) = 0 := by
  classical

  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : Algebra.EssFiniteType K' F' := by
    obtain ⟨y, hy, hyfin⟩ := hfg'
    exact essFiniteType_of_transcendental_of_finiteDimensional hy hyfin
  haveI hDC' : ∀ w : Place K' F', w.DCoordGenerates := dCoordGenerates_of_isCurveOver

  have hxK : Transcendental K x := fun halg =>
    hx ((halg.algHom (IsScalarTower.toAlgHom K F F')).tower_top K')

  set x' := algebraMap F F' x with hx'_def
  set c := w.differentialCoeff (D K' F' x') with hc_def
  have hcδ : coeffDer w x' = c := rfl

  have hDx' : D K' F' x' ≠ 0 := D_ne_zero_of_transcendental K' F' hfg' hx
  have hc0 : c ≠ 0 := by
    intro h
    apply hDx'
    rw [← w.differentialCoeff_smul_dCoord (D K' F' x'), ← hc_def, h, zero_smul]
  refine ⟨hc0, ?_⟩
  show w.ord c = 0

  have hc_mem : c ∈ w.toValuationSubring := differentialCoeff_D_mem w (hw x)
  have hc_nonneg : 0 ≤ w.ord c := ord_nonneg_of_mem w hc_mem

  obtain ⟨b, hb⟩ := exists_basis_D K F hfg hxK
  let d₀ : Derivation K F F := (b.coord 0).compDer (D K F)
  have hDf : ∀ f : F, D K F f = d₀ f • D K F x := fun f => by
    conv_lhs => rw [← b.sum_repr (D K F f)]
    rw [Fin.sum_univ_one, hb]
    rfl

  have hkey : ∀ f : F, coeffDer w (algebraMap F F' f) = algebraMap F F' (d₀ f) * c := by
    intro f
    have h1 : D K' F' (algebraMap F F' f) = algebraMap F F' (d₀ f) • D K' F' x' := by
      rw [← KaehlerDifferential.map_D K K' F F' f, hDf, map_smul,
        algebra_compatible_smul F' (d₀ f), KaehlerDifferential.map_D]
    rw [coeffDer_apply, h1, w.differentialCoeff_smul]

  set S : Subalgebra K' F' := Algebra.adjoin K' (Set.range (algebraMap F F')) with hS_def
  let Ow : Subalgebra K' F' :=
    { w.toValuationSubring.toSubring with
      algebraMap_mem' := fun r => w.algebraMap_mem' r }
  have hSO : S ≤ Ow := Algebra.adjoin_le (by rintro _ ⟨f, rfl⟩; exact hw f)
  have hSmem : ∀ z ∈ S, z ∈ w.toValuationSubring := fun z hz => hSO hz
  have hstab : ∀ z ∈ S, ∃ t ∈ S, coeffDer w z = t * c := by
    intro z hz
    refine Algebra.adjoin_induction (p := fun z _ => ∃ t ∈ S, coeffDer w z = t * c)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨f, rfl⟩
      exact ⟨algebraMap F F' (d₀ f), Algebra.subset_adjoin ⟨d₀ f, rfl⟩, hkey f⟩
    · intro r
      exact ⟨0, zero_mem _, by rw [Derivation.map_algebraMap, zero_mul]⟩
    · rintro a b - - ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
      exact ⟨ta + tb, add_mem hta htb, by rw [map_add, ha, hb, add_mul]⟩
    · rintro a b haS hbS ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
      refine ⟨a * tb + b * ta, add_mem (mul_mem haS htb) (mul_mem hbS hta), ?_⟩
      rw [Derivation.leibniz, ha, hb, smul_eq_mul, smul_eq_mul]
      ring

  by_contra hcne
  have hc1 : 1 ≤ w.ord c := by omega
  set k : ℤ := w.ord c + 1 with hk_def

  have hdiv : ∀ n : ℕ, ∀ z ∈ S, z ≠ 0 → w.ord z = n → k ∣ (n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hzS hz0 hzn
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · exact dvd_zero k
      have hz1 : 1 ≤ w.ord z := by omega
      obtain ⟨hδ0, hδord⟩ := coeffDer_of_one_le_ord w hz0 hz1
      obtain ⟨t, htS, ht⟩ := hstab z hzS
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hδ0 (by rw [ht, zero_mul])
      have htord : w.ord t = n - k := by
        have h := hδord
        rw [ht, w.ord_mul ht0 hc0, hzn] at h
        omega
      have ht_nonneg : 0 ≤ w.ord t := ord_nonneg_of_mem w (hSmem t htS)
      have hlt : (w.ord t).toNat < n := by omega
      have hih := ih _ hlt t htS ht0 (Int.toNat_of_nonneg ht_nonneg).symm
      rw [Int.toNat_of_nonneg ht_nonneg, htord] at hih
      simpa using hih
  have hdiv' : ∀ z ∈ S, z ≠ 0 → k ∣ w.ord z := fun z hzS hz0 => by
    have h0 : 0 ≤ w.ord z := ord_nonneg_of_mem w (hSmem z hzS)
    have := hdiv (w.ord z).toNat z hzS hz0 (Int.toNat_of_nonneg h0).symm
    rwa [Int.toNat_of_nonneg h0] at this

  have hϖmem : w.uniformizer ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
    rw [hgen]; exact IntermediateField.mem_top
  rw [IntermediateField.mem_adjoin_iff_div] at hϖmem
  obtain ⟨r, hr, s, hs, hrs⟩ := hϖmem
  have hϖ0 := w.uniformizer_ne_zero
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hϖ0 (by rw [hrs, div_zero])
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hϖ0 (by rw [hrs, zero_div])
  have hord1 : w.ord r - w.ord s = 1 := by
    rw [← w.ord_uniformizer, hrs, div_eq_mul_inv, w.ord_mul hr0 (inv_ne_zero hs0), w.ord_inv]
    ring
  have hk1 : k ∣ 1 := by
    rw [← hord1]
    exact dvd_sub (hdiv' r hr hr0) (hdiv' s hs hs0)
  have hk2 : 2 ≤ k := by omega
  have := Int.eq_one_of_dvd_one (by omega) hk1
  omega

end MainTheorem

end W7XNewPlaces
p2m_reactivate "P2MW.S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem.W7XNewPlaces"

open W7XNewPlaces in
theorem solution (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (w : Place K' F') (hw : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring)
    {x : F} (hx : Transcendental K' (algebraMap F F' x)) :
    w.differentialCoeff (KaehlerDifferential.D K' F' (algebraMap F F' x)) ≠ 0 ∧
      w.ordDifferential (KaehlerDifferential.D K' F' (algebraMap F F' x)) = 0 :=
  ordDifferential_D_eq_zero_of_forall_mem K F K' F' hfg hfg' hgen w hw hx

end S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem
end P2MW
export P2MW.S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem (solution)
