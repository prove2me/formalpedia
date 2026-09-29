-- Prove2me | solution 1 for AlgebraicCurve.Divisor.isPrincipal_of_constantFieldExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c9a20cba-0fd5-58c8-831c-093b57f9c653

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ext Place.coe_algebraMap Place.ord Divisor Divisor.degree HasPrincipalDivisors Pic HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.finiteResidue mem_span_range_algebraMap_of_constantFieldExtension Place.exists_comap_algebraMap_eq_of_constantFieldExtension"
namespace W7XK1a
p2m_open "AlgebraicCurve"

section Basic

variable {k L : Type*} [Field k] [Field L] [Algebra k L] (w : Place k L)

theorem ord_nonneg_of_mem {f : L} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have h1 : w.adicValuation f ≤ 1 := by
    have h := w.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : w.toValuationSubring) : L) = f from rfl] at h
    rw [h]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := w.adicValuation_ne_zero hf0
  have h2 : WithZero.log (w.adicValuation f) ≤ 0 :=
    (WithZero.log_le_iff_le_exp hne).2 (by simpa using h1)
  simp only [Place.ord]
  omega

theorem mem_of_ord_nonneg {f : L} (hf : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf0 hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hf
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem π.2 n)

theorem ord_eq_zero_of_mem_of_inv_mem {f : L} (hf : f ∈ w.toValuationSubring)
    (hfi : f⁻¹ ∈ w.toValuationSubring) : w.ord f = 0 := by
  have h1 := ord_nonneg_of_mem w hf
  have h2 := ord_nonneg_of_mem w hfi
  rw [w.ord_inv] at h2
  omega

theorem ord_algebraMap (a : k) : w.ord (algebraMap k L a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  exact ord_eq_zero_of_mem_of_inv_mem w (w.algebraMap_mem' a)
    (by rw [← map_inv₀]; exact w.algebraMap_mem' a⁻¹)

theorem irreducible_coe_ne_zero {π : w.toValuationSubring} (hπ : Irreducible π) : (π : L) ≠ 0 := by
  intro h
  exact hπ.ne_zero (by exact_mod_cast h)

theorem ord_coe_isUnit {X : w.toValuationSubring} (h : IsUnit X) : w.ord (X : L) = 0 := by
  obtain ⟨u, rfl⟩ := h
  exact w.ord_coe_unit u

theorem isUnit_of_ord_eq_zero {X : w.toValuationSubring} (h0 : X ≠ 0) (h : w.ord (X : L) = 0) :
    IsUnit X := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hX0 : (X : L) ≠ 0 := fun h' => h0 (by exact_mod_cast h')
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hX0 hπ
  rw [h, zpow_zero, mul_one] at hu
  have : X = (u : w.toValuationSubring) := Subtype.ext hu
  rw [this]
  exact Units.isUnit u

theorem ord_pos_of_mem_maximalIdeal {Y : w.toValuationSubring}
    (hY : Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring) (h0 : Y ≠ 0) :
    0 < w.ord (Y : L) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hY
  obtain ⟨b, rfl⟩ := hY
  have hb : b ≠ 0 := by rintro rfl; exact h0 (by simp)
  have hb' : (b : L) ≠ 0 := fun h' => hb (by exact_mod_cast h')
  push_cast
  rw [w.ord_mul hb' (irreducible_coe_ne_zero w hπ), w.ord_coe_irreducible hπ]
  have := ord_nonneg_of_mem w b.2
  omega

theorem mem_maximalIdeal_of_ord_pos {Y : w.toValuationSubring} (h : 0 < w.ord (Y : L)) :
    Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := ord_coe_isUnit w hu
  omega

theorem isUnit_add_of_mem_maximalIdeal {X Y : w.toValuationSubring} (hX : IsUnit X)
    (hY : Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring) : IsUnit (X + Y) := by
  by_contra h
  have h1 : X + Y ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h)
  have h2 : X ∈ IsLocalRing.maximalIdeal w.toValuationSubring := by
    simpa using sub_mem h1 hY
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hX

theorem exists_sub_algebraMap_mem_maximalIdeal [IsAlgClosed k] [IsCurveOver k L]
    (X : w.toValuationSubring) :
    ∃ a : k, X - algebraMap k w.toValuationSubring a ∈
      IsLocalRing.maximalIdeal w.toValuationSubring := by
  haveI : Module.Finite k w.ResidueField := IsCurveOver.finiteResidue w
  haveI : Algebra.IsIntegral k w.ResidueField := Algebra.IsIntegral.of_finite k _
  have hbij : Function.Bijective (algebraMap k w.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue w.toValuationSubring X)
  refine ⟨a, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
    IsScalarTower.algebraMap_apply k w.toValuationSubring w.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

end Basic

section Gauss

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem ord_sum_le [IsAlgClosed K] [IsCurveOver K F]
    (P : Place K F) (P' : Place K' F')
    (hcomap : P'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hord : ∀ f : F, P'.ord (algebraMap F F' f) = P.ord f)
    {ι : Type*} (s : Finset ι) (β : ι → K') (hβ : LinearIndependent K β) (u : ι → F)
    {i : ι} (hi : i ∈ s) (hui : u i ≠ 0) :
    P'.ord (∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (u j)) ≤ P.ord (u i) := by
  classical
  have hφmem : ∀ x : F, x ∈ P.toValuationSubring → algebraMap F F' x ∈ P'.toValuationSubring := by
    intro x hx
    rw [← hcomap] at hx
    exact hx

  set T := s.filter (fun j => u j ≠ 0) with hT
  have hiT : i ∈ T := Finset.mem_filter.2 ⟨hi, hui⟩
  have hTne : T.Nonempty := ⟨i, hiT⟩
  obtain ⟨i₀, hi₀T, hi₀⟩ := Finset.exists_mem_eq_inf' hTne (fun j => P.ord (u j))
  set m := T.inf' hTne (fun j => P.ord (u j)) with hm
  have hm_le : ∀ j ∈ T, m ≤ P.ord (u j) := fun j hj => Finset.inf'_le _ hj
  have hui₀ : u i₀ ≠ 0 := (Finset.mem_filter.1 hi₀T).2
  have hi₀s : i₀ ∈ s := (Finset.mem_filter.1 hi₀T).1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := irreducible_coe_ne_zero P hπ

  have ho_mem : ∀ j ∈ s, u j * (π : F) ^ (-m) ∈ P.toValuationSubring := by
    intro j hj
    by_cases huj : u j = 0
    · rw [huj, zero_mul]; exact zero_mem _
    apply mem_of_ord_nonneg
    rw [P.ord_mul huj (zpow_ne_zero _ hπ0), P.ord_zpow, P.ord_coe_irreducible hπ]
    have := hm_le j (Finset.mem_filter.2 ⟨hj, huj⟩)
    linarith

  have hdig : ∀ j ∈ s, ∃ a : K, ∃ r : P.toValuationSubring,
      r ∈ IsLocalRing.maximalIdeal P.toValuationSubring ∧
      u j * (π : F) ^ (-m) = algebraMap K F a + (r : F) := by
    intro j hj
    obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal P ⟨_, ho_mem j hj⟩
    refine ⟨a, _, ha, ?_⟩
    simp only [AddSubgroupClass.coe_sub, Place.coe_algebraMap]
    ring
  choose! a r har hur using hdig

  have hai₀ : a i₀ ≠ 0 := by
    intro h0
    have hunit : IsUnit (⟨_, ho_mem i₀ hi₀s⟩ : P.toValuationSubring) := by
      apply isUnit_of_ord_eq_zero P
      · intro h
        apply hui₀
        have h' : u i₀ * (π : F) ^ (-m) = 0 := by
          simpa using congrArg Subtype.val h
        rcases mul_eq_zero.1 h' with h'' | h''
        · exact h''
        · exact absurd h'' (zpow_ne_zero _ hπ0)
      · show P.ord (u i₀ * (π : F) ^ (-m)) = 0
        rw [P.ord_mul hui₀ (zpow_ne_zero _ hπ0), P.ord_zpow, P.ord_coe_irreducible hπ, ← hi₀]
        ring
    have heq : (⟨_, ho_mem i₀ hi₀s⟩ : P.toValuationSubring) = r i₀ := by
      apply Subtype.ext
      show u i₀ * (π : F) ^ (-m) = r i₀
      rw [hur i₀ hi₀s, h0, map_zero, zero_add]
    rw [heq] at hunit
    exact (IsLocalRing.mem_maximalIdeal _).1 (har i₀ hi₀s) hunit

  set d : K' := ∑ j ∈ s, a j • β j with hd
  have hd0 : d ≠ 0 := by
    intro h0
    exact hai₀ (linearIndependent_iff'.1 hβ s a h0 i₀ hi₀s)

  have hrmem : ∀ j ∈ s, (⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ : P'.toValuationSubring) ∈
      IsLocalRing.maximalIdeal P'.toValuationSubring := by
    intro j hj
    by_cases hr0 : r j = 0
    · have : (⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ : P'.toValuationSubring) = 0 := by
        apply Subtype.ext
        simp [hr0]
      rw [this]
      exact Ideal.zero_mem _
    apply mem_maximalIdeal_of_ord_pos P'
    show 0 < P'.ord (algebraMap F F' (r j))
    rw [hord]
    exact ord_pos_of_mem_maximalIdeal P (har j hj) hr0
  set Dd : P'.toValuationSubring := ⟨algebraMap K' F' d, P'.algebraMap_mem' d⟩ with hDd
  set Tt : P'.toValuationSubring := ∑ j ∈ s,
    (⟨algebraMap K' F' (β j), P'.algebraMap_mem' (β j)⟩ : P'.toValuationSubring) *
      ⟨algebraMap F F' (r j), hφmem _ (r j).2⟩ with hTt
  have hDunit : IsUnit Dd := by
    apply isUnit_of_ord_eq_zero P'
    · intro h
      have : algebraMap K' F' d = 0 := by simpa [hDd] using congrArg Subtype.val h
      exact hd0 ((algebraMap K' F').injective (by rw [this, map_zero]))
    · exact ord_algebraMap P' d
  have hTmem : Tt ∈ IsLocalRing.maximalIdeal P'.toValuationSubring :=
    Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ (hrmem j hj)
  have hunit := isUnit_add_of_mem_maximalIdeal P' hDunit hTmem
  have hcoe : ((Dd + Tt : P'.toValuationSubring) : F') =
      algebraMap K' F' d + ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j) := by
    simp [hDd, hTt]
  have hne' : algebraMap K' F' d + ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j) ≠ 0 := by
    rw [← hcoe]
    exact_mod_cast hunit.ne_zero
  have hord0 : P'.ord (algebraMap K' F' d +
      ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j)) = 0 := by
    rw [← hcoe]
    exact ord_coe_isUnit P' hunit

  have hS : ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (u j) =
      algebraMap F F' (π : F) ^ m * (algebraMap K' F' d +
        ∑ j ∈ s, algebraMap K' F' (β j) * algebraMap F F' (r j)) := by
    rw [hd, map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have huj : u j = (algebraMap K F (a j) + r j) * (π : F) ^ m := by
      rw [← hur j hj, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
    rw [huj, map_mul, map_add, map_zpow₀, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
    ring
  rw [hS, P'.ord_mul (zpow_ne_zero _ ((map_ne_zero _).2 hπ0)) hne', P'.ord_zpow, hord,
    P.ord_coe_irreducible hπ, hord0]
  simpa using hm_le i hiT

end Gauss

section Main

variable (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem exists_linearIndependent_repr {z : F'}
    (hz : z ∈ Submodule.span K' (Set.range (algebraMap F F'))) :
    ∃ (n : ℕ) (β : Fin n → K') (u : Fin n → F), LinearIndependent K β ∧
      z = ∑ k, algebraMap K' F' (β k) * algebraMap F F' (u k) := by
  classical
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hz
  set W : Submodule K K' := Submodule.span K (↑(c.support.image c) : Set K') with hW
  haveI : Module.Finite K W := FiniteDimensional.span_of_finite K (Finset.finite_toSet _)
  set b := Module.finBasis K W
  have hcW : ∀ f : F, c f ∈ W := by
    intro f
    by_cases hf : f ∈ c.support
    · exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem c hf))
    · rw [Finsupp.notMem_support_iff.1 hf]; exact zero_mem _
  refine ⟨_, fun k => (b k : K'), fun k => ∑ f ∈ c.support, b.repr ⟨c f, hcW f⟩ k • f,
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W), ?_⟩
  have hcf : ∀ f : F, c f = ∑ k, b.repr ⟨c f, hcW f⟩ k • (b k : K') := by
    intro f
    have h2 := congrArg Subtype.val (b.sum_repr ⟨c f, hcW f⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  simp only [Finsupp.sum, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  conv_lhs => rw [hcf f]
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul,
    ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
  ring

variable {K F} in

theorem degree_eq_sum [IsAlgClosed K] [IsCurveOver K F] (E : Divisor K F) :
    E.degree = E.sum fun _ n => n := by
  simp [Divisor.degree, Finsupp.liftAddHom_apply, IsCurveOver.deg_eq_one_of_isAlgClosed]

theorem isPrincipal_of_constantFieldExtension [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0)
    (hD' : D'.IsPrincipal) :
    D.IsPrincipal := by
  classical
  obtain ⟨z, hz0, hzD⟩ := hD'

  have hX := fun P : Place K F =>
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F K' F'
      hfg hfg' hgen P
  choose lift hlift_comap hlift_ord hlift_uniq using hX
  have hlift_inj : Function.Injective lift := by
    intro P Q h
    apply Place.ext
    rw [← hlift_comap P, ← hlift_comap Q, h]

  have hz_off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        z ∈ v'.toValuationSubring := by
    intro v' hv'
    apply mem_of_ord_nonneg
    rw [← hzD, hD'off v' hv']
  have hzspan := AlgebraicCurve.mem_span_range_algebraMap_of_constantFieldExtension K F K' F'
    hfg hfg' hgen z hz_off
  obtain ⟨n, β, u, hβ, hzu⟩ := exists_linearIndependent_repr K F K' F' hzspan

  obtain ⟨k₀, hk₀⟩ : ∃ k, u k ≠ 0 := by
    by_contra h
    push Not at h
    apply hz0
    rw [hzu]
    simp [h]

  have hle : ∀ P : Place K F, D P ≤ P.ord (u k₀) := by
    intro P
    have h := ord_sum_le P (lift P) (hlift_comap P) (hlift_ord P) Finset.univ β hβ u
      (Finset.mem_univ k₀) hk₀
    rwa [← hzu, ← hzD, hD'over _ _ (hlift_comap P)] at h

  have hdegD' : D'.degree = 0 := by
    obtain ⟨E', hE', hE'deg⟩ := HasPrincipalDivisors.exists_divisor (K := K') z hz0
    have : D' = E' := Finsupp.ext fun v' => by rw [hzD, hE']
    rw [this]
    exact hE'deg
  have hD'map : D' = Finsupp.mapDomain lift D := by
    ext v'
    by_cases hv' : ∃ P, lift P = v'
    · obtain ⟨P, rfl⟩ := hv'
      rw [Finsupp.mapDomain_apply hlift_inj, hD'over _ _ (hlift_comap P)]
    · push Not at hv'
      rw [Finsupp.mapDomain_notin_range _ _ (fun ⟨P, hP⟩ => hv' P hP)]
      apply hD'off
      intro P hP
      exact hv' P (hlift_uniq P v' hP).symm
  have hdegD : D.degree = 0 := by
    have h1 : D'.degree = D.sum fun _ n => n := by
      rw [hD'map, degree_eq_sum, Finsupp.sum_mapDomain_index_inj hlift_inj]
    rw [degree_eq_sum, ← h1, hdegD']
  obtain ⟨E, hE, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (u k₀) hk₀

  have hG : ∀ v, 0 ≤ (E - D) v := fun v => by
    simp only [Finsupp.coe_sub, Pi.sub_apply, hE]
    linarith [hle v]
  have hGdeg : (E - D).degree = 0 := by rw [map_sub, hEdeg, hdegD, sub_zero]
  have hG0 : E - D = 0 := by
    rw [degree_eq_sum, Finsupp.sum] at hGdeg
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hG v)).1 hGdeg
    ext v
    by_cases hv : v ∈ (E - D).support
    · exact h v hv
    · exact Finsupp.notMem_support_iff.1 hv
  refine ⟨u k₀, hk₀, fun v => ?_⟩
  have h := DFunLike.congr_fun hG0 v
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply, hE] at h
  linarith

end Main

end AlgebraicCurve.W7XK1a

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension.AlgebraicCurve in
theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0)
    (hD' : D'.IsPrincipal) :
    D.IsPrincipal :=
  AlgebraicCurve.W7XK1a.isPrincipal_of_constantFieldExtension K F K' F' hfg hfg' hgen D D'
    hD'over hD'off hD'

end S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension (solution)
