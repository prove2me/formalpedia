-- Prove2me | solution 1 for AlgebraicCurve.CurveModel.range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6ad21c85-070c-5302-be26-a2425c1fa8d5

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_TwoChartCech_GluedLines
import Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl.AlgebraicCurve Polynomial AlgebraicGeometry.Polynomial IsDedekindDomain"
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"

universe u

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel CurveModel.placeEquiv_apply Place Place.ext Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.ofHeightOneSpectrum_injective RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.placeOfPoint RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring RationalFunctionField.placeInfty RationalFunctionField.placeInfty_toValuationSubring range_algebraMap_functionField_eq_iInf_of_isAffineOpen"
namespace S1c
p2m_open "AlgebraicCurve"

variable (K : Type u) [Field K]

noncomputable abbrev ι : LaurentPolynomial K →+* RatFunc K :=
  LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)

theorem ι_T (n : ℤ) : ι K (LaurentPolynomial.T n) = (RatFunc.X : RatFunc K) ^ n := by
  rw [LaurentPolynomial.eval₂_T, Units.val_zpow_eq_zpow_val, Units.val_mk0]

theorem ι_C (a : K) : ι K (LaurentPolynomial.C a) = algebraMap K (RatFunc K) a :=
  LaurentPolynomial.eval₂_C _ _ _

theorem ι_comp_toLaurent : (ι K).comp Polynomial.toLaurent = algebraMap K[X] (RatFunc K) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · rw [RingHom.comp_apply, Polynomial.toLaurent_C, ι_C, RatFunc.algebraMap_C]
    rfl
  · rw [RingHom.comp_apply, Polynomial.toLaurent_X, ι_T, zpow_one, RatFunc.algebraMap_X]

theorem ι_toLaurent (p : K[X]) : ι K (Polynomial.toLaurent p) = algebraMap K[X] (RatFunc K) p := by
  rw [← ι_comp_toLaurent K, RingHom.comp_apply]

theorem ι_injective : Function.Injective (ι K) := by
  refine (injective_iff_map_eq_zero _).mpr fun h hh => ?_
  obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow h
  have h1 : algebraMap K[X] (RatFunc K) p = 0 := by
    rw [← ι_toLaurent, hp, map_mul, hh, zero_mul]
  have hp0 : p = 0 := (map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h1
  have h2 : h * LaurentPolynomial.T (n : ℤ) = 0 := by rw [← hp, hp0, map_zero]
  exact ((LaurentPolynomial.isUnit_T (n : ℤ)).mul_left_eq_zero).mp h2

theorem mem_polyPart_iff (f : LaurentPolynomial K) :
    f ∈ TwoChartCech.polyPart K ↔ ∃ p : K[X], Polynomial.toLaurent p = f := by
  classical
  constructor
  · intro hf
    obtain ⟨g, rfl⟩ : ∃ g : ℤ →₀ K, AddMonoidAlgebra.ofCoeff g = f := ⟨f.coeff, rfl⟩
    induction g using Finsupp.induction with
    | zero => exact ⟨0, by rw [map_zero]; rfl⟩
    | single_add n a g hn ha ih =>
        have hsupp : (Finsupp.single n a + g).support = insert n g.support := by
          rw [Finsupp.support_add_eq, Finsupp.support_single_ne_zero _ ha, Finset.singleton_union]
          rw [Finsupp.support_single_ne_zero _ ha, Finset.disjoint_singleton_left]
          exact hn
        replace hf : ∀ m ∈ (Finsupp.single n a + g).support, 0 ≤ m := hf
        have hn0 : 0 ≤ n := hf n (by rw [hsupp]; exact Finset.mem_insert_self _ _)
        obtain ⟨q, hq⟩ := ih (fun m hm => hf m (by rw [hsupp]; exact Finset.mem_insert_of_mem hm))
        refine ⟨Polynomial.monomial n.toNat a + q, ?_⟩
        rw [map_add, hq, Polynomial.toLaurent_C_mul_T, Int.toNat_of_nonneg hn0,
          ← LaurentPolynomial.single_eq_C_mul_T]
        rfl
  · rintro ⟨p, rfl⟩ n hn
    rw [LaurentPolynomial.support_coeff_toLaurent, Finset.mem_map] at hn
    obtain ⟨m, -, rfl⟩ := hn
    exact Int.natCast_nonneg m

theorem map_polyPart_eq_range_algebraMap :
    (TwoChartCech.polyPart K).toSubring.map (ι K) = (algebraMap K[X] (RatFunc K)).range := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨p, rfl⟩ := (mem_polyPart_iff K f).mp hf
    exact ⟨p, (ι_toLaurent K p).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨Polynomial.toLaurent p, (mem_polyPart_iff K _).mpr ⟨p, rfl⟩, ι_toLaurent K p⟩

theorem forall_valuation_le_one_iff (g : RatFunc K) :
    (∀ w : HeightOneSpectrum K[X], w.valuation (RatFunc K) g ≤ 1) ↔ g ∈ (algebraMap K[X] (RatFunc K)).range := by
  constructor
  · exact HeightOneSpectrum.mem_integers_of_valuation_le_one (RatFunc K) g
  · rintro ⟨p, rfl⟩ w
    exact w.valuation_le_one p

theorem valuation_X_eq_one_of_ne {w : HeightOneSpectrum K[X]} (hw : w ≠ Polynomial.idealX K) :
    w.valuation (RatFunc K) RatFunc.X = 1 := by
  rw [← RatFunc.algebraMap_X, HeightOneSpectrum.valuation_of_algebraMap]
  refine le_antisymm (w.intValuation_le_one _) ?_
  rw [← not_lt, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  intro hX
  apply hw
  apply HeightOneSpectrum.ext
  have hle : (Polynomial.idealX K).asIdeal ≤ w.asIdeal := by
    rw [Polynomial.idealX_span, Ideal.span_singleton_le_iff_mem]; exact hX
  exact ((Polynomial.idealX K).isMaximal.eq_of_le w.isPrime.ne_top hle).symm

theorem forall_ne_valuation_le_one_iff (g : RatFunc K) :
    (∀ w : HeightOneSpectrum K[X], w ≠ Polynomial.idealX K → w.valuation (RatFunc K) g ≤ 1) ↔
      g ∈ (ι K).range := by
  constructor
  · intro hg
    by_cases hg0 : g = 0
    · exact ⟨0, by rw [map_zero, hg0]⟩

    set v := (Polynomial.idealX K).valuation (RatFunc K) with hv
    have hvg : v g ≠ 0 := (Valuation.ne_zero_iff v).mpr hg0
    set k := WithZero.log (v g) with hk_def
    have hk : v g = WithZero.exp k := (WithZero.exp_log hvg).symm
    obtain ⟨N, hN⟩ : ∃ N : ℕ, v (RatFunc.X ^ N * g) ≤ 1 := by
      refine ⟨k.toNat, ?_⟩
      have hX : v RatFunc.X = WithZero.exp (-1) := Polynomial.valuation_X_eq_neg_one K
      rw [map_mul, map_pow, hX, hk, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero,
        WithZero.exp_le_exp]
      have h1 := Int.self_le_toNat k
      simp only [nsmul_eq_mul, mul_neg, mul_one]
      omega
    have hall : ∀ w : HeightOneSpectrum K[X], w.valuation (RatFunc K) (RatFunc.X ^ N * g) ≤ 1 := by
      intro w
      by_cases hw : w = Polynomial.idealX K
      · subst hw; exact hN
      · rw [map_mul, map_pow, valuation_X_eq_one_of_ne K hw, one_pow, one_mul]
        exact hg w hw
    obtain ⟨p, hp⟩ := (forall_valuation_le_one_iff K _).mp hall
    refine ⟨Polynomial.toLaurent p * LaurentPolynomial.T (-(N : ℤ)), ?_⟩
    rw [map_mul, ι_toLaurent, ι_T, hp, zpow_neg, zpow_natCast, mul_comm, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero N RatFunc.X_ne_zero), one_mul]
  · rintro ⟨f, rfl⟩ w hw
    obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
    have hf : ι K f = algebraMap K[X] (RatFunc K) p * (RatFunc.X ^ n)⁻¹ := by
      rw [← ι_toLaurent, hp, map_mul, ι_T, zpow_natCast, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero n RatFunc.X_ne_zero), mul_one]
    rw [hf, map_mul, map_inv₀, map_pow, valuation_X_eq_one_of_ne K hw, one_pow, inv_one, mul_one]
    exact w.valuation_le_one p

end AlgebraicCurve.S1c

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel CurveModel.placeEquiv_apply Place Place.ext Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.ofHeightOneSpectrum_injective RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.placeOfPoint RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring RationalFunctionField.placeInfty RationalFunctionField.placeInfty_toValuationSubring range_algebraMap_functionField_eq_iInf_of_isAffineOpen"
namespace S1c
p2m_open "AlgebraicCurve"

variable (K : Type u) [Field K]

theorem mul_T_apply (f : LaurentPolynomial K) (n m : ℤ) :
    (f * LaurentPolynomial.T n : LaurentPolynomial K).coeff m = f.coeff (m - n) := by
  rw [show (LaurentPolynomial.T n : LaurentPolynomial K) = AddMonoidAlgebra.single n 1 from rfl,
    AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

theorem toLaurent_apply_natCast (p : K[X]) (k : ℕ) :
    (Polynomial.toLaurent p : LaurentPolynomial K).coeff (k : ℤ) = p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact (Finsupp.mapDomain_apply Nat.castEmbedding.injective _ k).trans rfl

theorem toLaurent_apply_of_neg (p : K[X]) (m : ℤ) (hm : m < 0) :
    (Polynomial.toLaurent p : LaurentPolynomial K).coeff m = 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_notin_range _ _
    (by rintro ⟨k, rfl⟩; exact absurd hm (not_lt.mpr (Int.natCast_nonneg k)))

theorem mem_invPolyPart_iff_natDegree_le {f : LaurentPolynomial K} {n : ℕ} {p : K[X]}
    (hp : Polynomial.toLaurent p = f * LaurentPolynomial.T (n : ℤ)) :
    f ∈ TwoChartCech.invPolyPart K ↔ p.natDegree ≤ n := by
  have hcoeff : ∀ m : ℤ, f.coeff m = (Polynomial.toLaurent p : LaurentPolynomial K).coeff (m + n) := by
    intro m
    rw [hp, mul_T_apply, add_sub_cancel_right]
  constructor
  · intro hf
    by_contra hlt
    rw [not_le] at hlt
    have hm : (0 : ℤ) < (p.natDegree : ℤ) - n := by omega
    have hne : f.coeff ((p.natDegree : ℤ) - n) ≠ 0 := by
      rw [hcoeff, sub_add_cancel, toLaurent_apply_natCast]
      exact Polynomial.leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hlt)
    exact absurd (hf _ (Finsupp.mem_support_iff.mpr hne)) (not_le.mpr hm)
  · intro hle m hm
    rw [Finsupp.mem_support_iff, hcoeff] at hm
    by_contra hpos
    rw [not_le] at hpos
    apply hm
    have : m + n = (((m + n).toNat : ℕ) : ℤ) := by omega
    rw [this, toLaurent_apply_natCast]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

variable [DecidableEq (RatFunc K)]

theorem inftyValuation_ι_le_one_iff {f : LaurentPolynomial K} {n : ℕ} {p : K[X]}
    (hp : Polynomial.toLaurent p = f * LaurentPolynomial.T (n : ℤ)) (hp0 : p ≠ 0) :
    RatFunc.inftyValuation K (ι K f) ≤ 1 ↔ p.natDegree ≤ n := by
  have hf : ι K f = algebraMap K[X] (RatFunc K) p * (RatFunc.X ^ n)⁻¹ := by
    rw [← ι_toLaurent, hp, map_mul, ι_T, zpow_natCast, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero n RatFunc.X_ne_zero), mul_one]
  have hpv : RatFunc.inftyValuation K (algebraMap K[X] (RatFunc K) p) = WithZero.exp (p.natDegree : ℤ) := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero _
      ((map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hp0), RatFunc.intDegree_polynomial]
  rw [hf, map_mul, map_inv₀, map_pow, RatFunc.inftyValuation.X, hpv, ← WithZero.exp_nsmul, ← WithZero.exp_neg,
    ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
  simp only [nsmul_eq_mul, mul_one]
  omega

theorem map_invPolyPart_eq :
    (TwoChartCech.invPolyPart K).toSubring.map (ι K) =
      (ι K).range ⊓ (RationalFunctionField.placeInfty K).toValuationSubring.toSubring := by
  ext g
  rw [Subring.mem_inf, RingHom.mem_range]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨⟨f, rfl⟩, ?_⟩
    show ι K f ∈ (RationalFunctionField.placeInfty K).toValuationSubring
    rw [RationalFunctionField.placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff]
    obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
    by_cases hp0 : p = 0
    · have : f = 0 := by
        have h2 : f * LaurentPolynomial.T (n : ℤ) = 0 := by rw [← hp, hp0, map_zero]
        exact ((LaurentPolynomial.isUnit_T (n : ℤ)).mul_left_eq_zero).mp h2
      rw [this, map_zero, map_zero]; exact zero_le'
    exact (inftyValuation_ι_le_one_iff K hp hp0).mpr ((mem_invPolyPart_iff_natDegree_le K hp).mp hf)
  · rintro ⟨⟨f, rfl⟩, hg⟩
    refine ⟨f, ?_, rfl⟩
    change ι K f ∈ (RationalFunctionField.placeInfty K).toValuationSubring at hg
    rw [RationalFunctionField.placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff] at hg
    obtain ⟨n, p, hp⟩ := LaurentPolynomial.exists_T_pow f
    by_cases hp0 : p = 0
    · have : f = 0 := by
        have h2 : f * LaurentPolynomial.T (n : ℤ) = 0 := by rw [← hp, hp0, map_zero]
        exact ((LaurentPolynomial.isUnit_T (n : ℤ)).mul_left_eq_zero).mp h2
      rw [this]; exact Subalgebra.zero_mem _
    exact (mem_invPolyPart_iff_natDegree_le K hp).mpr ((inftyValuation_ι_le_one_iff K hp hp0).mp hg)

end AlgebraicCurve.S1c

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel CurveModel.placeEquiv_apply Place Place.ext Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.ofHeightOneSpectrum_injective RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.placeOfPoint RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring RationalFunctionField.placeInfty RationalFunctionField.placeInfty_toValuationSubring range_algebraMap_functionField_eq_iInf_of_isAffineOpen"
namespace S1c
p2m_open "AlgebraicCurve"

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]

open _root_.AlgebraicCurve.RationalFunctionField in

theorem place_eq_ofHeightOneSpectrum_or_eq_placeInfty (v : Place K (RatFunc K)) :
    (∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w) ∨ v = placeInfty K := by
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨w, hw, -⟩ := h
    exact Or.inl ⟨w, Place.ext (v.adicValuation_valuationSubring.symm.trans
      ((Valuation.isEquiv_iff_valuationSubring _ _).mp hw))⟩

theorem ofHeightOneSpectrum_ne_placeInfty (w : HeightOneSpectrum K[X]) :
    Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w ≠ RationalFunctionField.placeInfty K := by
  intro h
  apply RatFunc.adicValuation_not_isEquiv_infty_valuation w
  rw [Valuation.isEquiv_iff_valuationSubring,
    ← Place.ofHeightOneSpectrum_toValuationSubring (K := K) (F := RatFunc K), h,
    RationalFunctionField.placeInfty_toValuationSubring]

theorem mem_ofHeightOneSpectrum_iff (w : HeightOneSpectrum K[X]) (g : RatFunc K) :
    g ∈ (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).toValuationSubring ↔
      w.valuation (RatFunc K) g ≤ 1 := by
  rw [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]

theorem placeOfPoint_zero_eq :
    RationalFunctionField.placeOfPoint K 0 = Place.ofHeightOneSpectrum (Polynomial.idealX K) := by
  rw [RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum]
  congr 1
  apply HeightOneSpectrum.ext
  rw [RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal, Polynomial.idealX_span, map_zero, sub_zero]

theorem iInf_ne_placeInfty_eq :
    (⨅ (v : Place K (RatFunc K)) (_ : v ≠ RationalFunctionField.placeInfty K), v.toValuationSubring.toSubring) =
      (TwoChartCech.polyPart K).toSubring.map (ι K) := by
  rw [map_polyPart_eq_range_algebraMap]
  ext g
  simp only [Subring.mem_iInf]
  rw [← forall_valuation_le_one_iff]
  constructor
  · intro h w
    rw [← mem_ofHeightOneSpectrum_iff]
    exact h _ (ofHeightOneSpectrum_ne_placeInfty K w)
  · intro h v hv
    rcases place_eq_ofHeightOneSpectrum_or_eq_placeInfty K v with ⟨w, rfl⟩ | rfl
    · exact (mem_ofHeightOneSpectrum_iff K w g).mpr (h w)
    · exact absurd rfl hv

theorem iInf_ne_ne_eq :
    (⨅ (v : Place K (RatFunc K)) (_ : v ≠ RationalFunctionField.placeInfty K)
        (_ : v ≠ RationalFunctionField.placeOfPoint K 0), v.toValuationSubring.toSubring) = (ι K).range := by
  ext g
  simp only [Subring.mem_iInf]
  rw [← forall_ne_valuation_le_one_iff]
  constructor
  · intro h w hw
    rw [← mem_ofHeightOneSpectrum_iff]
    refine h _ (ofHeightOneSpectrum_ne_placeInfty K w) ?_
    rw [placeOfPoint_zero_eq]
    exact fun heq => hw (Place.ofHeightOneSpectrum_injective heq)
  · intro h v hv hv0
    rcases place_eq_ofHeightOneSpectrum_or_eq_placeInfty K v with ⟨w, rfl⟩ | rfl
    · refine (mem_ofHeightOneSpectrum_iff K w g).mpr (h w ?_)
      rintro rfl
      exact hv0 (placeOfPoint_zero_eq K).symm
    · exact absurd rfl hv

theorem iInf_ne_placeOfPoint_zero_eq :
    (⨅ (v : Place K (RatFunc K)) (_ : v ≠ RationalFunctionField.placeOfPoint K 0), v.toValuationSubring.toSubring) =
      (TwoChartCech.invPolyPart K).toSubring.map (ι K) := by
  rw [map_invPolyPart_eq, ← iInf_ne_ne_eq]
  ext g
  simp only [Subring.mem_iInf, Subring.mem_inf]
  constructor
  · intro h
    refine ⟨fun v hv hv0 => h v hv0, h _ ?_⟩
    rw [placeOfPoint_zero_eq]
    exact (ofHeightOneSpectrum_ne_placeInfty K _).symm
  · rintro ⟨h, hinf⟩ v hv0
    by_cases hv : v = RationalFunctionField.placeInfty K
    · subst hv; exact hinf
    · exact h v hv hv0

end AlgebraicCurve.S1c

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel CurveModel.placeEquiv_apply Place Place.ext Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.ofHeightOneSpectrum_injective RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.placeOfPoint RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring RationalFunctionField.placeInfty RationalFunctionField.placeInfty_toValuationSubring range_algebraMap_functionField_eq_iInf_of_isAffineOpen"
namespace S1c
p2m_open "AlgebraicCurve"

variable (K : Type u) [Field K]

theorem range_sections_eq_iInf (M : CurveModel K (RatFunc K)) (W : M.C.Opens) (hW : IsAffineOpen W) [Nonempty W] :
    ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
        (algebraMap Γ(M.C, W) M.C.functionField)).range =
      ⨅ (w : Place K (RatFunc K)) (_ : (M.placeEquiv.symm w).1 ∈ W), w.toValuationSubring.toSubring := by
  letI := M.functionFieldAlgebra
  set e : RatFunc K ≃+* M.C.functionField := M.ffEquiv with he_def
  have he : ∀ a : K, e (algebraMap K (RatFunc K) a) = algebraMap K M.C.functionField a := M.ffEquiv_algebraMap

  have H := AlgebraicCurve.range_algebraMap_functionField_eq_iInf_of_isAffineOpen M.toBase W hW

  have hL : ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
        (algebraMap Γ(M.C, W) M.C.functionField)).range =
      ((algebraMap Γ(M.C, W) M.C.functionField).range).comap (e : RatFunc K →+* M.C.functionField) := by
    rw [← RingHom.map_range]
    exact Subring.map_equiv_eq_comap_symm e.symm _

  have hstalk : ∀ xc : closedPoints M.C,
      ((algebraMap (M.C.presheaf.stalk xc.1) M.C.functionField).range).comap (e : RatFunc K →+* M.C.functionField) =
        (M.placeEquiv xc).toValuationSubring.toSubring := by
    intro xc
    rw [CurveModel.placeEquiv_apply, ← M.range_stalk_eq xc, ← RingHom.map_range]
    exact (Subring.map_equiv_eq_comap_symm e.symm _).symm
  rw [hL, H, Subring.comap_iInf]
  simp_rw [Subring.comap_iInf]
  apply le_antisymm
  ·
    refine le_iInf fun w => le_iInf fun hw => ?_
    set xc := M.placeEquiv.symm w with hxc

    let v : Place K M.C.functionField := Place.congrRingEquiv e he w
    have hv : (algebraMap (M.C.presheaf.stalk xc.1) M.C.functionField).range = v.toValuationSubring.toSubring := by
      have h1 := hstalk xc
      rw [hxc, Equiv.apply_symm_apply] at h1

      have h2 := congrArg (Subring.comap (e.symm : M.C.functionField →+* RatFunc K)) h1
      rw [Subring.comap_comap] at h2
      have h3 : (e : RatFunc K →+* M.C.functionField).comp (e.symm : M.C.functionField →+* RatFunc K) =
          RingHom.id _ := by
        ext y; exact e.apply_symm_apply y
      rw [h3] at h2
      have h4 : Subring.comap (RingHom.id _) (algebraMap (M.C.presheaf.stalk xc.1) M.C.functionField).range =
          (algebraMap (M.C.presheaf.stalk xc.1) M.C.functionField).range := SetLike.ext fun _ => Iff.rfl
      rw [h4] at h2
      rw [h2]
      rfl
    refine (iInf_le_of_le v (iInf_le_of_le ⟨xc.1, hw, xc.2, hv⟩ le_rfl)).trans ?_

    show Subring.comap (e : RatFunc K →+* M.C.functionField) v.toValuationSubring.toSubring ≤ _
    intro g hg
    have hg' : e g ∈ (Place.congrRingEquiv e he w).toValuationSubring := hg
    rw [Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap] at hg'
    have : e.symm (e g) ∈ w.toValuationSubring := hg'
    rwa [e.symm_apply_apply] at this
  ·
    refine le_iInf fun v => le_iInf fun hv => ?_
    obtain ⟨x, hxW, hxc, hxv⟩ := hv
    have h1 := hstalk ⟨x, hxc⟩
    rw [hxv] at h1
    rw [h1]
    exact iInf_le_of_le (M.placeEquiv ⟨x, hxc⟩) (iInf_le_of_le (by rw [Equiv.symm_apply_apply]; exact hxW) le_rfl)

end AlgebraicCurve.S1c

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "CurveModel CurveModel.placeEquiv_apply Place Place.ext Place.ofHeightOneSpectrum Place.ofHeightOneSpectrum_toValuationSubring Place.ofHeightOneSpectrum_injective RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal RationalFunctionField.placeOfPoint RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum Place.congrRingEquiv Place.congrRingEquiv_toValuationSubring RationalFunctionField.placeInfty RationalFunctionField.placeInfty_toValuationSubring range_algebraMap_functionField_eq_iInf_of_isAffineOpen"
namespace S1c
p2m_open "AlgebraicCurve"

variable (K : Type u) [Field K] [DecidableEq (RatFunc K)]

theorem coe_placeEquiv_symm_mem_iff_ne (M : CurveModel K (RatFunc K)) (W : M.C.Opens) (v₀ : Place K (RatFunc K))
    (hW : ((W : Set M.C)) = {(M.placeEquiv.symm v₀).1}ᶜ) (w : Place K (RatFunc K)) :
    (M.placeEquiv.symm w).1 ∈ W ↔ w ≠ v₀ := by
  rw [← SetLike.mem_coe, hW, Set.mem_compl_singleton_iff, Ne, Subtype.val_inj, Equiv.apply_eq_iff_eq]

end AlgebraicCurve.S1c

open AlgebraicCurve.S1c in

theorem solution
    (K : Type u) [Field K] [DecidableEq (RatFunc K)]
    (M : CurveModel K (RatFunc K)) (U V : M.C.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    [Nonempty U] [Nonempty V] [Nonempty (U ⊓ V : M.C.Opens)]
    (hUset : ((U : Set M.C)) = {(M.placeEquiv.symm (RationalFunctionField.placeInfty K)).1}ᶜ)
    (hVset : ((V : Set M.C)) = {(M.placeEquiv.symm (RationalFunctionField.placeOfPoint K 0)).1}ᶜ) :
    Function.Injective
        (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, U) M.C.functionField)).range =
        ((TwoChartCech.polyPart K).toSubring).map
          (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, V) M.C.functionField)).range =
        ((TwoChartCech.invPolyPart K).toSubring).map
          (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K)) (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)) ∧
      ((M.ffEquiv.symm : M.C.functionField ≃+* RatFunc K).toRingHom.comp
          (algebraMap Γ(M.C, U ⊓ V) M.C.functionField)).range =
        (LaurentPolynomial.eval₂ (algebraMap K (RatFunc K))
          (Units.mk0 (RatFunc.X : RatFunc K) RatFunc.X_ne_zero)).range := by
  refine ⟨ι_injective K, ?_, ?_, ?_⟩
  · rw [range_sections_eq_iInf K M U hU, ← iInf_ne_placeInfty_eq K]
    refine iInf_congr fun w => iInf_congr_Prop (coe_placeEquiv_symm_mem_iff_ne K M U _ hUset w) fun _ => rfl
  · rw [range_sections_eq_iInf K M V hV, ← iInf_ne_placeOfPoint_zero_eq K]
    refine iInf_congr fun w => iInf_congr_Prop (coe_placeEquiv_symm_mem_iff_ne K M V _ hVset w) fun _ => rfl
  · rw [range_sections_eq_iInf K M (U ⊓ V) hUV, ← iInf_ne_ne_eq K]
    refine iInf_congr fun w => ?_
    have h : (M.placeEquiv.symm w).1 ∈ U ⊓ V ↔
        w ≠ RationalFunctionField.placeInfty K ∧ w ≠ RationalFunctionField.placeOfPoint K 0 := by
      rw [TopologicalSpace.Opens.mem_inf, coe_placeEquiv_symm_mem_iff_ne K M U _ hUset w,
        coe_placeEquiv_symm_mem_iff_ne K M V _ hVset w]
    rw [iInf_congr_Prop h (f₂ := fun _ => w.toValuationSubring.toSubring) fun _ => rfl, iInf_and]

end S_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
end P2MW
export P2MW.S_AlgebraicCurve_CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl (solution)
