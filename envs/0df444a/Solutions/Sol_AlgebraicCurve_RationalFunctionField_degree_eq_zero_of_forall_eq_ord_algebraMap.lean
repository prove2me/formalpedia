-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/53133994-14a7-53b6-900f-486e09a3ccaa

import Mathlib.FieldTheory.RatFunc.Degree
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap.AlgebraicCurve"
open IsDedekindDomain WithZero IsLocalRing
open scoped Polynomial

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single Place.ofHeightOneSpectrum RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "exists_forall_ne_ofHeightOneSpectrum subsingleton_setOf_forall_ne_ofHeightOneSpectrum ord_ofHeightOneSpectrum_of_span ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum deg_ofHeightOneSpectrum deg_eq_one_of_forall_ne_ofHeightOneSpectrum"
p2m_open "AlgebraicCurve.RationalFunctionField~finitePlace~heightOneSpectrumOfIrreducible_asIdeal~heightOneSpectrumOfIrreducible AlgebraicCurve"

namespace WFj
variable (K : Type*) [Field K]

def heightOneSpectrumOfIrreducible {p : K[X]} (hp : Irreducible p) :
    HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {p}
  isPrime := (PrincipalIdealRing.isMaximal_of_irreducible hp).isPrime
  ne_bot := by simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero

theorem heightOneSpectrumOfIrreducible_asIdeal {p : K[X]} (hp : Irreducible p) :
    (heightOneSpectrumOfIrreducible K hp).asIdeal = Ideal.span {p} := rfl

def finitePlace {p : K[X]} (hp : Irreducible p) : Place K (RatFunc K) :=
  Place.ofHeightOneSpectrum (heightOneSpectrumOfIrreducible K hp)

variable {K}

theorem ne_finitePlace_of_forall_ne {v : Place K (RatFunc K)}
    (hv : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w) {p : K[X]} (hp : Irreducible p) :
    v ≠ finitePlace K hp :=
  hv _

theorem single_add_single_apply_eq_ord {vinf : Place K (RatFunc K)}
    (hvinf : ∀ w : HeightOneSpectrum K[X], vinf ≠ Place.ofHeightOneSpectrum w)
    {p : K[X]} (hp : Irreducible p) (v : Place K (RatFunc K)) :
    (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) v
      = v.ord (algebraMap K[X] (RatFunc K) p) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  rw [Finsupp.add_apply]
  by_cases hfin : ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w
  · obtain ⟨w, rfl⟩ := hfin

    rw [Finsupp.single_eq_of_ne (hvinf w).symm, add_zero]
    by_cases hcase :
        Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w = finitePlace K hp
    · rw [hcase, Finsupp.single_eq_same]
      exact (ord_ofHeightOneSpectrum_of_span (heightOneSpectrumOfIrreducible K hp) hp0
        (heightOneSpectrumOfIrreducible_asIdeal K hp)).symm
    · rw [Finsupp.single_eq_of_ne hcase]
      symm
      by_contra hne
      refine hcase ?_
      have hmem : p ∈ w.asIdeal :=
        (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) w hp0).mp hne
      have hspan : Ideal.span {p} = w.asIdeal :=
        (PrincipalIdealRing.isMaximal_of_irreducible hp).eq_of_le w.isPrime.ne_top
          ((Ideal.span_singleton_le_iff_mem _).mpr hmem)
      have hwp : w = heightOneSpectrumOfIrreducible K hp :=
        HeightOneSpectrum.ext
          (hspan.symm.trans (heightOneSpectrumOfIrreducible_asIdeal K hp).symm)
      rw [hwp]
      rfl
  ·
    have hv : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w :=
      fun w h => hfin ⟨w, h⟩
    have hveq : v = vinf := subsingleton_setOf_forall_ne_ofHeightOneSpectrum hv hvinf
    rw [Finsupp.single_eq_of_ne (show v ≠ finitePlace K hp from hv _), zero_add, hveq,
      Finsupp.single_eq_same,
      ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum vinf hvinf (RatFunc.algebraMap_ne_zero hp0),
      RatFunc.intDegree_polynomial]

theorem degree_single_add_single {vinf : Place K (RatFunc K)}
    (hvinf : ∀ w : HeightOneSpectrum K[X], vinf ≠ Place.ofHeightOneSpectrum w)
    {p : K[X]} (hp : Irreducible p) :
    Divisor.degree (Finsupp.single (finitePlace K hp) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ))) = 0 := by
  rw [map_add, Divisor.degree_single, Divisor.degree_single,
    show (finitePlace K hp).deg = p.natDegree from
      deg_ofHeightOneSpectrum K (heightOneSpectrumOfIrreducible_asIdeal K hp),
    deg_eq_one_of_forall_ne_ofHeightOneSpectrum vinf hvinf]
  push_cast
  ring

end WFj

end AlgebraicCurve.RationalFunctionField

end

theorem solution {K : Type*} [Field K] (q : Polynomial K) : ∀ D : Divisor K (RatFunc K), (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) → Divisor.degree D = 0 := by
  classical
  obtain ⟨vinf, hvinf⟩ := AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum (K := K)
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro D hD
    have hzero : D = 0 := by
      ext v
      simp [hD v]
    rw [hzero, map_zero]
  · intro x hx D hD
    obtain ⟨r, -, rfl⟩ := Polynomial.isUnit_iff.mp hx
    have hC : (algebraMap K[X] (RatFunc K)) (Polynomial.C r) = algebraMap K (RatFunc K) r := by
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    have hzero : D = 0 := by
      ext v
      rw [hD v, hC, v.ord_algebraMap]
      simp
    rw [hzero, map_zero]
  · intro a p ha hp ih D hD
    have hp' : algebraMap K[X] (RatFunc K) p ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
    have ha' : algebraMap K[X] (RatFunc K) a ≠ 0 := RatFunc.algebraMap_ne_zero ha
    set Dp : Divisor K (RatFunc K) :=
      Finsupp.single (AlgebraicCurve.RationalFunctionField.WFj.finitePlace K hp.irreducible) (1 : ℤ)
        + Finsupp.single vinf (-(p.natDegree : ℤ)) with hDp_def
    have hDp : ∀ v : Place K (RatFunc K), Dp v = v.ord (algebraMap K[X] (RatFunc K) p) :=
      fun v => AlgebraicCurve.RationalFunctionField.WFj.single_add_single_apply_eq_ord hvinf
        hp.irreducible v
    have hDa : ∀ v : Place K (RatFunc K),
        (D - Dp) v = v.ord (algebraMap K[X] (RatFunc K) a) := by
      intro v
      rw [Finsupp.sub_apply, hD v, hDp v, map_mul, v.ord_mul hp' ha']
      ring
    have hdeg_p : Divisor.degree Dp = 0 :=
      AlgebraicCurve.RationalFunctionField.WFj.degree_single_add_single hvinf hp.irreducible
    have hdeg_a : Divisor.degree (D - Dp) = 0 := ih (D - Dp) hDa
    have hsplit : D = Dp + (D - Dp) := by abel
    rw [hsplit, map_add, hdeg_p, zero_add]
    exact hdeg_a

end S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_degree_eq_zero_of_forall_eq_ord_algebraMap (solution)
