-- Prove2me | solution 1 for AlgebraicCurve.RationalFunctionField.isPrincipal_of_degree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/714bd581-28a6-5639-8c2a-cdfe52f58215

import Mathlib.FieldTheory.RatFunc.Degree
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_subsingleton_setOf_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_ord_ofHeightOneSpectrum_ne_zero_iff
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_ofHeightOneSpectrum_of_span
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_deg_ofHeightOneSpectrum
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_forall_ne_ofHeightOneSpectrum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero.AlgebraicCurve IsDedekindDomain Polynomial"

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_one Divisor Divisor.degree Place.ofHeightOneSpectrum Place.ord_ofHeightOneSpectrum_ne_zero_iff Divisor.degree_eq_sum"
namespace RationalFunctionField
p2m_export "AlgebraicCurve.RationalFunctionField" "subsingleton_setOf_forall_ne_ofHeightOneSpectrum ord_ofHeightOneSpectrum_of_span ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum deg_ofHeightOneSpectrum deg_eq_one_of_forall_ne_ofHeightOneSpectrum"
namespace W2B
p2m_open "AlgebraicCurve.RationalFunctionField AlgebraicCurve"

variable {K : Type*} [Field K]

theorem ord_prod {F : Type*} [Field F] [Algebra K F] (v : Place K F) {ι : Type*} (s : Finset ι)
    (g : ι → F) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hg a (Finset.mem_cons_self ..))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_cons_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_cons_of_mem hi)]

abbrev IsFinite (v : Place K (RatFunc K)) : Prop :=
  ∃ w : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum w

def spec {v : Place K (RatFunc K)} (hv : IsFinite v) : HeightOneSpectrum K[X] := hv.choose

theorem eq_ofHeightOneSpectrum_spec {v : Place K (RatFunc K)} (hv : IsFinite v) :
    v = Place.ofHeightOneSpectrum (spec hv) := hv.choose_spec

open Classical in

def gen (v : Place K (RatFunc K)) : K[X] :=
  if hv : IsFinite v then Submodule.IsPrincipal.generator (spec hv).asIdeal else 1

theorem span_gen {v : Place K (RatFunc K)} (hv : IsFinite v) :
    (spec hv).asIdeal = Ideal.span {gen v} := by
  simp only [gen, dif_pos hv]
  exact (Ideal.span_singleton_generator _).symm

theorem gen_of_not_isFinite {v : Place K (RatFunc K)} (hv : ¬ IsFinite v) : gen v = 1 := by
  simp only [gen, dif_neg hv]

theorem gen_ne_zero (v : Place K (RatFunc K)) : gen v ≠ 0 := by
  by_cases hv : IsFinite v
  · intro h
    exact (spec hv).ne_bot (by rw [span_gen hv, h, Ideal.span_singleton_eq_bot])
  · rw [gen_of_not_isFinite hv]; exact one_ne_zero

theorem algebraMap_gen_ne_zero (v : Place K (RatFunc K)) :
    algebraMap K[X] (RatFunc K) (gen v) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (gen_ne_zero v)

open Classical in

theorem ord_gen_of_isFinite {u : Place K (RatFunc K)} (hu : IsFinite u) (v : Place K (RatFunc K)) :
    u.ord (algebraMap K[X] (RatFunc K) (gen v)) = if v = u then 1 else 0 := by
  classical
  by_cases hvu : v = u
  · subst hvu
    rw [if_pos rfl]
    have h := ord_ofHeightOneSpectrum_of_span (spec hu) (gen_ne_zero v) (span_gen hu)
    rwa [← eq_ofHeightOneSpectrum_spec hu] at h
  rw [if_neg hvu]
  by_cases hv : IsFinite v
  ·
    by_contra hne
    rw [eq_ofHeightOneSpectrum_spec hu] at hne
    have hmem : gen v ∈ (spec hu).asIdeal :=
      (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) (spec hu)
        (gen_ne_zero v)).mp hne
    have hle : (spec hv).asIdeal ≤ (spec hu).asIdeal := by
      rw [span_gen hv, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have heq : (spec hv).asIdeal = (spec hu).asIdeal :=
      (spec hv).isMaximal.eq_of_le (spec hu).isPrime.ne_top hle
    exact hvu (by rw [eq_ofHeightOneSpectrum_spec hv, eq_ofHeightOneSpectrum_spec hu,
      HeightOneSpectrum.ext heq])
  · rw [gen_of_not_isFinite hv, map_one, Place.ord_one]

open Classical in

theorem ord_gen_of_not_isFinite {u : Place K (RatFunc K)} (hu : ¬ IsFinite u)
    (v : Place K (RatFunc K)) :
    u.ord (algebraMap K[X] (RatFunc K) (gen v)) = -(v.deg : ℤ) + if v = u then 1 else 0 := by
  classical
  have hu' : ∀ w : HeightOneSpectrum K[X], u ≠ Place.ofHeightOneSpectrum w :=
    fun w h => hu ⟨w, h⟩
  by_cases hv : IsFinite v
  · have hvu : v ≠ u := fun h => hu (h ▸ hv)
    rw [if_neg hvu, add_zero,
      ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum u hu' (algebraMap_gen_ne_zero v),
      RatFunc.intDegree_polynomial]
    conv_rhs => rw [eq_ofHeightOneSpectrum_spec hv, deg_ofHeightOneSpectrum K (span_gen hv)]
  ·
    have hv' : ∀ w : HeightOneSpectrum K[X], v ≠ Place.ofHeightOneSpectrum w :=
      fun w h => hv ⟨w, h⟩
    have hvu : v = u := subsingleton_setOf_forall_ne_ofHeightOneSpectrum hv' hu'
    rw [if_pos hvu, gen_of_not_isFinite hv, map_one, Place.ord_one,
      deg_eq_one_of_forall_ne_ofHeightOneSpectrum v hv']
    norm_num

def genFactor (D : Divisor K (RatFunc K)) (v : Place K (RatFunc K)) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (gen v) ^ (D v)

theorem genFactor_ne_zero (D : Divisor K (RatFunc K)) (v : Place K (RatFunc K)) :
    genFactor D v ≠ 0 :=
  zpow_ne_zero _ (algebraMap_gen_ne_zero v)

theorem isPrincipal_of_degree_eq_zero' (D : Divisor K (RatFunc K)) (hD : Divisor.degree D = 0) :
    D.IsPrincipal := by
  classical
  refine ⟨∏ v ∈ D.support, genFactor D v,
    Finset.prod_ne_zero_iff.mpr fun v _ => genFactor_ne_zero D v, fun u => ?_⟩
  rw [ord_prod u _ _ fun v _ => genFactor_ne_zero D v]
  have hfactor : ∀ v : Place K (RatFunc K),
      u.ord (genFactor D v) = D v * u.ord (algebraMap K[X] (RatFunc K) (gen v)) := by
    intro v
    rw [genFactor, u.ord_zpow]
  have hdeg : ∑ v ∈ D.support, D v * (v.deg : ℤ) = 0 := by
    rw [← Divisor.degree_eq_sum D, hD]
  by_cases hu : IsFinite u
  ·
    have hcong : ∀ v ∈ D.support, u.ord (genFactor D v) = if v = u then D u else 0 := by
      intro v _
      rw [hfactor v, ord_gen_of_isFinite hu v]
      by_cases hvu : v = u
      · rw [if_pos hvu, if_pos hvu, hvu, mul_one]
      · rw [if_neg hvu, if_neg hvu, mul_zero]
    rw [Finset.sum_congr rfl hcong, Finset.sum_ite_eq']
    by_cases hmem : u ∈ D.support
    · rw [if_pos hmem]
    · simp [Finsupp.notMem_support_iff.mp hmem]
  ·
    have hcong : ∀ v ∈ D.support, u.ord (genFactor D v)
        = -(D v * (v.deg : ℤ)) + (if v = u then D v else 0) := by
      intro v _
      rw [hfactor v, ord_gen_of_not_isFinite hu v]
      by_cases hv : v = u
      · rw [if_pos hv, if_pos hv]; ring
      · rw [if_neg hv, if_neg hv]; ring
    rw [Finset.sum_congr rfl hcong, Finset.sum_add_distrib, Finset.sum_neg_distrib, hdeg,
      neg_zero, zero_add, Finset.sum_ite_eq']
    by_cases hmem : u ∈ D.support
    · rw [if_pos hmem]
    · simp [Finsupp.notMem_support_iff.mp hmem]

end AlgebraicCurve.RationalFunctionField.W2B

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero.AlgebraicCurve in

theorem solution {K : Type*} [Field K] (D : Divisor K (RatFunc K)) (hD : Divisor.degree D = 0) : D.IsPrincipal :=
  AlgebraicCurve.RationalFunctionField.W2B.isPrincipal_of_degree_eq_zero' D hD

end S_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_RationalFunctionField_isPrincipal_of_degree_eq_zero (solution)
