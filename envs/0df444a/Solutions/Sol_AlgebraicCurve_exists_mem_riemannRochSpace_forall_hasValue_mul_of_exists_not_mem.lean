-- Prove2me | solution 1 for AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d07fcad1-d482-518e-8c85-9fb8551cfb5f

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "riemannRochSpace mem_riemannRochSpace_iff Place Divisor IsCurveOver IsCurveOver.finiteResidue Place.hasValue_algebraMap"
namespace EvalCount
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf

theorem mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem hasValue_zero_of_ord_pos (v : Place K F) {f : F} (h : f = 0 ∨ 0 < v.ord f) :
    v.HasValue f 0 := by
  rcases h with rfl | h
  · simpa using Place.hasValue_algebraMap v (0 : K)
  · have hf : f ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : v.adicValuation f < 1 := by
      rw [v.adicValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hmem : f ∈ v.toValuationSubring := v.mem_iff_adicValuation_le_one.mpr hlt.le
    refine ⟨hmem, ?_⟩
    have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
    rw [map_zero, IsLocalRing.residue_eq_zero_iff]
    exact hmax

theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 :=
  hasValue_zero_of_ord_pos v (Or.inl rfl)

theorem hvAdd {v : Place K F} {f g : F} {a b : K} (hf : v.HasValue f a) (hg : v.HasValue g b) :
    v.HasValue (f + g) (a + b) := by
  obtain ⟨hfm, hfr⟩ := hf
  obtain ⟨hgm, hgr⟩ := hg
  refine ⟨add_mem hfm hgm, ?_⟩
  have e : (⟨f + g, add_mem hfm hgm⟩ : v.toValuationSubring) = ⟨f, hfm⟩ + ⟨g, hgm⟩ := rfl
  rw [e, map_add, hfr, hgr, map_add]

theorem hvSmul {v : Place K F} {f : F} {a : K} (c : K) (hf : v.HasValue f a) :
    v.HasValue (c • f) (c * a) := by
  rw [Algebra.smul_def]
  exact (Place.hasValue_algebraMap v c).mul hf

theorem hvSum {v : Place K F} {ι : Type*} (s : Finset ι) (f : ι → F) (b : ι → K)
    (h : ∀ j ∈ s, v.HasValue (f j) (b j)) :
    v.HasValue (∑ j ∈ s, f j) (∑ j ∈ s, b j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValue_zero v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact hvAdd (h a (Finset.mem_insert_self a s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem riemannRochSpace_mono {D D' : Divisor K F} (h : D ≤ D') :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((neg_le_neg (Finsupp.le_def.mp h v)).trans h0)

theorem ne_zero_and_ord_add_eq_zero {D : Divisor K F} {f : F} {w : Place K F}
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    f ≠ 0 ∧ w.ord f + D w = 0 := by
  rw [mem_riemannRochSpace_iff] at hf hf'
  push Not at hf'
  obtain ⟨v, hf0, hv⟩ := hf'
  have hvw : v = w := by
    by_contra hne
    have h1 : (D - Finsupp.single w 1 : Divisor K F) v = D v := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hne, sub_zero]
    rcases hf v with h | h
    · exact hf0 h
    · rw [h1] at hv
      exact absurd h (not_le.mpr hv)
  subst hvw
  refine ⟨hf0, ?_⟩
  rcases hf v with h | h
  · exact absurd h hf0
  · rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hv
    omega

theorem exists_mem_riemannRochSpace_not_mem_of_finrank_lt {D D' : Divisor K F}
    [FiniteDimensional K ↥(riemannRochSpace D')]
    (h : Module.finrank K ↥(riemannRochSpace D') < Module.finrank K ↥(riemannRochSpace D)) :
    ∃ p ∈ riemannRochSpace D, p ∉ riemannRochSpace D' := by
  by_contra hcon
  push Not at hcon
  have hle : riemannRochSpace D ≤ riemannRochSpace D' := fun p hp => hcon p hp
  exact absurd (LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hle)) (not_le.mpr h)

theorem twist_mul_mem {E : Divisor K F} {v : Place K F} {t p : F} (ht0 : t ≠ 0) (ht : v.ord t = E v)
    (hp : p ∈ riemannRochSpace E) : t * p ∈ v.toValuationSubring := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [mul_zero]; exact zero_mem _
  · apply mem_of_ord_nonneg v (mul_ne_zero ht0 hp0)
    rcases (mem_riemannRochSpace_iff.mp hp) v with h | h
    · exact absurd h hp0
    · rw [v.ord_mul ht0 hp0, ht]
      omega

theorem exists_hasValue_twist_mul {E : Divisor K F} {v : Place K F} {t p : F}
    (hrat : Function.Surjective (algebraMap K v.ResidueField))
    (ht0 : t ≠ 0) (ht : v.ord t = E v) (hp : p ∈ riemannRochSpace E) :
    ∃ a : K, v.HasValue (t * p) a := by
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hrat (twist_mul_mem ht0 ht hp)
  exact ⟨a, ha⟩

section Closed

variable [IsAlgClosed K] [IsCurveOver K F]

theorem surjective_algebraMap_residueField (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

end Closed

end AlgebraicCurve.EvalCount

theorem solution
    {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : Divisor k F) (v : ι → Place k F) (hv : Function.Injective v) (t : ι → F)
    (ht : ∀ i, t i ≠ 0 ∧ (v i).ord (t i) = E (v i))
    (hstep : ∀ i, ∃ g ∈ riemannRochSpace (E - ∑ j ∈ Finset.univ.erase i, Finsupp.single (v j) 1),
      g ∉ riemannRochSpace (E - ∑ j, Finsupp.single (v j) 1))
    (c : ι → k) :
    ∃ p ∈ riemannRochSpace E, ∀ i, (v i).HasValue (t i * p) (c i) := by
  classical
  choose g hg hg' using hstep

  have hS : ∀ (s : Finset ι) (l : ι), (∑ j ∈ s, Finsupp.single (v j) (1 : ℤ)) (v l) = if l ∈ s then 1 else 0 := by
    intro s l
    rw [Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply, hv.eq_iff]
    rw [Finset.sum_ite_eq']
  have hSnonneg : ∀ s : Finset ι, (0 : Divisor k F) ≤ ∑ j ∈ s, Finsupp.single (v j) (1 : ℤ) :=
    fun s => Finset.sum_nonneg fun j _ => Finsupp.single_nonneg.mpr zero_le_one
  have hEfull : ∀ i, E - ∑ j, Finsupp.single (v j) (1 : ℤ)
      = (E - ∑ j ∈ Finset.univ.erase i, Finsupp.single (v j) 1) - Finsupp.single (v i) 1 := by
    intro i
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), sub_sub]

  have hkey : ∀ i, g i ≠ 0 ∧ (v i).ord (g i) = - E (v i) := by
    intro i
    have h := EvalCount.ne_zero_and_ord_add_eq_zero (hg i) (by rw [← hEfull i]; exact hg' i)
    refine ⟨h.1, ?_⟩
    have hc : (E - ∑ j ∈ Finset.univ.erase i, Finsupp.single (v j) (1 : ℤ)) (v i) = E (v i) := by
      rw [Finsupp.sub_apply, hS]
      simp
    rw [hc] at h
    omega
  have hoff : ∀ i l, l ≠ i → -E (v l) + 1 ≤ (v l).ord (g i) := by
    intro i l hl
    rcases (mem_riemannRochSpace_iff.mp (hg i)) (v l) with h | h
    · exact absurd h (hkey i).1
    · rw [Finsupp.sub_apply, hS, if_pos (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩)] at h
      omega

  have hdiag : ∀ i, ∃ a : k, a ≠ 0 ∧ (v i).HasValue (t i * g i) a := by
    intro i
    have hne : t i * g i ≠ 0 := mul_ne_zero (ht i).1 (hkey i).1
    have h0 : (v i).ord (t i * g i) = 0 := by
      rw [(v i).ord_mul (ht i).1 (hkey i).1, (ht i).2, (hkey i).2]; ring
    obtain ⟨hm, hu⟩ := (v i).exists_isUnit_of_ord_eq_zero hne h0
    obtain ⟨a, ha, hane⟩ := (v i).exists_hasValue_of_surjective (EvalCount.surjective_algebraMap_residueField _) hm
    exact ⟨a, hane hu, ha⟩
  choose a ha0 ha using hdiag
  have hzero : ∀ i l, l ≠ i → (v l).HasValue (t l * g i) 0 := by
    intro i l hl
    apply EvalCount.hasValue_zero_of_ord_pos
    right
    rw [(v l).ord_mul (ht l).1 (hkey i).1, (ht l).2]
    have := hoff i l hl
    omega

  refine ⟨∑ j, (c j * (a j)⁻¹) • g j, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact EvalCount.riemannRochSpace_mono (sub_le_self _ (hSnonneg _)) (hg j)
  · intro i
    have hsum := EvalCount.hvSum (v := v i) Finset.univ (fun j => (c j * (a j)⁻¹) • (t i * g j))
      (fun j => (c j * (a j)⁻¹) * (if j = i then a j else 0)) (fun j _ => by
        by_cases hji : j = i
        · subst hji
          rw [if_pos rfl]
          exact EvalCount.hvSmul _ (ha j)
        · rw [if_neg hji]
          exact EvalCount.hvSmul (c j * (a j)⁻¹) (hzero j i (Ne.symm hji)))
    have hval : (∑ j, (c j * (a j)⁻¹) * (if j = i then a j else 0)) = c i := by
      simp_rw [mul_ite, mul_zero]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ i), inv_mul_cancel_right₀ (ha0 i)]
    rw [hval] at hsum
    have e : t i * ∑ j, (c j * (a j)⁻¹) • g j = ∑ j, (c j * (a j)⁻¹) • (t i * g j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm]
    rw [e]
    exact hsum

end S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem
end P2MW
export P2MW.S_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_mul_of_exists_not_mem (solution)
