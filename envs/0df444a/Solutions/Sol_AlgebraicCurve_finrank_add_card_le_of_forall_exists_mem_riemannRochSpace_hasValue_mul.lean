-- Prove2me | solution 1 for AlgebraicCurve.finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/25444c38-7874-5699-a76c-ffaa4d1cc8e3

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul.AlgebraicCurve"

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
    {ι : Type*} [Fintype ι]
    (E₁ E₂ : Divisor k F)
    [FiniteDimensional k ↥(riemannRochSpace E₁)] [FiniteDimensional k ↥(riemannRochSpace E₂)]
    (v₁ v₂ : ι → Place k F) (t₁ t₂ : ι → F)
    (ht₁ : ∀ i, t₁ i ≠ 0 ∧ (v₁ i).ord (t₁ i) = E₁ (v₁ i))
    (ht₂ : ∀ i, t₂ i ≠ 0 ∧ (v₂ i).ord (t₂ i) = E₂ (v₂ i))
    (lam : ι → k)
    (hsurj : ∀ c : ι → k, ∃ p ∈ riemannRochSpace E₁, ∀ i, (v₁ i).HasValue (t₁ i * p) (c i))
    (T : Submodule k (F × F))
    (hT : ∀ p, p ∈ T ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : k, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c) :
    FiniteDimensional k ↥T ∧
      Module.finrank k ↥T + Fintype.card ι ≤
        Module.finrank k ↥(riemannRochSpace E₁) + Module.finrank k ↥(riemannRochSpace E₂) := by
  classical

  have hex₁ : ∀ (p : ↥(riemannRochSpace E₁)) (i : ι), ∃ a : k, (v₁ i).HasValue (t₁ i * (p : F)) a :=
    fun p i => EvalCount.exists_hasValue_twist_mul (EvalCount.surjective_algebraMap_residueField _)
      (ht₁ i).1 (ht₁ i).2 p.2
  have hex₂ : ∀ (p : ↥(riemannRochSpace E₂)) (i : ι), ∃ a : k, (v₂ i).HasValue (t₂ i * (p : F)) a :=
    fun p i => EvalCount.exists_hasValue_twist_mul (EvalCount.surjective_algebraMap_residueField _)
      (ht₂ i).1 (ht₂ i).2 p.2
  choose val₁ hval₁ using hex₁
  choose val₂ hval₂ using hex₂
  let V₁ : ↥(riemannRochSpace E₁) →ₗ[k] (ι → k) :=
    { toFun := val₁
      map_add' := fun p q => funext fun i => (hval₁ (p + q) i).unique (by
        have h := EvalCount.hvAdd (hval₁ p i) (hval₁ q i)
        rwa [← mul_add] at h)
      map_smul' := fun c p => funext fun i => (hval₁ (c • p) i).unique (by
        have h := EvalCount.hvSmul c (hval₁ p i)
        rwa [← mul_smul_comm] at h) }
  let V₂ : ↥(riemannRochSpace E₂) →ₗ[k] (ι → k) :=
    { toFun := val₂
      map_add' := fun p q => funext fun i => (hval₂ (p + q) i).unique (by
        have h := EvalCount.hvAdd (hval₂ p i) (hval₂ q i)
        rwa [← mul_add] at h)
      map_smul' := fun c p => funext fun i => (hval₂ (c • p) i).unique (by
        have h := EvalCount.hvSmul c (hval₂ p i)
        rwa [← mul_smul_comm] at h) }
  let Dg : (ι → k) →ₗ[k] (ι → k) := LinearMap.pi fun i => lam i • LinearMap.proj i
  let Φ : (↥(riemannRochSpace E₁) × ↥(riemannRochSpace E₂)) →ₗ[k] (ι → k) :=
    V₁.comp (LinearMap.fst k _ _) - Dg.comp (V₂.comp (LinearMap.snd k _ _))
  have hΦ : ∀ (p : ↥(riemannRochSpace E₁)) (q : ↥(riemannRochSpace E₂)) (i : ι),
      Φ (p, q) i = val₁ p i - lam i * val₂ q i := by
    intro p q i
    simp [Φ, V₁, V₂, Dg]

  let j : ↥T →ₗ[k] (↥(riemannRochSpace E₁) × ↥(riemannRochSpace E₂)) :=
    { toFun := fun x => (⟨x.1.1, ((hT x.1).mp x.2).1⟩, ⟨x.1.2, ((hT x.1).mp x.2).2.1⟩)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => ((z.1 : ↥(riemannRochSpace E₁)) : F)) h
    · exact congrArg (fun z => ((z.2 : ↥(riemannRochSpace E₂)) : F)) h
  have hjker : ∀ x : ↥T, j x ∈ LinearMap.ker Φ := by
    intro x
    obtain ⟨-, -, hx⟩ := (hT x.1).mp x.2
    rw [LinearMap.mem_ker]
    funext i
    obtain ⟨c, hc₁, hc₂⟩ := hx i
    rw [hΦ, Pi.zero_apply]
    have e₁ : val₁ (j x).1 i = lam i * c := (hval₁ (j x).1 i).unique hc₁
    have e₂ : val₂ (j x).2 i = c := (hval₂ (j x).2 i).unique hc₂
    rw [e₁, e₂, sub_self]
  have hfinT : FiniteDimensional k ↥T := Module.Finite.of_injective j hj
  let j' : ↥T →ₗ[k] ↥(LinearMap.ker Φ) := LinearMap.codRestrict (LinearMap.ker Φ) j hjker
  have hj' : Function.Injective j' := fun x y h => hj (congrArg Subtype.val h)
  have hT_le : Module.finrank k ↥T ≤ Module.finrank k ↥(LinearMap.ker Φ) :=
    LinearMap.finrank_le_finrank_of_injective hj'

  have hrange : LinearMap.range Φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro d
    obtain ⟨p, hp, hpv⟩ := hsurj d
    refine ⟨(⟨p, hp⟩, 0), funext fun i => ?_⟩
    rw [hΦ]
    have e₁ : val₁ ⟨p, hp⟩ i = d i := (hval₁ _ i).unique (hpv i)
    have e₂ : val₂ 0 i = 0 := by
      have h := congrFun (map_zero V₂) i
      exact h
    rw [e₁, e₂, mul_zero, sub_zero]
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_prod] at hrank
  refine ⟨hfinT, ?_⟩
  omega

end S_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul
end P2MW
export P2MW.S_AlgebraicCurve_finrank_add_card_le_of_forall_exists_mem_riemannRochSpace_hasValue_mul (solution)
