-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f4b05cad-7b6b-5812-b878-e4f79dabf374

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp

set_option autoImplicit false

universe u

open IsLocalRing AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (f : F) [Fact (f ≠ 0)] (htf : Transcendental R f)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({f} : Set F)) F)
    (I : Ideal ↥(chartAlgFin R F f)) (hne : I ≠ ⊤) (hfI : jChartFin R F f ∈ I)
    (htor : ∀ y : ↥(chartAlgFin R F f) ⧸ I, algebraMap R (↥(chartAlgFin R F f) ⧸ I) ϖ * y = 0 → y = 0) :
    ∃ v : Place K₀ F, (∀ a : ↥(chartAlgFin R F f), (a : F) ∈ v.toValuationSubring) ∧
      ∀ a ∈ I, (a : F) ∈ v.toValuationSubring.nonunits := by
  classical
  have hf0 : (f : F) ≠ 0 := Fact.out

  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
  haveI := hM.isPrime
  obtain ⟨P, hPmin, -⟩ := Ideal.exists_minimalPrimes_le hIM
  haveI hPprime : P.IsPrime := hPmin.1.1
  have hIP : I ≤ P := hPmin.1.2

  have hϖP : algebraMap R ↥(chartAlgFin R F f) ϖ ∉ P := by
    intro hϖ'
    rw [Ideal.minimalPrimes_eq_comap] at hPmin
    obtain ⟨p', hp', hPp'⟩ := hPmin
    have hmem : Ideal.Quotient.mk I (algebraMap R _ ϖ) ∈ p' := by
      rw [← hPp'] at hϖ'; exact hϖ'
    have hnzd : Ideal.Quotient.mk I (algebraMap R ↥(chartAlgFin R F f) ϖ) ∈ nonZeroDivisors (↥(chartAlgFin R F f) ⧸ I) := by
      rw [mem_nonZeroDivisors_iff]
      have key : ∀ y, Ideal.Quotient.mk I (algebraMap R ↥(chartAlgFin R F f) ϖ) * y = 0 → y = 0 :=
        fun y hy => htor y (by rw [← Ideal.Quotient.mk_algebraMap]; exact hy)
      exact ⟨key, fun y hy => key y (by rw [mul_comm]; exact hy)⟩
    exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp') hmem hnzd

  have hRP : ∀ s : R, s ≠ 0 → algebraMap R ↥(chartAlgFin R F f) s ∉ P := by
    intro s hs hsP
    have hQ : (P.comap (algebraMap R ↥(chartAlgFin R F f))) ≠ ⊥ := fun h => by
      have : s ∈ P.comap (algebraMap R ↥(chartAlgFin R F f)) := hsP
      rw [h, Ideal.mem_bot] at this; exact hs this
    haveI : (P.comap (algebraMap R ↥(chartAlgFin R F f))).IsPrime := Ideal.IsPrime.comap _
    have hmax : (P.comap (algebraMap R ↥(chartAlgFin R F f))).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hQ
    have : ϖ ∈ P.comap (algebraMap R ↥(chartAlgFin R F f)) := by
      rw [IsLocalRing.eq_maximalIdeal hmax, hϖ]; exact Ideal.mem_span_singleton_self ϖ
    exact hϖP this

  have hone : (1 : ↥(chartAlgFin R F f)) ∉ P := fun h => hPprime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hb0 : ∀ b : ↥(chartAlgFin R F f), b ∉ P → (b : F) ≠ 0 := by
    intro b hb h0; apply hb; have : b = 0 := Subtype.ext h0; rw [this]; exact P.zero_mem
  let D : Subring F :=
    { carrier := {x | ∃ a b : ↥(chartAlgFin R F f), b ∉ P ∧ x * (b : F) = (a : F)}
      mul_mem' := by
        rintro x y ⟨a, b, hb, hx⟩ ⟨a', b', hb', hy⟩
        refine ⟨a * a', b * b', fun h => (hPprime.mem_or_mem h).elim hb hb', ?_⟩
        rw [Subalgebra.coe_mul, Subalgebra.coe_mul, ← hx, ← hy]; ring
      one_mem' := ⟨1, 1, hone, by simp⟩
      add_mem' := by
        rintro x y ⟨a, b, hb, hx⟩ ⟨a', b', hb', hy⟩
        refine ⟨a * b' + a' * b, b * b', fun h => (hPprime.mem_or_mem h).elim hb hb', ?_⟩
        rw [Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_mul, ← hx, ← hy]; ring
      zero_mem' := ⟨0, 1, hone, by simp⟩
      neg_mem' := by
        rintro x ⟨a, b, hb, hx⟩
        exact ⟨-a, b, hb, by rw [Subalgebra.coe_neg, ← hx]; ring⟩ }
  have hAD : ∀ a : ↥(chartAlgFin R F f), (a : F) ∈ D := fun a => ⟨a, 1, hone, by simp⟩
  letI algAD : Algebra ↥(chartAlgFin R F f) ↥D :=
    (RingHom.codRestrict ((chartAlgFin R F f).val.toRingHom) D (fun a => hAD a)).toAlgebra
  have halgAD : ∀ a : ↥(chartAlgFin R F f), ((algebraMap ↥(chartAlgFin R F f) ↥D a : ↥D) : F) = (a : F) :=
    fun _ => rfl
  haveI hlocD : IsLocalization.AtPrime ↥D P :=
    { map_units := by
        rintro ⟨b, hb⟩
        have hb' : b ∉ P := hb
        refine isUnit_iff_exists_inv.mpr ⟨⟨(b : F)⁻¹, 1, b, hb', ?_⟩, Subtype.ext ?_⟩
        · rw [inv_mul_cancel₀ (hb0 b hb')]; simp
        · show (b : F) * (b : F)⁻¹ = 1
          exact mul_inv_cancel₀ (hb0 b hb')
      surj := by
        rintro ⟨x, a, b, hb, hx⟩
        exact ⟨(a, ⟨b, hb⟩), Subtype.ext hx⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : (x : F) = (y : F) := congrArg (fun z : ↥D => (z : F)) h
        rw [Subtype.ext this]⟩ }
  haveI : IsLocalRing ↥D := IsLocalization.AtPrime.isLocalRing ↥D P
  have hDunit : ∀ a : ↥(chartAlgFin R F f), a ∉ P → IsUnit (algebraMap ↥(chartAlgFin R F f) ↥D a) :=
    fun a ha => IsLocalization.map_units ↥D (⟨a, ha⟩ : ↥P.primeCompl)
  have hDnonunit : ∀ a : ↥(chartAlgFin R F f), a ∈ P → ¬ IsUnit (algebraMap ↥(chartAlgFin R F f) ↥D a) :=
    fun a ha => (IsLocalRing.mem_maximalIdeal _).mp ((IsLocalization.AtPrime.to_map_mem_maximal_iff ↥D P a).mpr ha)

  have hK : ∀ c : K₀, algebraMap K₀ F c ∈ D := by
    intro c
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero hs
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    have hr : algebraMap R F r ∈ D := by
      have : algebraMap R F r = ((algebraMap R ↥(chartAlgFin R F f) r : ↥(chartAlgFin R F f)) : F) := rfl
      rw [this]; exact hAD _
    have hsD : (algebraMap R F s)⁻¹ ∈ D := by
      obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp (hDunit _ (hRP s hs0))
      have : (algebraMap R F s)⁻¹ = ((u : ↥D) : F) := by
        have h1 := congrArg (fun z : ↥D => (z : F)) hu
        simp only [Subring.coe_mul, halgAD, OneMemClass.coe_one] at h1

        have h2 : algebraMap R F (s : R) * (u : F) = 1 := h1
        exact (eq_inv_of_mul_eq_one_right h2).symm ▸ rfl
      rw [this]; exact u.2
    rw [div_eq_mul_inv]
    exact D.mul_mem hr hsD

  haveI := hFD
  obtain ⟨Q, hQD, hQnu⟩ := AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
    (K := K₀) f D hK ⟨algebraMap ↥(chartAlgFin R F f) ↥D (jChartFin R F f),
      fun h => hf0 (congrArg (fun z : ↥D => (z : F)) h), hDnonunit _ (hIP hfI)⟩
  refine ⟨Q, fun a => hQD _ (hAD a), fun a ha => ?_⟩
  have := (hQnu (algebraMap ↥(chartAlgFin R F f) ↥D a)).mpr (hDnonunit a (hIP ha))
  exact this

end S_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_exists_place_forall_mem_and_forall_mem_nonunits_of_forall_mul_eq_zero_imp (solution)
