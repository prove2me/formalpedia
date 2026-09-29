-- Prove2me | solution 1 for AlgebraicGeometry.two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/714db6f9-03d0-5a76-8dea-de47efc690a4

import Mathlib
import Theorems.Thm_MvPolynomial_CrossingQuotient_existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing MvPolynomial

namespace VertexDim

theorem algebraMap_mem_nonZeroDivisors (O : Type) [CommRing O] [IsDomain O] (ϖ : O) (hϖ : Prime ϖ) (hϖu : ¬ IsUnit ϖ) (a : O) :
    algebraMap O (CrossingQuotient O a) ϖ ∈ nonZeroDivisors (CrossingQuotient O a) := by
  classical
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  obtain ⟨f, rfl⟩ := CrossingQuotient.mk_surjective a b

  have hmem : C ϖ * f ∈ Ideal.span {(X 0 * X 1 - C a : (MvPolynomial (Fin 2) O))} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap O (CrossingQuotient O a) ϖ = CrossingQuotient.mk a (C ϖ) := (CrossingQuotient.mk_C_eq_algebraMap a ϖ).symm
    rw [mul_comm] at hb
    rw [RingHom.map_mul, ← CrossingQuotient.mk_apply, ← CrossingQuotient.mk_apply, ← this]
    exact hb
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hmem

  have hCprime : Prime (C ϖ : (MvPolynomial (Fin 2) O)) := (MvPolynomial.prime_C_iff (σ := Fin 2)).mpr hϖ
  have hndvd : ¬ (C ϖ : (MvPolynomial (Fin 2) O)) ∣ (X 0 * X 1 - C a) := by
    rintro ⟨h, hh⟩
    have h1 := congrArg (MvPolynomial.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) hh
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sub, MvPolynomial.coeff_C,
      if_neg (by
        intro h0
        have := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h0
        simp at this),
      sub_zero, show (X 0 * X 1 : (MvPolynomial (Fin 2) O)) = MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 by
        rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul],
      MvPolynomial.coeff_monomial, if_pos rfl] at h1
    exact hϖu (IsUnit.of_mul_eq_one _ h1.symm)
  have hdvd : (C ϖ : (MvPolynomial (Fin 2) O)) ∣ g * (X 0 * X 1 - C a) := ⟨f, by rw [hg]⟩
  rcases hCprime.dvd_or_dvd hdvd with hg' | h'
  · obtain ⟨g', rfl⟩ := hg'
    have hC0 : (C ϖ : (MvPolynomial (Fin 2) O)) ≠ 0 := hCprime.ne_zero
    have : f = g' * (X 0 * X 1 - C a) := by
      apply mul_left_cancel₀ hC0
      rw [← hg, mul_assoc]
    rw [CrossingQuotient.mk_apply, Ideal.Quotient.eq_zero_iff_mem, this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  · exact absurd h' hndvd

end VertexDim

open VertexDim in
set_option maxHeartbeats 3200000 in
theorem solution
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (E : ℕ) (hE : 1 ≤ E) (w : Oˣ) (a : O) (ha : a = (w : O) * ϖ ^ E)
    (m : ↥(CrossingQuotient.crossingScheme a))
    (hm : CrossingQuotient.U a ∈ m.asIdeal ∧ CrossingQuotient.V a ∈ m.asIdeal) :
    2 ≤ ringKrullDim ((CrossingQuotient.crossingScheme a).presheaf.stalk m) := by
  classical
  obtain ⟨hmU, hmV⟩ := hm
  haveI : m.asIdeal.IsPrime := m.isPrime

  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Ideal.span_singleton_zero] at hϖ
    exact (IsDiscreteValuationRing.not_isField O) (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hϖ)
  have hϖmem : ϖ ∈ IsLocalRing.maximalIdeal O := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hϖu : ¬ IsUnit ϖ := (IsLocalRing.mem_maximalIdeal ϖ).mp hϖmem
  have hϖprime : Prime ϖ := (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal ϖ hϖ0 hϖ).prime

  have hamem : algebraMap O (CrossingQuotient O a) a ∈ m.asIdeal := by
    rw [← CrossingQuotient.U_mul_V]; exact Ideal.mul_mem_left _ _ hmV
  have hϖm : algebraMap O (CrossingQuotient O a) ϖ ∈ m.asIdeal := by
    have hamem' : algebraMap O (CrossingQuotient O a) ((w : O) * ϖ ^ E) ∈ m.asIdeal := by rw [← ha]; exact hamem
    rw [map_mul, map_pow] at hamem'
    rcases (Ideal.IsPrime.mem_or_mem inferInstance hamem') with hw | hpow
    · exact absurd (hw) (fun h => (Ideal.IsPrime.ne_top inferInstance)
        (Ideal.eq_top_of_isUnit_mem _ h ((Units.isUnit w).map _)))
    · exact Ideal.IsPrime.mem_of_pow_mem inferInstance E hpow

  let π : O →+* (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.mk _
  have hπa : π a = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, ha]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hϖmem E hE)
  obtain ⟨χ₁, ⟨hχ₁O, hχ₁U, hχ₁V⟩, -⟩ :=
    MvPolynomial.CrossingQuotient.existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq
      ((Polynomial.C : (O ⧸ IsLocalRing.maximalIdeal O) →+* Polynomial (O ⧸ IsLocalRing.maximalIdeal O)).comp π) a (0 : Polynomial (O ⧸ IsLocalRing.maximalIdeal O)) Polynomial.X
      (by rw [zero_mul, RingHom.comp_apply, hπa, map_zero])
  obtain ⟨χ₂, ⟨hχ₂O, hχ₂U, hχ₂V⟩, -⟩ :=
    MvPolynomial.CrossingQuotient.existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq
      π a (0 : (O ⧸ IsLocalRing.maximalIdeal O)) 0 (by rw [zero_mul, hπa])
  haveI : IsDomain (Polynomial (O ⧸ IsLocalRing.maximalIdeal O)) := inferInstance
  let p₁ : Ideal (CrossingQuotient O a) := RingHom.ker χ₁
  haveI hp₁ : p₁.IsPrime := RingHom.ker_isPrime χ₁

  have hker₂ : RingHom.ker χ₂ ≤ m.asIdeal := by
    intro b hb
    obtain ⟨f, rfl⟩ := CrossingQuotient.mk_surjective a b

    have hsplit : f - C (MvPolynomial.coeff 0 f) ∈ Ideal.span (Set.range (X : Fin 2 → (MvPolynomial (Fin 2) O))) := by
      rw [show Set.range (X : Fin 2 → (MvPolynomial (Fin 2) O)) = X '' Set.univ from Set.image_univ.symm, MvPolynomial.mem_ideal_span_X_image]
      intro mo hmo
      by_contra hcon
      push_neg at hcon
      have hmo0 : mo = 0 := by ext i; simpa using hcon i (Set.mem_univ i)
      rw [hmo0, MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, MvPolynomial.coeff_C, if_pos rfl, sub_self] at hmo
      exact hmo rfl
    have hXm : Ideal.map (CrossingQuotient.mk a) (Ideal.span (Set.range (X : Fin 2 → (MvPolynomial (Fin 2) O)))) ≤ m.asIdeal := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      fin_cases i
      · exact hmU
      · exact hmV
    have h1 : CrossingQuotient.mk a (f - C (MvPolynomial.coeff 0 f)) ∈ m.asIdeal := hXm (Ideal.mem_map_of_mem _ hsplit)
    have h2 : χ₂ (CrossingQuotient.mk a (f - C (MvPolynomial.coeff 0 f))) = 0 := by

      have : Ideal.map (CrossingQuotient.mk a) (Ideal.span (Set.range (X : Fin 2 → (MvPolynomial (Fin 2) O)))) ≤ RingHom.ker χ₂ := by
        rw [Ideal.map_span, Ideal.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        fin_cases i
        · exact hχ₂U
        · exact hχ₂V
      exact this (Ideal.mem_map_of_mem _ hsplit)
    have h3 : χ₂ (CrossingQuotient.mk a (C (MvPolynomial.coeff 0 f))) = 0 := by
      have hb' : χ₂ (CrossingQuotient.mk a f) = 0 := hb
      have : CrossingQuotient.mk a f = CrossingQuotient.mk a (C (MvPolynomial.coeff 0 f)) + CrossingQuotient.mk a (f - C (MvPolynomial.coeff 0 f)) := by
        rw [← map_add, add_sub_cancel]
      rw [this, map_add, h2, add_zero] at hb'
      exact hb'
    have h4 : CrossingQuotient.mk a (C (MvPolynomial.coeff 0 f)) ∈ m.asIdeal := by
      have hc : CrossingQuotient.mk a (C (MvPolynomial.coeff 0 f)) = algebraMap O (CrossingQuotient O a) (MvPolynomial.coeff 0 f) :=
        CrossingQuotient.mk_C_eq_algebraMap a _
      rw [hc] at h3 ⊢
      have h5 : π (MvPolynomial.coeff 0 f) = 0 := by rw [← hχ₂O]; exact h3
      rw [Ideal.Quotient.eq_zero_iff_mem, hϖ] at h5
      obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.mp h5
      rw [← hc', map_mul]
      exact Ideal.mul_mem_left _ _ hϖm
    have : CrossingQuotient.mk a f = CrossingQuotient.mk a (C (MvPolynomial.coeff 0 f)) + CrossingQuotient.mk a (f - C (MvPolynomial.coeff 0 f)) := by
      rw [← map_add, add_sub_cancel]
    rw [this]
    exact add_mem h4 h1

  have hχ₁₂ : (Polynomial.evalRingHom (0 : (O ⧸ IsLocalRing.maximalIdeal O))).comp χ₁ = χ₂ := by
    obtain ⟨χ, -, huniq⟩ :=
      MvPolynomial.CrossingQuotient.existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq
        π a (0 : (O ⧸ IsLocalRing.maximalIdeal O)) 0 (by rw [zero_mul, hπa])
    have e1 := huniq ((Polynomial.evalRingHom (0 : (O ⧸ IsLocalRing.maximalIdeal O))).comp χ₁) ⟨by rw [RingHom.comp_assoc, hχ₁O]; ext x; simp, by
      rw [RingHom.comp_apply, hχ₁U, map_zero], by rw [RingHom.comp_apply, hχ₁V, Polynomial.coe_evalRingHom, Polynomial.eval_X]⟩
    have e2 := huniq _ ⟨hχ₂O, hχ₂U, hχ₂V⟩
    rw [e1, e2]
  have hp₁m : p₁ ≤ m.asIdeal := by
    intro b hb
    apply hker₂
    rw [RingHom.mem_ker, ← hχ₁₂, RingHom.comp_apply, show χ₁ b = 0 from hb, map_zero]
  have hp₁ne : p₁ ≠ m.asIdeal := by
    intro h
    have : CrossingQuotient.V a ∈ p₁ := h ▸ hmV
    rw [RingHom.mem_ker, hχ₁V] at this
    exact Polynomial.X_ne_zero this
  have hp₁lt : p₁ < m.asIdeal := lt_of_le_of_ne hp₁m hp₁ne

  obtain ⟨p₀, hp₀min, hp₀le⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (CrossingQuotient O a))) (J := p₁) bot_le
  haveI hp₀ : p₀.IsPrime := hp₀min.1.1
  have hϖp₁ : algebraMap O (CrossingQuotient O a) ϖ ∈ p₁ := by
    rw [RingHom.mem_ker, ← RingHom.comp_apply, hχ₁O, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hϖmem, map_zero]
  have hϖp₀ : algebraMap O (CrossingQuotient O a) ϖ ∉ p₀ := fun h =>
    Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp₀min) h
      (algebraMap_mem_nonZeroDivisors O ϖ hϖprime hϖu a)
  have hp₀lt : p₀ < p₁ := lt_of_le_of_ne hp₀le (fun h => hϖp₀ (h ▸ hϖp₁))

  let q₀ : PrimeSpectrum (CrossingQuotient O a) := ⟨p₀, hp₀⟩
  let q₁ : PrimeSpectrum (CrossingQuotient O a) := ⟨p₁, hp₁⟩
  let l : LTSeries (PrimeSpectrum (CrossingQuotient O a)) :=
    ((RelSeries.singleton _ m).cons q₁ (by show q₁ < m; exact hp₁lt)).cons q₀ (by show q₀ < q₁; exact hp₀lt)
  have hllen : l.length = 2 := rfl
  have hllast : l.last = m := rfl
  have hL := Order.length_le_height_last (p := l)
  rw [hllen, hllast] at hL

  rw [show ringKrullDim ((CrossingQuotient.crossingScheme a).presheaf.stalk m) = ringKrullDim (Localization.AtPrime m.asIdeal) from
      (ringKrullDim_eq_of_ringEquiv (AlgebraicGeometry.StructureSheaf.stalkIso (CommRingCat.of (CrossingQuotient O a)) m).toRingEquiv).symm,
    IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal (Localization.AtPrime m.asIdeal), PrimeSpectrum.height_eq_orderHeight]
  have h2 := (WithBot.coe_le_coe (α := ℕ∞)).mpr hL
  simpa using h2

end S_AlgebraicGeometry_two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal
end P2MW
export P2MW.S_AlgebraicGeometry_two_le_ringKrullDim_stalk_crossingScheme_of_mem_asIdeal (solution)
