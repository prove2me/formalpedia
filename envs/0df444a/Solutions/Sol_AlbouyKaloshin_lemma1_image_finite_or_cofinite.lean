-- Prove2me | solution 1 for AlbouyKaloshin.lemma1_image_finite_or_cofinite
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:30:11.461908+00:00
-- url     : https://prove2.me/submissions/e22ae323-326b-4f93-8d2b-aa951dba842e

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

open Topology

namespace AKL1

/-- closed point of `Spec ℂ[X]` at `c` -/
noncomputable def pt (c : ℂ) : PrimeSpectrum (Polynomial ℂ) :=
  ⟨RingHom.ker (Polynomial.evalRingHom c), RingHom.ker_isPrime _⟩

lemma mem_pt (c : ℂ) (g : Polynomial ℂ) : g ∈ (pt c).asIdeal ↔ g.eval c = 0 := by
  simp [pt, RingHom.mem_ker]

/-- the Boolean algebra of sets whose trace on closed points is finite or cofinite -/
def FC (E : Set (PrimeSpectrum (Polynomial ℂ))) : Prop :=
  (pt ⁻¹' E).Finite ∨ (pt ⁻¹' E)ᶜ.Finite

def B : BooleanSubalgebra (Set (PrimeSpectrum (Polynomial ℂ))) where
  carrier := {E | FC E}
  supClosed' := by
    intro E hE F hF
    simp only [Set.mem_setOf_eq, FC, Set.sup_eq_union, Set.preimage_union, Set.compl_union] at *
    rcases hE with h | h <;> rcases hF with h' | h'
    · exact Or.inl (h.union h')
    · exact Or.inr (h'.subset Set.inter_subset_right)
    · exact Or.inr (h.subset Set.inter_subset_left)
    · exact Or.inr (h.subset Set.inter_subset_left)
  infClosed' := by
    intro E hE F hF
    simp only [Set.mem_setOf_eq, FC, Set.inf_eq_inter, Set.preimage_inter, Set.compl_inter] at *
    rcases hE with h | h <;> rcases hF with h' | h'
    · exact Or.inl (h.subset Set.inter_subset_left)
    · exact Or.inl (h.subset Set.inter_subset_left)
    · exact Or.inl (h'.subset Set.inter_subset_right)
    · exact Or.inr (h.union h')
  bot_mem' := by simp [FC]
  compl_mem' := by
    intro E hE
    simp only [Set.mem_setOf_eq, FC, Set.preimage_compl, compl_compl] at *
    exact hE.symm

lemma open_mem (U : Set (PrimeSpectrum (Polynomial ℂ))) (hU : IsOpen U) : U ∈ B := by
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isOpen_iff U).1 hU
  show FC U
  unfold FC
  have key : (pt ⁻¹' U)ᶜ = {c | ∀ g ∈ s, g.eval c = 0} := by
    ext c
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq]
    rw [← Set.mem_compl_iff, hs, PrimeSpectrum.mem_zeroLocus]
    constructor
    · intro h g hg; exact (mem_pt c g).1 (h hg)
    · intro h g hg; exact (mem_pt c g).2 (h g hg)
  by_cases h0 : ∃ g ∈ s, g ≠ 0
  · obtain ⟨g, hg, hg0⟩ := h0
    right
    rw [key]
    refine (g.rootSet_finite ℂ).subset ?_
    intro c hc
    simp only [Set.mem_setOf_eq] at hc
    rw [Polynomial.mem_rootSet]
    exact ⟨hg0, by simpa using hc g hg⟩
  · push_neg at h0
    left
    have : pt ⁻¹' U = ∅ := by
      rw [← compl_compl (pt ⁻¹' U), key]
      ext c
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_not]
      intro g hg; rw [h0 g hg]; simp
    rw [this]; exact Set.finite_empty

lemma constructible_FC (E : Set (PrimeSpectrum (Polynomial ℂ))) (hE : IsConstructible E) :
    FC E := by
  have : BooleanSubalgebra.closure {U | IsOpen U ∧ IsRetrocompact U} ≤ B :=
    BooleanSubalgebra.closure_le.2 (fun U hU => open_mem U hU.1)
  exact this hE

end AKL1

open AKL1 in
theorem solution (N : ℕ) (S : Set (MvPolynomial (Fin N) ℂ))
    (f : MvPolynomial (Fin N) ℂ) :
    ((fun z => MvPolynomial.eval z f) '' {z : Fin N → ℂ | ∀ p ∈ S, MvPolynomial.eval z p = 0}).Finite ∨
    ((fun z => MvPolynomial.eval z f) '' {z : Fin N → ℂ | ∀ p ∈ S, MvPolynomial.eval z p = 0})ᶜ.Finite := by
  set I : Ideal (MvPolynomial (Fin N) ℂ) := Ideal.span S
  let A := MvPolynomial (Fin N) ℂ ⧸ I
  let φ : Polynomial ℂ →+* A :=
    (Ideal.Quotient.mk I).comp (Polynomial.aeval f).toRingHom
  have hφ : φ.FinitePresentation := by
    have h1 : (φ.comp (algebraMap ℂ (Polynomial ℂ))).FiniteType := by
      have : φ.comp (algebraMap ℂ (Polynomial ℂ)) = algebraMap ℂ A := by
        ext x; simp only [φ, A, RingHom.comp_apply]; rw [← Ideal.Quotient.mk_algebraMap]; simp
      rw [this]
      exact RingHom.finiteType_algebraMap.2 inferInstance
    exact RingHom.FinitePresentation.of_finiteType.1 (RingHom.FiniteType.of_comp_finiteType h1)
  have hcon := constructible_FC _ (PrimeSpectrum.isConstructible_range_comap hφ)
  have heq : (fun z => MvPolynomial.eval z f) '' {z : Fin N → ℂ | ∀ p ∈ S, MvPolynomial.eval z p = 0}
      = pt ⁻¹' Set.range (PrimeSpectrum.comap φ) := by
    ext c
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨z, hz, rfl⟩
      let ψ : A →+* ℂ := Ideal.Quotient.lift I (MvPolynomial.eval z) (by
        intro a ha
        refine Submodule.span_induction (fun p hp => hz p hp) (by simp)
          (fun x y _ _ hx hy => by simp [hx, hy]) (fun r x _ hx => by simp [hx]) ha)
      refine ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime _⟩, ?_⟩
      ext g
      simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.mem_ker, mem_pt]
      have key : ∀ g : Polynomial ℂ, MvPolynomial.eval z (Polynomial.aeval f g)
          = g.eval (MvPolynomial.eval z f) := by
        intro g
        induction g using Polynomial.induction_on with
        | C a => simp
        | add p q hp hq => simp [hp, hq]
        | monomial n a h => simp [pow_succ]
      simp [φ, ψ, A, key]
    · rintro ⟨Q, hQ⟩
      obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q.asIdeal Q.isPrime.ne_top
      have hM' : (M.comap (Ideal.Quotient.mk I)).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      obtain ⟨z, hz⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM'
      have mem : ∀ g, Ideal.Quotient.mk I g ∈ M → MvPolynomial.eval z g = 0 := by
        intro g hg
        have : g ∈ M.comap (Ideal.Quotient.mk I) := hg
        rw [hz] at this
        simpa [MvPolynomial.mem_vanishingIdeal_singleton_iff] using this
      refine ⟨z, fun p hp => mem p ?_, ?_⟩
      · rw [(Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.subset_span hp)]; exact M.zero_mem
      · have hX : (Polynomial.X - Polynomial.C c) ∈ (PrimeSpectrum.comap φ Q).asIdeal := by
          rw [hQ, mem_pt]; simp
        have h2 : φ (Polynomial.X - Polynomial.C c) ∈ M := hQM hX
        have h3 : Ideal.Quotient.mk I (f - MvPolynomial.C c) ∈ M := by
          simpa [φ] using h2
        have := mem _ h3
        simp at this
        linear_combination this
  rw [heq]; exact hcon
