-- Prove2me | solution 1 for AlgHom.injective_of_trdeg_le_one_of_exists_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/b5cd7d8a-0373-5965-9427-2fce996b61ff

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental

set_option autoImplicit false

open Polynomial

namespace E87LD

variable {k D L E : Type*} [Field k] [CommRing D] [IsDomain D] [Algebra k D]
  [CommRing L] [Algebra k L] [CommRing E] [Algebra k E]

theorem exists_mem_ne_zero_map_eq_zero (Ψ : D →ₐ[k] E) (A : Subalgebra k D) (b : D) (hb : Ψ b = 0) (hb0 : b ≠ 0) :
    ∀ (n : ℕ) (P : Polynomial A), P.natDegree = n → P ≠ 0 → Polynomial.aeval b P = 0 →
      ∃ c : A, c ≠ 0 ∧ Ψ c = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hn hP0 hP
    have hsplit : Polynomial.aeval b P = b * Polynomial.aeval b P.divX + algebraMap A D (P.coeff 0) := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add P]
      rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
    by_cases h0 : P.coeff 0 = 0
    · have hdiv : P.divX ≠ 0 := by
        intro h
        apply hP0
        rw [← Polynomial.X_mul_divX_add P, h, h0]; simp
      have hev : Polynomial.aeval b P.divX = 0 := by
        rw [hP, h0, map_zero, add_zero] at hsplit
        exact (mul_eq_zero.mp hsplit.symm).resolve_left hb0
      have hdeg : P.divX.natDegree < n := by
        rw [← hn, Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        have : P.natDegree ≠ 0 := by
          intro hz
          apply hP0
          rw [Polynomial.eq_C_of_natDegree_eq_zero hz, h0, map_zero]
        omega
      exact ih _ hdeg P.divX rfl hdiv hev
    · refine ⟨P.coeff 0, h0, ?_⟩
      have := congrArg Ψ hsplit
      rw [hP, map_zero, map_add, map_mul, hb, zero_mul, zero_add] at this

      exact this.symm

theorem injective_of_trdeg_le_one_of_transcendental [IsDomain L]
    (Θ : D →ₐ[k] L) (hΘ : Function.Injective Θ) (hL : Algebra.trdeg k L ≤ 1)
    (Ψ : D →ₐ[k] E) (d : D) (hd : Transcendental k (Ψ d)) : Function.Injective Ψ := by
  classical
  rw [injective_iff_map_eq_zero]
  intro b hb
  by_contra hb0

  have hdT : Transcendental k d := fun halg => hd (halg.algHom Ψ)

  have hx : AlgebraicIndependent k (fun _ : Unit => d) :=
    algebraicIndependent_unique_type_iff.mpr hdT
  have hdep : ¬ AlgebraicIndependent k (fun o : Option Unit => o.elim b (fun _ : Unit => d)) := by
    intro hind
    have h2 := (hind.map' hΘ).lift_cardinalMk_le_trdeg
    have h1 : Cardinal.lift.{0} (Algebra.trdeg k L) ≤ 1 := by
      simpa using (Cardinal.lift_le.{0}).mpr hL
    have h3 : (2 : Cardinal) ≤ 1 := by
      have : Cardinal.lift.{u_3} (Cardinal.mk (Option Unit)) = 2 := by simp
      rw [this] at h2
      exact h2.trans h1
    norm_num at h3

  rw [hx.option_iff_transcendental] at hdep
  have halg : IsAlgebraic (Algebra.adjoin k (Set.range fun _ : Unit => d)) b := by
    unfold Transcendental at hdep; push Not at hdep; exact hdep
  obtain ⟨P, hP0, hP⟩ := halg
  obtain ⟨c, hc0, hc⟩ := exists_mem_ne_zero_map_eq_zero Ψ _ b hb hb0 _ P rfl hP0 hP

  have hrange : (Set.range fun _ : Unit => d) = {d} := by
    ext x; simp [eq_comm]
  have hcmem : (c : D) ∈ Algebra.adjoin k ({d} : Set D) := by rw [← hrange]; exact c.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hcmem
  obtain ⟨G, hG⟩ := hcmem
  have hG0 : G ≠ 0 := by
    intro h
    apply hc0
    apply Subtype.ext
    change (c : D) = 0
    rw [← hG, h, map_zero]
  apply hd
  refine ⟨G, hG0, ?_⟩
  rw [Polynomial.aeval_algHom_apply]
  change Ψ ((Polynomial.aeval d).toRingHom G) = 0
  rw [hG, hc]

end E87LD

theorem solution
    {k D L E : Type*} [Field k] [CommRing D] [IsDomain D] [Algebra k D]
    [CommRing L] [IsDomain L] [Algebra k L] [CommRing E] [Algebra k E]
    (Θ : D →ₐ[k] L) (hΘ : Function.Injective Θ) (hL : Algebra.trdeg k L ≤ 1)
    (Ψ : D →ₐ[k] E) (hΨ : ∃ d : D, Transcendental k (Ψ d)) :
    Function.Injective Ψ := by
  obtain ⟨d, hd⟩ := hΨ
  exact E87LD.injective_of_trdeg_le_one_of_transcendental Θ hΘ hL Ψ d hd

end S_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental
end P2MW
export P2MW.S_AlgHom_injective_of_trdeg_le_one_of_exists_transcendental (solution)
