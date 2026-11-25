-- Prove2me | solution 1 for Arxiv1810_02867.em_constitutive_reorganisation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T21:54:52.047837+00:00
-- url     : https://prove2.me/submissions/830d3f29-cda2-44a8-ae95-2e594ba07822

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

set_option autoImplicit false

open MeasureTheory Matrix

namespace S71EM
open Arxiv1810_02867

lemma dlin (a b : Fin 3 → ℝ) (E H : ℝ → Fin 3 → ℝ)
    (hE : ∀ l, Differentiable ℝ (fun t => E t l)) (hH : ∀ k, Differentiable ℝ (fun t => H t k))
    (t : ℝ) :
    deriv (fun s => ∑ l, a l * E s l + ∑ k, b k * H s k) t =
      ∑ l, a l * deriv (fun s => E s l) t + ∑ k, b k * deriv (fun s => H s k) t := by
  have h1 : HasDerivAt (fun s => ∑ l, a l * E s l) (∑ l, a l * deriv (fun s => E s l) t) t :=
    HasDerivAt.fun_sum fun l _ => ((hE l t).hasDerivAt.const_mul (a l))
  have h2 : HasDerivAt (fun s => ∑ k, b k * H s k) (∑ k, b k * deriv (fun s => H s k) t) t :=
    HasDerivAt.fun_sum fun k _ => ((hH k t).hasDerivAt.const_mul (b k))
  exact (h1.add h2).deriv

end S71EM

open Arxiv1810_02867 S71EM in
theorem solution (eps eta theta nu mu : Space → Fin 3 → Fin 3 → ℝ)
    (E H D B Je Jm : Space → ℝ → Fin 3 → ℝ)
    (hmunu : ∀ x j l, ∑ k, mu x j k * nu x k l = kd j l)
    (heps : ∀ x i j, eps x i j = eps x j i) (hnu : ∀ x k l, nu x k l = nu x l k)
    (hmu : ∀ x j k, mu x j k = mu x k j) (heta : ∀ x i j, eta x i j = -theta x j i)
    (hcon : EMConstitutive eps eta theta nu E B D H) (hmax : MaxwellEqs D B E H Je Jm)
    (hE : ∀ x l, Differentiable ℝ (fun t => E x t l))
    (hH : ∀ x k, Differentiable ℝ (fun t => H x t k)) :
    (∀ x t j, B x t j = ∑ l, zetaEM (mu x) (theta x) j l * E x t l + ∑ k, mu x j k * H x t k) ∧
    (∀ x t i, D x t i = ∑ l, epsO (eps x) (eta x) (mu x) (theta x) i l * E x t l +
        ∑ k, xiEM (eta x) (mu x) i k * H x t k) ∧
    (∀ x i l, epsO (eps x) (eta x) (mu x) (theta x) i l =
        epsO (eps x) (eta x) (mu x) (theta x) l i) ∧
    (∀ x l j, xiEM (eta x) (mu x) l j = zetaEM (mu x) (theta x) j l) ∧
    MaxwellEO (fun x => epsO (eps x) (eta x) (mu x) (theta x)) (fun x => xiEM (eta x) (mu x)) mu
      E H Je Jm := by
  have hB : ∀ x t j, B x t j = ∑ l, zetaEM (mu x) (theta x) j l * E x t l +
      ∑ k, mu x j k * H x t k := by
    intro x t j
    have hk0 := (hcon x t).2 0
    have hk1 := (hcon x t).2 1
    have hk2 := (hcon x t).2 2
    have m0 := hmunu x j 0
    have m1 := hmunu x j 1
    have m2 := hmunu x j 2
    have hBj : B x t j = ∑ l, kd j l * B x t l := by
      fin_cases j <;> simp [kd, Fin.sum_univ_three]
    simp only [zetaEM, Fin.sum_univ_three] at hk0 hk1 hk2 m0 m1 m2 hBj ⊢
    linear_combination hBj - mu x j 0 * hk0 - mu x j 1 * hk1 - mu x j 2 * hk2 -
      B x t 0 * m0 - B x t 1 * m1 - B x t 2 * m2
  have hD : ∀ x t i, D x t i = ∑ l, epsO (eps x) (eta x) (mu x) (theta x) i l * E x t l +
      ∑ k, xiEM (eta x) (mu x) i k * H x t k := by
    intro x t i
    have hd := (hcon x t).1 i
    have b0 := hB x t 0
    have b1 := hB x t 1
    have b2 := hB x t 2
    simp only [zetaEM, epsO, xiEM, Fin.sum_univ_three] at hd b0 b1 b2 ⊢
    linear_combination hd + eta x i 0 * b0 + eta x i 1 * b1 + eta x i 2 * b2
  have hsym : ∀ x i l, epsO (eps x) (eta x) (mu x) (theta x) i l =
      epsO (eps x) (eta x) (mu x) (theta x) l i := by
    intro x i l
    simp only [epsO, heta, Fin.sum_univ_three]
    rw [heps x i l, hmu x 1 0, hmu x 2 0, hmu x 2 1]
    ring
  have hxz : ∀ x l j, xiEM (eta x) (mu x) l j = zetaEM (mu x) (theta x) j l := by
    intro x l j
    simp only [xiEM, zetaEM, heta, Fin.sum_univ_three]
    rw [hmu x 0 j, hmu x 1 j, hmu x 2 j]
    ring
  refine ⟨hB, hD, hsym, hxz, ?_⟩
  intro x t
  obtain ⟨m1, m2⟩ := hmax x t
  constructor
  · intro i
    have e : pdt (cmp D i) x t = ∑ l, epsO (eps x) (eta x) (mu x) (theta x) i l *
        pdt (cmp E l) x t + ∑ k, xiEM (eta x) (mu x) i k * pdt (cmp H k) x t := by
      unfold pdt Arxiv1810_02867.cmp
      rw [show (fun s => D x s i) = fun s => ∑ l, epsO (eps x) (eta x) (mu x) (theta x) i l *
        E x s l + ∑ k, xiEM (eta x) (mu x) i k * H x s k from funext fun s => hD x s i]
      exact dlin _ _ (E x) (H x) (hE x) (hH x) t
    have := m1 i
    rw [e] at this
    exact this
  · intro j
    have e : pdt (cmp B j) x t = ∑ l, xiEM (eta x) (mu x) l j *
        pdt (cmp E l) x t + ∑ k, mu x j k * pdt (cmp H k) x t := by
      simp_rw [hxz]
      unfold pdt Arxiv1810_02867.cmp
      rw [show (fun s => B x s j) = fun s => ∑ l, zetaEM (mu x) (theta x) j l *
        E x s l + ∑ k, mu x j k * H x s k from funext fun s => hB x s j]
      exact dlin _ _ (E x) (H x) (hE x) (hH x) t
    have := m2 j
    rw [e] at this
    exact this
