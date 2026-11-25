-- Prove2me | solution 1 for Arxiv1810_02867.willis_constitutive_reorganisation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T22:00:44.025245+00:00
-- url     : https://prove2.me/submissions/21ee85e2-e310-4e2c-99b4-636f1c178276

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

set_option autoImplicit false

open MeasureTheory Matrix

namespace S71WI
open Arxiv1810_02867

lemma swap4 (G : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    ∑ k, ∑ l, ∑ m, ∑ n, G k l m n = ∑ m, ∑ n, ∑ k, ∑ l, G k l m n := by
  calc ∑ k, ∑ l, ∑ m, ∑ n, G k l m n = ∑ k, ∑ m, ∑ l, ∑ n, G k l m n :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ m, ∑ k, ∑ l, ∑ n, G k l m n := Finset.sum_comm
    _ = ∑ m, ∑ k, ∑ n, ∑ l, G k l m n :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ∑ k, ∑ l, G k l m n := Finset.sum_congr rfl fun m _ => Finset.sum_comm

lemma kdsum (k l : Fin 3) (f : Fin 3 → Fin 3 → ℝ) :
    ∑ p, ∑ q, (1 / 2) * (kd k p * kd l q + kd k q * kd l p) * f p q = (1 / 2) * (f k l + f l k) := by
  fin_cases k <;> fin_cases l <;> simp [kd, Fin.sum_univ_three] <;> ring

lemma dlin (a : Fin 3 → ℝ) (b : Fin 3 → Fin 3 → ℝ) (v : ℝ → Fin 3 → ℝ) (T : ℝ → Fin 3 → Fin 3 → ℝ)
    (hv : ∀ j, Differentiable ℝ (fun t => v t j))
    (hT : ∀ m n, Differentiable ℝ (fun t => T t m n)) (t : ℝ) :
    deriv (fun s => ∑ p, a p * v s p + ∑ m, ∑ n, b m n * T s m n) t =
      ∑ p, a p * deriv (fun s => v s p) t + ∑ m, ∑ n, b m n * deriv (fun s => T s m n) t := by
  have h1 : HasDerivAt (fun s => ∑ p, a p * v s p) (∑ p, a p * deriv (fun s => v s p) t) t :=
    HasDerivAt.fun_sum fun j _ => ((hv j t).hasDerivAt.const_mul (a j))
  have h2 : HasDerivAt (fun s => ∑ m, ∑ n, b m n * T s m n)
      (∑ m, ∑ n, b m n * deriv (fun s => T s m n) t) t :=
    HasDerivAt.fun_sum fun m _ => HasDerivAt.fun_sum fun n _ =>
      ((hT m n t).hasDerivAt.const_mul (b m n))
  exact (h1.add h2).deriv

end S71WI

open Arxiv1810_02867 S71WI in
theorem solution (rho : Space → Fin 3 → Fin 3 → ℝ)
    (S2 S1 : Space → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (c s : Space → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (mom v F : Space → ℝ → Fin 3 → ℝ) (tau e h : Space → ℝ → Fin 3 → Fin 3 → ℝ)
    (htau : ∀ x t i j, tau x t i j = tau x t j i) (he : ∀ x t k l, e x t k l = e x t l k)
    (hh : ∀ x t k l, h x t k l = h x t l k)
    (hsc : ∀ x k l p q, ∑ m, ∑ n, s x k l m n * c x m n p q =
      (1 / 2) * (kd k p * kd l q + kd k q * kd l p))
    (hrho : ∀ x i k, rho x i k = rho x k i)
    (hc : ∀ x m n p q, c x m n p q = c x n m p q ∧ c x m n p q = c x m n q p ∧
      c x m n p q = c x p q m n)
    (hs : ∀ x k l m n, s x k l m n = s x l k m n ∧ s x k l m n = s x k l n m ∧
      s x k l m n = s x m n k l)
    (hS1 : ∀ x m n p, S1 x m n p = S1 x n m p) (hS2 : ∀ x i k l, S2 x i k l = S2 x i l k)
    (hS21 : ∀ x i k l, S2 x i k l = -S1 x k l i)
    (hbase : ElastoBase mom tau e v F h) (hcon : WillisConst rho S2 S1 c mom v e tau)
    (hv : ∀ x p, Differentiable ℝ (fun t => v x t p))
    (htd : ∀ x m n, Differentiable ℝ (fun t => tau x t m n)) :
    (∀ x t k l, e x t k l = -∑ p, zetaW (s x) (S1 x) k l p * v x t p +
        ∑ m, ∑ n, s x k l m n * tau x t m n) ∧
    (∀ x t i, mom x t i = ∑ p, rhoOW (rho x) (S2 x) (s x) (S1 x) i p * v x t p -
        ∑ m, ∑ n, xiW (S2 x) (s x) i m n * tau x t m n) ∧
    (∀ x i p, rhoOW (rho x) (S2 x) (s x) (S1 x) i p = rhoOW (rho x) (S2 x) (s x) (S1 x) p i) ∧
    (∀ x k l p, zetaW (s x) (S1 x) k l p = zetaW (s x) (S1 x) l k p) ∧
    (∀ x i m n, xiW (S2 x) (s x) i m n = xiW (S2 x) (s x) i n m) ∧
    (∀ x p k l, xiW (S2 x) (s x) p k l = zetaW (s x) (S1 x) k l p) ∧
    ElastoEqs (fun x => rhoOW (rho x) (S2 x) (s x) (S1 x)) (fun x => xiW (S2 x) (s x)) s v tau
      F h := by
  have hE : ∀ x t k l, e x t k l = -∑ p, zetaW (s x) (S1 x) k l p * v x t p +
      ∑ m, ∑ n, s x k l m n * tau x t m n := by
    intro x t k l
    have hT := (hcon x t).2
    have key : ∑ m, ∑ n, s x k l m n * tau x t m n =
        ∑ p, zetaW (s x) (S1 x) k l p * v x t p +
          ∑ p, ∑ q, (∑ m, ∑ n, s x k l m n * c x m n p q) * e x t p q := by
      simp only [hT, zetaW, Fin.sum_univ_three]; ring
    rw [key]
    simp only [hsc, kdsum]
    rw [← he x t k l]; ring
  have hM : ∀ x t i, mom x t i = ∑ p, rhoOW (rho x) (S2 x) (s x) (S1 x) i p * v x t p -
      ∑ m, ∑ n, xiW (S2 x) (s x) i m n * tau x t m n := by
    intro x t i
    rw [(hcon x t).1 i]
    simp only [hE x t, rhoOW, xiW, zetaW, Fin.sum_univ_three]
    ring
  have hsym : ∀ x i p, rhoOW (rho x) (S2 x) (s x) (S1 x) i p =
      rhoOW (rho x) (S2 x) (s x) (S1 x) p i := by
    intro x i p
    unfold rhoOW
    rw [hrho x i p, swap4]
    congr 1
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hS21 x i k l, hS21 x p m n, (hs x k l m n).2.2]; ring
  have hz : ∀ x k l p, zetaW (s x) (S1 x) k l p = zetaW (s x) (S1 x) l k p := by
    intro x k l p
    unfold zetaW
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [(hs x k l m n).1]
  have hxs : ∀ x i m n, xiW (S2 x) (s x) i m n = xiW (S2 x) (s x) i n m := by
    intro x i m n
    unfold xiW
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [(hs x a b m n).2.1]
  have hxz : ∀ x p k l, xiW (S2 x) (s x) p k l = zetaW (s x) (S1 x) k l p := by
    intro x p k l
    simp only [xiW, zetaW, hS21, neg_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [(hs x a b k l).2.2]; ring
  refine ⟨hE, hM, hsym, hz, hxs, hxz, ?_⟩
  intro x t
  obtain ⟨b1, b2⟩ := hbase x t
  constructor
  · intro i
    have hd : pdt (cmp mom i) x t = ∑ p, rhoOW (rho x) (S2 x) (s x) (S1 x) i p * pdt (cmp v p) x t +
        ∑ m, ∑ n, (-xiW (S2 x) (s x) i m n) * pdt (fun y s' => tau y s' m n) x t := by
      unfold pdt Arxiv1810_02867.cmp
      rw [show (fun s' => mom x s' i) = fun s' => ∑ p, rhoOW (rho x) (S2 x) (s x) (S1 x) i p *
        v x s' p + ∑ m, ∑ n, (-xiW (S2 x) (s x) i m n) * tau x s' m n from funext fun s' => by
          rw [hM x s' i]; simp only [neg_mul, Finset.sum_neg_distrib]; ring]
      exact dlin _ _ (v x) (tau x) (hv x) (htd x) t
    have := b1 i
    rw [hd] at this
    simp only [neg_mul, Finset.sum_neg_distrib] at this
    linarith
  · intro k l
    have hd : pdt (fun y s' => e y s' k l) x t =
        ∑ p, (-xiW (S2 x) (s x) p k l) * pdt (cmp v p) x t +
        ∑ m, ∑ n, s x k l m n * pdt (fun y s' => tau y s' m n) x t := by
      unfold pdt Arxiv1810_02867.cmp
      rw [show (fun s' => e x s' k l) = fun s' => ∑ p, (-xiW (S2 x) (s x) p k l) *
        v x s' p + ∑ m, ∑ n, s x k l m n * tau x s' m n from funext fun s' => by
          rw [hE x s' k l]; simp only [hxz, neg_mul, Finset.sum_neg_distrib]]
      exact dlin _ _ (v x) (tau x) (hv x) (htd x) t
    have := b2 k l
    rw [hd] at this
    simp only [neg_mul, Finset.sum_neg_distrib] at this
    linarith
