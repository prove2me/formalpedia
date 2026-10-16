-- Prove2me | Definitions.Def_NonstatRL_PerStep_Window
-- name    : NonstatRL_PerStep_Window
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:16:53.818371+00:00
-- url     : https://prove2.me/theorems/85e78d1f-675e-45b8-8fd0-c9a391cdb292
-- title:
--   Sliding-window estimators, confidence regions, and variation
-- statement:
--   Let $[l,h)$ be a window of observed state-action pairs. The visit count $N(s,a)$ counts appearances of $(s,a)$ and $N^+(s,a)=\max\{1,N(s,a)\}$. Reward and transition estimators divide their corresponding visit sums by $N^+$. Their comparison quantities average the true rewards and transition probabilities at the visited times with the same denominator. Thus the comparison quantities are zero at an unvisited pair.
--
--   The reward confidence set intersects $[0,1]$ with the radius $2\sqrt{2\log(SAT/\delta)/N^+}$ ball around the observed average. The transition confidence set intersects the probability simplex with the $\ell_1$ ball of radius $2\sqrt{2S\log(SAT/\delta)/N^+}+\eta$. Here $SA=\sum_s|\mathcal A_s|$. The local events bound the difference between comparison and observed averages by the corresponding radius; local variation sums the one-step drift from $l$ through the round preceding $t$.
--
--   These objects state the algorithm's uncertainty at an episode start and its subsequent drift. **Formalization Note** Windows are zero-based half-open intervals. The event for transitions retains the paper's $\ell_1$ error inequality; the literal simplex-membership wording fails when a pair has not been visited. The count denominator is at least one.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, pp. 12–14, (3)–(6), events and variation displays

import Mathlib
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm

namespace NonstatRL.PerStep

def count {S A : ℕ} (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A) : ℕ :=
  ((Finset.Ico lo hi).filter (fun q => st q = s ∧ ac q = a)).card

def countPlus {S A : ℕ} (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A) : ℝ :=
  (max 1 (count st ac lo hi s a) : ℕ)

noncomputable def rHat {S A : ℕ} (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (R : ℕ → ℝ) (lo hi : ℕ) (s : Fin S) (a : Fin A) : ℝ :=
  (∑ q ∈ Finset.Ico lo hi, if st q = s ∧ ac q = a then R q else 0) /
    countPlus st ac lo hi s a

noncomputable def rBar {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A) : ℝ :=
  (∑ q ∈ Finset.Ico lo hi, if st q = s ∧ ac q = a then (M q).r s a else 0) /
    countPlus st ac lo hi s a

noncomputable def pHat {S A : ℕ} (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A) (s' : Fin S) : ℝ :=
  ((Finset.Ico lo hi).filter
    (fun q => st q = s ∧ ac q = a ∧ st (q + 1) = s')).card /
    countPlus st ac lo hi s a

noncomputable def pBar {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (s : Fin S) (a : Fin A) (s' : Fin S) : ℝ :=
  (∑ q ∈ Finset.Ico lo hi,
    if st q = s ∧ ac q = a then ((M q).P s a s' : ℝ) else 0) /
    countPlus st ac lo hi s a

noncomputable def radR {S A : ℕ} (As : Fin S → Finset (Fin A))
    (T : ℕ) (δ n : ℝ) : ℝ :=
  2 * Real.sqrt (2 * Real.log ((∑ s : Fin S, ((As s).card : ℝ)) * T / δ) / n)

noncomputable def radP {S A : ℕ} (As : Fin S → Finset (Fin A))
    (T : ℕ) (δ n : ℝ) : ℝ :=
  2 * Real.sqrt (2 * S * Real.log ((∑ s : Fin S, ((As s).card : ℝ)) * T / δ) / n)

def Hr {S A : ℕ} (As : Fin S → Finset (Fin A))
    (T : ℕ) (δ : ℝ) (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (R : ℕ → ℝ) (lo hi : ℕ) (s : Fin S) (a : Fin A) : Set ℝ :=
  {v | 0 ≤ v ∧ v ≤ 1 ∧ |v - rHat st ac R lo hi s a| ≤
    radR As T δ (countPlus st ac lo hi s a)}

def Hp {S A : ℕ} (As : Fin S → Finset (Fin A))
    (T : ℕ) (δ : ℝ) (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) (η : ℝ) (s : Fin S) (a : Fin A) : Set (Fin S → ℝ) :=
  {v | (∀ s', 0 ≤ v s') ∧ (∑ s' : Fin S, v s') = 1 ∧
    (∑ s' : Fin S, |v s' - pHat st ac lo hi s a s'|) ≤
      radP As T δ (countPlus st ac lo hi s a) + η}

def EventR {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (T : ℕ) (δ : ℝ)
    (st : ℕ → Fin S) (ac : ℕ → Fin A) (R : ℕ → ℝ)
    (lo hi : ℕ) : Prop :=
  ∀ s : Fin S, ∀ a : Fin A, a ∈ As s →
    |rBar M st ac lo hi s a - rHat st ac R lo hi s a| ≤
      radR As T δ (countPlus st ac lo hi s a)

def EventP {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (T : ℕ) (δ : ℝ)
    (st : ℕ → Fin S) (ac : ℕ → Fin A)
    (lo hi : ℕ) : Prop :=
  ∀ s : Fin S, ∀ a : Fin A, a ∈ As s →
    (∑ s' : Fin S,
      |pBar M st ac lo hi s a s' - pHat st ac lo hi s a s'|) ≤
        radP As T δ (countPlus st ac lo hi s a)

noncomputable def varR {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (lo t : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ico lo t, NonstatRL.Oracle.rewardDrift M As q

noncomputable def varP {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (lo t : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ico lo t, NonstatRL.Oracle.transDrift M As q

end NonstatRL.PerStep


