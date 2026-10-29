-- Prove2me | Definitions.Def_RefDemandLearning_SlowMoving_Mechanism
-- name    : RefDemandLearning_SlowMoving_Mechanism
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:22:06.240991+00:00
-- url     : https://prove2.me/theorems/63038455-4482-4f0f-8686-440e6474174c
-- title:
--   Continuous reference-price mechanisms and changing exponential smoothing
-- statement:
--   Let $I=[\ell,u]$ be a real price interval with $0\le\ell<u$. A reference mechanism is a family of continuous maps $\rho_{n+1}:I^n\to I$, including the initial value on the singleton empty-history space. Prices are genuine real interval elements. The reference along a path $p$ is $\rho_{n+1}(p_1,\ldots,p_n)$.
--
--   The class $\mathcal R_{ES}$ consists of mechanisms for which some $\zeta\in[0,1)$ satisfies $r_{t+1}=\zeta r_t+(1-\zeta)p_t$ for every history. The class $\mathcal R_G$ allows a sequence of change times $\tau_1=1$, strictly increasing while finite and permanently infinite after its first infinite term, and arbitrary coefficients $\zeta_k\in[0,1)$. For one finite $c>0$, every positive integer interval satisfies
--   $$\#\{\tau_k:s<\tau_k\le t\}\le c\sqrt{t-s}.$$
--   The smoothing recurrence is imposed only when $\tau_k\le t$ and $t+1<\tau_{k+1}$. At a reset the reference may depend continuously on the entire previous history. Infinitely many changes and coefficients approaching one are permitted.
--
--   For a history $h$ of length $s$ followed by a held price $p$, the tracking error is
--   $$\sum_{k=s+1}^{t}|\rho_k(h,p,\ldots,p)-p|.$$
--
--   **Formalization Note.** Mechanisms are a standalone object, independent of the demand model. Continuous maps have interval-valued outputs. Periods and regime indices are zero-based internally, while change-time values and the endpoints $s,t$ keep the source numbering. Infinity is `WithTop`; counting distinct finite change times equals the source double indicator sum. The clamp extends evaluation to arbitrary real inputs and equals the identity on the interval. No demand, regret or estimation bound is part of this definition.
-- source:
--   den Boer and Keskin, Dynamic Pricing with Demand Learning and Reference Effects, DOI https://doi.org/10.1287/mnsc.2021.4234, supplied April 19, 2021 artifact, Sections 2 and 3, printed/PDF pp. 8–10, 13, 16–17; (2.4), (3.1)–(3.6)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace RefDemandLearning.SlowMoving

/-- A nondegenerate compact interval of nonnegative real prices. -/
structure PriceInterval where
  lo : ℝ
  hi : ℝ
  nonneg : 0 ≤ lo
  lt : lo < hi

abbrev Price (I : PriceInterval) := Set.Icc I.lo I.hi

/-- Extension from arbitrary real inputs; the identity on the price interval. -/
def clipPrice (I : PriceInterval) (x : ℝ) : Price I :=
  ⟨max I.lo (min x I.hi), le_max_left _ _,
    max_le (le_of_lt I.lt) (min_le_right _ _)⟩

/-- `ref n` is the source's rho_(n+1), taking exactly n past prices. -/
structure Mechanism (I : PriceInterval) where
  ref : (n : ℕ) → C((Fin n → Price I), Price I)

/-- Reference price along an infinite price path, with zero-based periods. -/
def reference {I : PriceInterval} (ρ : Mechanism I) (p : ℕ → Price I) (n : ℕ) : ℝ :=
  ρ.ref n (fun j => p j.val)

/-- The source's R_ES, including coefficient zero and excluding one. -/
def IsES {I : PriceInterval} (ρ : Mechanism I) : Prop :=
  ∃ ζ : ℝ, 0 ≤ ζ ∧ ζ < 1 ∧ ∀ (p : ℕ → Price I) (n : ℕ),
    reference ρ p (n + 1) = ζ * reference ρ p n + (1 - ζ) * (p n : ℝ)

/-- Change times retain the source's one-based time values; regime indices are zero-based. -/
def IsChangeSchedule (τ : ℕ → WithTop ℕ) : Prop := by
  classical
  exact τ 0 = 1 ∧
  (∀ k, τ (k + 1) < ⊤ → τ k < τ (k + 1)) ∧
  (∀ k, τ k = ⊤ → τ (k + 1) = ⊤) ∧
  ∃ c : ℝ, 0 < c ∧ ∀ s t : ℕ, 1 ≤ s → s < t →
    (∑ l ∈ Finset.Ioc s t, if ∃ k, τ k = (l : WithTop ℕ) then (1 : ℝ) else 0)
      ≤ c * Real.sqrt (t - s : ℕ)

/-- R_G: continuous resets are unrestricted, and no uniform contraction is required. -/
def IsGeneral {I : PriceInterval} (ρ : Mechanism I) : Prop :=
  ∃ (τ : ℕ → WithTop ℕ) (ζ : ℕ → ℝ), IsChangeSchedule τ ∧
    (∀ k, 0 ≤ ζ k ∧ ζ k < 1) ∧
    ∀ (p : ℕ → Price I) (k n : ℕ),
      τ k ≤ ((n + 1 : ℕ) : WithTop ℕ) →
      ((n + 2 : ℕ) : WithTop ℕ) < τ (k + 1) →
      reference ρ p (n + 1) = ζ k * reference ρ p n + (1 - ζ k) * (p n : ℝ)

/-- Append a held price after an arbitrary history of length s. -/
def heldPath {I : PriceInterval} (s : ℕ) (h : Fin s → Price I) (p : Price I)
    (n : ℕ) : Price I :=
  if hn : n < s then h ⟨n, hn⟩ else p

/-- Sum from source time s+1 to t, including the first reference after the history. -/
def trackingError {I : PriceInterval} (ρ : Mechanism I) (s t : ℕ)
    (h : Fin s → Price I) (p : Price I) : ℝ :=
  ∑ n ∈ Finset.Ico s t, |reference ρ (heldPath s h p) n - (p : ℝ)|

end RefDemandLearning.SlowMoving


