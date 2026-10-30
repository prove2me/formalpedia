-- Prove2me | Definitions.Def_MultimodalPricing_Regret_Smooth
-- name    : MultimodalPricing_Regret_Smooth
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:01:48.084989+00:00
-- url     : https://prove2.me/theorems/4b67a0c9-bca4-4751-a5f7-a16e332cedcb
-- title:
--   Smooth demand on a closed price interval
-- statement:
--   For $k\ge1$, $C>0$ and $a\le b$, the predicate $\mathrm{Smooth}(k,C,a,b,f)$ means that $f$ takes values in $[0,1]$ on $[a,b]$ and has successive within-interval derivatives $g_0=f,g_1,\ldots,g_{k-1}$. For every $q<k$, $|g_q(p)|\le C$ on the interval, and $|g_{k-1}(p)-g_{k-1}(p')|\le C|p-p'|$. No derivative is required when $k=1$. Values outside the interval are immaterial; singleton intervals are allowed.
--
--   The expected revenue is $r(p)=pf(p)$, its best value is the supremum over $[a,b]$, and the local polynomial with coefficient vector $c$ is $\sum_{q<k}c_q(p-a)^q$. Smoothness gives continuity, so the revenue supremum on a nonempty closed interval is finite and attained. This is the paper's demand-specific smoothness class, not a globally differentiable extension.
-- source:
--   Wang, Chen, Simchi-Levi, Multi-Modal Dynamic Pricing, https://doi.org/10.1287/mnsc.2020.3819, supplied artifact (published metadata; SSRN 3489355 footer), Assumption 1, printed/PDF p. 10; Lemma 1, p. 12

import Mathlib

noncomputable section

namespace MultimodalPricing.Regret

/-- Assumption 1. Successive derivatives within the closed interval; order zero is f. -/
def Smooth (k : ℕ) (C a b : ℝ) (f : ℝ → ℝ) : Prop :=
  1 ≤ k ∧ 0 < C ∧ a ≤ b ∧
  (∀ p ∈ Set.Icc a b, f p ∈ Set.Icc (0 : ℝ) 1) ∧
  ∃ g : ℕ → ℝ → ℝ,
    (∀ p ∈ Set.Icc a b, g 0 p = f p) ∧
    (∀ q, q + 1 < k → ∀ p ∈ Set.Icc a b,
      HasDerivWithinAt (g q) (g (q + 1) p) (Set.Icc a b) p) ∧
    (∀ q, q < k → ∀ p ∈ Set.Icc a b, |g q p| ≤ C) ∧
    (∀ p ∈ Set.Icc a b, ∀ p' ∈ Set.Icc a b,
      |g (k - 1) p - g (k - 1) p'| ≤ C * |p - p'|)

/-- Expected revenue, p. 10. -/
def reward (f : ℝ → ℝ) (p : ℝ) : ℝ := p * f p

/-- The supremum is a maximum for Smooth functions on a nonempty closed interval. -/
def bestReward (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  sSup (reward f '' Set.Icc a b)

/-- The displayed polynomial allows a zero leading coefficient. -/
def localPolynomial (k : ℕ) (a : ℝ) (c : Fin k → ℝ) (p : ℝ) : ℝ :=
  ∑ q : Fin k, c q * (p - a) ^ q.val

end MultimodalPricing.Regret


