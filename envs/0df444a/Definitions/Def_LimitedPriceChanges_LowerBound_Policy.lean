-- Prove2me | Definitions.Def_LimitedPriceChanges_LowerBound_Policy
-- name    : LimitedPriceChanges_LowerBound_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:19.514046+00:00
-- url     : https://prove2.me/theorems/c6ab16f0-00f9-4883-bed7-90adeb594d3a
-- title:
--   Randomized policies with a sure price-change budget
-- statement:
--   A policy draws a random seed once, then at period $t$ chooses a price in $[1,6]$ using the seed and the demand observations from earlier periods. Inventory is replenished to one before every sale, so sales equal Bernoulli demand. Along every seed and demand path, at most $m$ consecutive-period price changes occur:
--   $$\sum_{t=1}^{T-1}\mathbf 1\{p_t\ne p_{t+1}\}\le m.$$
--   For parameter $z$, a path receives the product of its conditional Bernoulli probabilities. Expected regret is the finite sum over demand paths of their weight times $\sum_t(G^*(z)-r_z(p_t))$, integrated over the seed probability measure.
--
--   This represents the randomized, adaptive policy class used by Theorem 2. **Formalization Note** Lean periods are zero-based: index $t$ denotes paper period $t+1$. A single seed can encode all successive random draws. The expectation uses a nonnegative lintegral, and the change budget holds surely for every seed and path.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), pp. 5–6, admissibility and (2); p. 35, (49)

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Model

namespace LimitedPriceChanges.LowerBound

/-- The realized price at zero-based period `t`, given a complete demand path. -/
noncomputable def priceAlong {S : Type} {T : ℕ}
    (price : (t : ℕ) → S → (Fin t → Bool) → ℝ)
    (s : S) (d : Fin T → Bool) (t : Fin T) : ℝ :=
  price t.val s (fun i => d ⟨i.val, lt_trans i.isLt t.isLt⟩)

/-- Number of adjacent price changes along a complete path. -/
noncomputable def changeCount {S : Type} {T : ℕ}
    (price : (t : ℕ) → S → (Fin t → Bool) → ℝ)
    (s : S) (d : Fin T → Bool) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : Fin T =>
    if ht : t.val + 1 < T then
      priceAlong price s d t ≠ priceAlong price s d ⟨t.val + 1, ht⟩
    else False)).card

/-- A randomized, demand-adapted price policy with a sure change budget. -/
structure Policy (S : Type) [MeasurableSpace S] (T m : ℕ) where
  price : (t : ℕ) → S → (Fin t → Bool) → ℝ
  feasible : ∀ t s h, price t s h ∈ Set.Icc (1 : ℝ) 6
  measurable : ∀ t h, Measurable (fun s => price t s h)
  changes : ∀ s (d : Fin T → Bool), changeCount price s d ≤ m

/-- Probability of a finite Bernoulli demand path conditional on the policy seed. -/
noncomputable def pathWeight {S : Type} [MeasurableSpace S] {T m : ℕ}
    (π : Policy S T m) (z : ℝ) (s : S) (d : Fin T → Bool) : ENNReal :=
  ∏ t : Fin T,
    if d t then ENNReal.ofReal (nu (priceAlong π.price s d t) z)
    else ENNReal.ofReal (1 - nu (priceAlong π.price s d t) z)

/-- Expected total regret, as a finite path sum and a seed lintegral. -/
noncomputable def regret {S : Type} [MeasurableSpace S] {T m : ℕ}
    (μ : MeasureTheory.Measure S) (π : Policy S T m) (z : ℝ) : ENNReal :=
  ∫⁻ s, ∑ d : Fin T → Bool,
    pathWeight π z s d *
      ∑ t : Fin T, ENNReal.ofReal (Gstar z - rev (priceAlong π.price s d t) z) ∂μ

end LimitedPriceChanges.LowerBound


