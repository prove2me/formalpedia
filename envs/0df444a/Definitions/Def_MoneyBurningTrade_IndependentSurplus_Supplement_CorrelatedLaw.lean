-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_CorrelatedLaw
-- name    : MoneyBurningTrade_IndependentSurplus_Supplement_CorrelatedLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:36:38.891266+00:00
-- url     : https://prove2.me/theorems/31bd1f8a-a685-4c5b-accd-ca4bb380d8e1
-- title:
--   Section 4.3 — the correlated law F and its parameters
-- statement:
--   Let $q$ be the grid (22) of length $n$, $\Delta_i$ and $C$ as there, and $\eta>0$. For $2\le i\le n-2$ let
--
--   $$S_i=[q_{i-1},\,q_{i-1}+\eta],\qquad B_i=[q_{i+1}-\eta,\,q_{i+1}].$$
--
--   The joint law $F$ draws an index $i\in\{2,\dots,n-2\}$ with probability $C/\Delta_i$, then the seller's value uniformly on $S_i$ and, independently given $i$, the buyer's value uniformly on $B_i$:
--
--   $$F=\sum_{i=2}^{n-2}\frac{C}{\Delta_i}\;\mathrm{Unif}(S_i)\otimes\mathrm{Unif}(B_i).$$
--
--   The values are correlated because one index selects both intervals. The admissible parameters of §4.3 are: $n\ge4$; $\tau$ such that the grid with slack $\tau$ is a separation grid (Definition 4.4); and
--
--   $$0<\eta<\min\Bigl(\tau,\;\delta^2\min_{2\le i\le n-2}\Delta_i\Bigr).$$
--
--   **Formalization Note** The uniform law on an interval is Lebesgue measure conditioned on it. The minimum is written as the conjunction $\eta<\tau$ and $\eta<\delta^2\Delta_i$ for every $2\le i\le n-2$. That $F$ is a probability measure on $[0,1]^2$ is left to theorems.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), §4.3, "The distribution", printed p. 30–31 (PDF p. 31–32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Mathlib
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Supplement_CorrelatedGrid
import Definitions.Def_MoneyBurningTrade_IndependentSurplus_SeparationGrid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus.Supplement

/-- `S_i = [q_{i−1}, q_{i−1} + η]`, §4.3 p.30. -/
def sellerBox (n : ℕ) (η : ℝ) (i : ℕ) : Set ℝ :=
  Set.Icc ((correlatedGrid n).q (i - 1)) ((correlatedGrid n).q (i - 1) + η)

/-- `B_i = [q_{i+1} − η, q_{i+1}]`, §4.3 p.30. -/
def buyerBox (n : ℕ) (η : ℝ) (i : ℕ) : Set ℝ :=
  Set.Icc ((correlatedGrid n).q (i + 1) - η) ((correlatedGrid n).q (i + 1))

/-- The correlated joint law `F` of §4.3 p.30: draw `i ∈ {2,…,n−2}` with probability
`C/Δ_i`, then the seller's value uniformly on `S_i` and, independently given `i`,
the buyer's value uniformly on `B_i`. The uniform law on an interval is Lebesgue
measure conditioned on it (`ProbabilityTheory.cond`). Normalization and support
are left to theorems. Seller's value first. -/
noncomputable def correlatedLaw (n : ℕ) (η : ℝ) : Measure (ℝ × ℝ) :=
  ∑ i ∈ Finset.Icc 2 (n - 2), ENNReal.ofReal (corrC n / corrSpread n i) •
    ((ProbabilityTheory.cond volume (sellerBox n η i)).prod
      (ProbabilityTheory.cond volume (buyerBox n η i)))

/-- The parameter constraints of §4.3 pp.30–31: `n ≥ 4`; the grid (22) with slack `τ`
is a separation grid (Definition 4.4); and `0 < η < min(τ, δ²·min_{2≤i≤n−2} Δ_i)`,
written as `η < τ` and `η < δ²Δ_i` for every `2 ≤ i ≤ n − 2`. -/
def IsCorrelatedParam (n : ℕ) (τ η : ℝ) : Prop :=
  4 ≤ n ∧ IsSeparationGrid (correlatedGrid n) τ ∧ 0 < η ∧ η < τ ∧
  ∀ i : ℕ, 2 ≤ i → i ≤ n - 2 → η < corrDelta n ^ 2 * corrSpread n i

end MoneyBurningTrade.IndependentSurplus.Supplement


