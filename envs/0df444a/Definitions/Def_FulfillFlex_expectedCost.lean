-- Prove2me | Definitions.Def_FulfillFlex_expectedCost
-- name    : FulfillFlex_expectedCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:32.650196+00:00
-- url     : https://prove2.me/theorems/7db79e95-c8a0-4693-ac61-7cd655bebe11
-- title:
--   The expected cost $C^\theta(r,T)$ of a spillover limit policy
-- statement:
--   The cost of a sample path is the total fulfillment and lost sales cost,
--
--   $$
--   \sum_j c_{jj}\,(\text{local at }j)+\sum_{j'}\sum_{j\ne j'}c_{j'j}\,(\text{spillover }j'\to j)+\sum_j p_j\,(\text{lost at }j).
--   $$
--
--   The **expected cost** $C^\theta(r,T)$ of the spillover limit policy with limits $\theta$, from inventory $r$ over $T$ days, is its expectation under the law of the arrival sequence. The expected amounts of local fulfillment, spillover and lost sales are defined the same way; they are what the proof of Proposition 3 bounds term by term.
--
--   **Formalization Note** Expectations are sums in $[0,\infty]$, so an infinite expectation is the value $\infty$ and not a junk $0$. Under Assumption 1 every path cost is nonnegative, so `ENNReal.ofReal` loses nothing.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), §1.3, p.6; Proposition 3, p.16

import Mathlib
import Definitions.Def_FulfillFlex_horizonLaw
import Definitions.Def_FulfillFlex_run

open scoped ENNReal

namespace FulfillFlex

/-- The total fulfillment and lost sales cost of a final state, DeValve, Wei, Wu, Yuan, SSRN
3265838 (2021-01-18 version), §1.3, p.6: "the sum of total fulfillment and lost sales costs":
`∑_j c_jj · (local at j) + ∑_{j'} ∑_{j ≠ j'} c_{j'j} · (spillover j' → j) + ∑_j p_j · (lost at j)`. -/
noncomputable def pathCost {N : ℕ} (c : DC N → DC N → ℝ) (p : DC N → ℝ) (s : State N) : ℝ :=
  ∑ j, c j j * s.localFill j
    + ∑ j', ∑ j ∈ Finset.univ.erase j', c j' j * s.spill j' j
    + ∑ j, p j * s.lost j

/-- The expectation of a `[0, ∞]`-valued function under a `PMF`. -/
noncomputable def expectation {X : Type} (P : PMF X) (g : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, P x * g x

/-- The expected amount of local fulfillment at DC `j` under limits `θ`, inventory `r`, `T` days. -/
noncomputable def expectedLocal {N : ℕ} (ν : PMF (DC N → ℕ)) (α : DC N → unitInterval)
    (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (θ : DC N → DC N → ℝ) (r : DC N → ℝ) (T : ℕ)
    (j : DC N) : ℝ≥0∞ :=
  expectation (horizonLaw ν α T) fun w => ((run A c θ r w).localFill j : ℝ≥0∞)

/-- The expected amount of DC `j` demand filled from DC `j'`. -/
noncomputable def expectedSpill {N : ℕ} (ν : PMF (DC N → ℕ)) (α : DC N → unitInterval)
    (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (θ : DC N → DC N → ℝ) (r : DC N → ℝ) (T : ℕ)
    (j' j : DC N) : ℝ≥0∞ :=
  expectation (horizonLaw ν α T) fun w => ((run A c θ r w).spill j' j : ℝ≥0∞)

/-- The expected lost sales at DC `j`. -/
noncomputable def expectedLost {N : ℕ} (ν : PMF (DC N → ℕ)) (α : DC N → unitInterval)
    (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (θ : DC N → DC N → ℝ) (r : DC N → ℝ) (T : ℕ)
    (j : DC N) : ℝ≥0∞ :=
  expectation (horizonLaw ν α T) fun w => ((run A c θ r w).lost j : ℝ≥0∞)

/-- **The expected cost `C^θ(r, T)` of a spillover limit policy.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), `C^π(r, T)` of Proposition 3, p.16, for
the spillover limit policy `π` with limits `θ`, inventory `r` and horizon `T`.

**Formalization Note** The expectation is a sum in `ℝ≥0∞`, so an infinite expected cost is `⊤` and
not a junk `0`. Under Assumption 1 and on the policy's links, every path cost is nonnegative, so
`ENNReal.ofReal` loses nothing. -/
noncomputable def expectedCost {N : ℕ} (ν : PMF (DC N → ℕ)) (α : DC N → unitInterval)
    (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (p : DC N → ℝ) (θ : DC N → DC N → ℝ)
    (r : DC N → ℝ) (T : ℕ) : ℝ≥0∞ :=
  expectation (horizonLaw ν α T) fun w => ENNReal.ofReal (pathCost c p (run A c θ r w))

end FulfillFlex


