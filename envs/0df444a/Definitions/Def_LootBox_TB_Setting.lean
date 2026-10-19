-- Prove2me | Definitions.Def_LootBox_TB_Setting
-- name    : LootBox_TB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:15.814025+00:00
-- url     : https://prove2.me/theorems/a8336419-7689-4038-b5e5-7bc0f3625af3
-- title:
--   §2, §2.1, pp. 6–10 — i.i.d. valuations, traditional loot box with uniform draws, myopic purchases (U_t ≥ 0), R_TB(p), R_TB; first passage r, harmonic tail, ζ_N
-- statement:
--   This file fixes the model of §2 and §2.1 of Chen, Elmachtoub, Hamilton and Lei, together with the random-walk objects used in the proof of their Theorem 3.
--
--   **Valuations.** A monopolist sells $N \ge 1$ distinct virtual items. A random customer's valuations $V_1,\dots,V_N$ are i.i.d. with law $F$, a probability measure on $\mathbb R$ that puts no mass on $(-\infty,0)$ and has a finite second moment (the standing assumptions `ValLaw`). Their mean and variance are
--   $$\mu = \int x\,F(dx), \qquad \sigma^2 = \int (x-\mu)^2\,F(dx).$$
--   A duplicate of an item is worth nothing.
--
--   **The traditional box.** In every period the seller offers a box at a fixed price $p$; each box contains an item drawn uniformly at random from $[N]$, independently of everything else. Writing $d_0, d_1, \dots$ for the draws, the set of items owned before the $(t+1)$-th box is $S_{t+1} = \{d_0,\dots,d_{t-1}\}$, so $S_1 = \emptyset$. The expected utility of the $(t+1)$-th box is
--   $$U_{t+1} = \frac{\sum_{i \in [N]\setminus S_{t+1}} V_i}{N} - p .$$
--
--   **Myopic purchasing.** The customer buys the next box if and only if its expected utility is non-negative, and leaves forever the first time it is negative. The number of boxes bought is therefore the first index $t$ with $U_{t+1} < 0$ (it is $+\infty$ only if that never happens).
--
--   **Revenue.** With the valuations and the draws independent (product law),
--   $$R_{TB}(p) = \frac{p \cdot \mathbb E[\#\text{ of traditional box purchases}]}{N}, \qquad R_{TB} = \sup_{p > 0} R_{TB}(p).$$
--
--   **Walk objects.** For an i.i.d. sequence $w_0, w_1, \dots$ with law $F$ (law `walkLaw F`) and a level $t$, the first passage of the partial sums is
--   $$r(t) = \inf\Big\{ j \ge 1 : t \le \sum_{i<j} w_i \Big\} \in \{1,2,\dots\} \cup \{\infty\}.$$
--   The harmonic tail is $\sum_{k=r}^{N} 1/k$ (zero when $r > N$ or $r = \infty$), and
--   $$\zeta_N = \sum_{i=1}^{N} \frac1i - \log N - \gamma,$$
--   with $\gamma$ the Euler–Mascheroni constant.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Purchase counts take values in $\mathbb N \cup \{\infty\}$ (`ℕ∞`), and expectations and revenues are lower Lebesgue integrals in $[0,\infty]$ (`ℝ≥0∞`), so no expectation is ever truncated to a real number. Draws are 0-based: draw $t$ is the item of the $(t+1)$-th box. The paper's "$\max_p$" is taken as a supremum over prices $p>0$; at $p \le 0$ a customer with non-negative valuations never stops. The law of values and draws needs $N \ge 1$ (`[NeZero N]`). The variance is the centred second moment, finite under the $L^2$ hypothesis.
-- source:
--   Chen, Elmachtoub, Hamilton & Lei, Loot Box Pricing and Design, manuscript submitted August 2019 (Management Science doi:10.1287/mnsc.2020.3748), §2 and §2.1, pp. 6–10; proof of Theorem 3, pp. 32–33 (random walk C_j, r_N, ζ_N)

import Mathlib

namespace LootBox.TB

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Standing hypotheses of §2 (p. 6) on the valuation law `F` (a probability measure on `ℝ`):
valuations are non-negative and have a finite variance (hence a finite mean). -/
structure ValLaw (F : Measure ℝ) [IsProbabilityMeasure F] : Prop where
  nonneg : F (Set.Iio 0) = 0
  sq_int : MemLp id 2 F

/-- µ, the mean of the valuation law. -/
noncomputable def mean (F : Measure ℝ) : ℝ := ∫ x, x ∂F

/-- σ², the variance of the valuation law (centred second moment). -/
noncomputable def var (F : Measure ℝ) : ℝ := ∫ x, (x - mean F) ^ 2 ∂F

/-- Items owned before opening box `t + 1` (draws `0, …, t − 1`): the set `S_{t+1}`. -/
def owned {N : ℕ} (d : ℕ → Fin N) (t : ℕ) : Finset (Fin N) := (Finset.range t).image d

/-- `U_{t+1} = (∑_{i ∉ S_{t+1}} V_i) / N − p`, the expected utility of the `(t+1)`-th traditional box. -/
noncomputable def util {N : ℕ} (p : ℝ) (v : Fin N → ℝ) (d : ℕ → Fin N) (t : ℕ) : ℝ :=
  (∑ i ∈ (owned d t)ᶜ, v i) / N - p

/-- Number of traditional boxes bought by the myopic customer: the first `t` with `U_{t+1} < 0`
(the customer buys while the expected utility is non-negative and leaves forever at the first
negative one); `⊤` if that never happens. -/
noncomputable def purchases {N : ℕ} (p : ℝ) (v : Fin N → ℝ) (d : ℕ → Fin N) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : util p v d t < 0), (t : ℕ∞)

/-- Joint law of the valuations `(V_1, …, V_N)` (i.i.d. `F`) and the box draws (i.i.d. uniform on
the `N` items, independent of the valuations). Draw `t` is the item in the `(t+1)`-th box. -/
noncomputable def law (F : Measure ℝ) [IsProbabilityMeasure F] (N : ℕ) [NeZero N] :
    Measure ((Fin N → ℝ) × (ℕ → Fin N)) :=
  (Measure.pi fun _ : Fin N => F).prod
    (Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype (Fin N)).toMeasure)

/-- `R_TB(p) = p · E[# of traditional box purchases] / N`, valued in `ℝ≥0∞`. -/
noncomputable def revenue (F : Measure ℝ) [IsProbabilityMeasure F] (N : ℕ) [NeZero N] (p : ℝ) :
    ℝ≥0∞ :=
  ENNReal.ofReal p * (∫⁻ ω, ((purchases p ω.1 ω.2 : ℕ∞) : ℝ≥0∞) ∂(law F N)) / N

/-- `R_TB = sup_{p > 0} R_TB(p)`, the optimal normalized revenue of the traditional box. -/
noncomputable def optRevenue (F : Measure ℝ) [IsProbabilityMeasure F] (N : ℕ) [NeZero N] : ℝ≥0∞ :=
  ⨆ (p : ℝ) (_ : 0 < p), revenue F N p

/-- Law of an i.i.d. sequence `w_0, w_1, …` with common law `F` (the backward walk's increments). -/
noncomputable def walkLaw (F : Measure ℝ) [IsProbabilityMeasure F] : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => F

/-- First passage `r(t) = inf {j ≥ 1 | t ≤ ∑_{i<j} w_i}` of the partial-sum walk, `⊤` if never. -/
noncomputable def firstPassage (w : ℕ → ℝ) (t : ℝ) : ℕ∞ :=
  ⨅ (j : ℕ) (_ : 1 ≤ j ∧ t ≤ ∑ i ∈ Finset.range j, w i), (j : ℕ∞)

/-- Harmonic tail `∑_{k=r}^{N} 1/k`; empty (`0`) when `r > N` or `r = ⊤`. -/
noncomputable def harmTail (N : ℕ) (r : ℕ∞) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 N).filter (fun k : ℕ => r ≤ (k : ℕ∞)), (1 : ℝ) / (k : ℝ)

/-- `ζ_N = ∑_{i=1}^{N} 1/i − log N − γ`, with `γ` the Euler–Mascheroni constant. -/
noncomputable def zeta (N : ℕ) : ℝ :=
  (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant

end LootBox.TB


