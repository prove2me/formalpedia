-- Prove2me | Definitions.Def_LeiBR_Rand_Algorithm2
-- name    : LeiBR_Rand_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:34.86472+00:00
-- url     : https://prove2.me/theorems/b74608b1-bff3-4bef-86bb-fa74651b2cf0
-- title:
--   Algorithm 2, (33), Assumption 3, (A.2) — the randomized inexact proximal BR scheme and the weighted norm $\|\cdot\|_P$
-- statement:
--   **Algorithm 2** runs on a probability space $(\Omega, \mathcal F, \mathbb P)$ with a filtration $(\mathcal F_k)_{k \ge 0}$, the information available up to and including the computation of $x_k$. Player $i$ holds coins $\chi_{i,k} \in \{0,1\}$, and $x_0 \in X$ is a given starting profile. At major iteration $k$:
--
--   1. if $\chi_{i,k} = 1$, player $i$ updates to a point $x_{i,k+1} \in X_i$ with
--   $$\mathbb E\big[\|x_{i,k+1} - \widehat x_i(y_k)\|^2 \,\big|\, \mathcal F_k\big] \le \alpha_{i,k}^2 \quad \text{a.s.}, \tag{33}$$
--   where $\alpha_{i,k} \ge 0$ is $\mathcal F_k$-measurable; otherwise $x_{i,k+1} = x_{i,k}$;
--   2. $y_{k+1} = x_{k+1}$.
--
--   **Assumption 3**: $\mathbb P(\chi_{i,k} = 1) = p_i > 0$ and $\chi_{i,k}$ is independent of $\mathcal F_k$. The number of updates of player $i$ before iteration $k$ is $\beta_{i,k} = \sum_{l=0}^{k-1}\chi_{i,l}$ ($\beta_{i,0} = 0$). The **weighted norm** of (A.2) is
--   $$\|x\|_P^2 = \sum_{i=1}^N \frac{\|x_i\|^2}{p_i}.$$
--
--   When the inexact responses come from the stochastic gradient scheme (SA$_{i,k}$), player $i$ draws samples $\xi^t_{i,k}$, $t \ge 1$, that are i.i.d. with the law of $\xi$ and independent of $\mathcal F_k$. It runs $j_{i,k}$ steps from $z_{i,1} = x_{i,k}$ and sets $x_{i,k+1} = z_{i,j_{i,k}}$.
--
--   **Formalization Note**
--   - `IsAlg2Run` is the abstract scheme: any candidates $w_{i,k} \in X_i$, $\mathcal F_{k+1}$-measurable, satisfying (33), with $x_{i,k+1} = w_{i,k}$ if $\chi_{i,k} = 1$. Lean writes "$y_k = x_k$" directly.
--   - `IsAlg2SARun` is the scheme realized by (SA$_{i,k}$). Samples are drawn for every player at every iteration and used only by the players with $\chi_{i,k} = 1$; in law this is the paper's scheme.
--   - Assumption 3 is read as: $\chi_{i,k}$ is independent of $\mathcal F_k$ *together with* player $i$'s round-$k$ candidate (respectively samples). The proof's step (A.4), "By (33) and Assumption 3", needs this.
--   - $\chi_{i,k}$ and the round-$k$ samples are $\mathcal F_{k+1}$-measurable.
--   - $x_0$ is deterministic.
--   - (33) carries an integrability hypothesis, so that the conditional expectation is not the junk value $0$.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 14, Algorithm 2, (33), Assumption 3; p. 15, β_{i,k} and §4.3 (F_k, ξ_{i,k}); p. 31, (A.2)

import Mathlib
import Definitions.Def_LeiBR_Rand_Game
import Definitions.Def_LeiBR_Rand_SA

namespace LeiBR.Rand

open MeasureTheory ProbabilityTheory

variable {N : ℕ} {n : Fin N → ℕ}

/-- The weighted norm (A.2): `‖v‖_P = (∑_i ‖v_i‖²/p_i)^{1/2}`. -/
noncomputable def wnorm (p : Fin N → ℝ) (v : LeiBR.Sync.Profile n) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2 / p i)

/-- `β_{i,k} = ∑_{l=0}^{k-1} χ_{i,l}` (with `β_{i,0} = 0`), the number of updates of player `i`
before major iteration `k` (p. 15). -/
def beta {Ω : Type*} (χ : Fin N → ℕ → Ω → ℕ) (i : Fin N) (k : ℕ) (ω : Ω) : ℕ :=
  ∑ l ∈ Finset.range k, χ i l ω

/-- A run of Algorithm 2 (randomized inexact proximal BR scheme, p. 14) on the probability space
`(Ω, P)` with filtration `F`.

* `χ i k ∈ {0, 1}` is player `i`'s coin at major iteration `k`; it is `F_{k+1}`-measurable,
  `P(χ_{i,k} = 1) = p_i ∈ (0, 1]`, and (Assumption 3) it is independent of `F_k` and of the
  round-`k` candidate `w_{i,k}`.
* `x 0` is the deterministic feasible point `x0`; `x_{i,k+1} = w_{i,k}` if `χ_{i,k} = 1` and
  `x_{i,k+1} = x_{i,k}` otherwise (step (1)); `y_k = x_k` (step (2)).
* The candidate `w_{i,k} ∈ X_i` is `F_{k+1}`-measurable and satisfies the inexactness
  condition (33): `E[‖w_{i,k} − x̂_i(x_k)‖² | F_k] ≤ α²_{i,k}` a.s., with `α_{i,k} ≥ 0`
  `F_k`-measurable. -/
structure IsAlg2Run {Ω : Type*} [MeasurableSpace Ω] (G : Game N n) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n)
    (P : Measure Ω) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (p : Fin N → ℝ)
    (χ : Fin N → ℕ → Ω → ℕ) (w : ∀ i, ℕ → Ω → LeiBR.Sync.Strat n i) (α : Fin N → ℕ → Ω → ℝ)
    (x0 : LeiBR.Sync.Profile n) (x : ℕ → Ω → LeiBR.Sync.Profile n) : Prop where
  p_pos : ∀ i, 0 < p i
  p_le_one : ∀ i, p i ≤ 1
  coin_le_one : ∀ i k ω, χ i k ω ≤ 1
  coin_meas : ∀ i k, Measurable[F (k + 1)] (χ i k)
  coin_prob : ∀ i k, P {ω | χ i k ω = 1} = ENNReal.ofReal (p i)
  coin_indep : ∀ i k, Indep (MeasurableSpace.comap (χ i k) inferInstance)
    (F k ⊔ MeasurableSpace.comap (w i k) inferInstance) P
  x0_feas : G.Feasible x0
  init : ∀ ω, x 0 ω = x0
  step : ∀ k ω i, x (k + 1) ω i = if χ i k ω = 1 then w i k ω else x k ω i
  w_mem : ∀ i k ω, w i k ω ∈ G.X i
  w_meas : ∀ i k, StronglyMeasurable[F (k + 1)] (w i k)
  α_nonneg : ∀ i k ω, 0 ≤ α i k ω
  α_meas : ∀ i k, Measurable[F k] (α i k)
  inexact : ∀ i k, Integrable (fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2) P ∧
    P[fun ω => ‖w i k ω - xhat (x k ω) i‖ ^ 2 | F k] ≤ᵐ[P] fun ω => α i k ω ^ 2

/-- A run of Algorithm 2 in which every candidate is computed by the projected stochastic
gradient scheme (SA_{i,k}) (§4.3, p. 15).

* Coins as in `IsAlg2Run`; the coin `χ_{i,k}` is independent of `F_k` together with player `i`'s
  round-`k` samples (Assumption 3).
* `ξs i k t` (`t ≥ 1`) is player `i`'s `t`-th sample at major iteration `k`: each has the law `μξ`
  of `ξ`, `(ξs i k t)_{t ≥ 1}` are i.i.d., the vector `ξ_{i,k}` is independent of `F_k`, and all
  are `F_{k+1}`-measurable. (Samples are drawn for every player at every iteration and used
  only by the players with `χ_{i,k} = 1`.)
* `x 0 = x0` is deterministic and feasible. If `χ_{i,k} = 1`, player `i` runs (SA_{i,k}) from
  `z_{i,1} = x_{i,k}` with `y_k = x_k` and the projection `Π_i` onto `X_i`, for `j i k ω` steps,
  and `x_{i,k+1} = z_{i, j_{i,k}}`; otherwise `x_{i,k+1} = x_{i,k}`. -/
structure IsAlg2SARun {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (G : Game N n)
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i) (mu : ℝ)
    (μξ : Measure (EuclideanSpace ℝ (Fin d)))
    (P : Measure Ω) (F : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (p : Fin N → ℝ)
    (χ : Fin N → ℕ → Ω → ℕ) (ξs : Fin N → ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (j : Fin N → ℕ → Ω → ℕ) (x0 : LeiBR.Sync.Profile n) (x : ℕ → Ω → LeiBR.Sync.Profile n) : Prop where
  p_pos : ∀ i, 0 < p i
  p_le_one : ∀ i, p i ≤ 1
  coin_le_one : ∀ i k ω, χ i k ω ≤ 1
  coin_meas : ∀ i k, Measurable[F (k + 1)] (χ i k)
  coin_prob : ∀ i k, P {ω | χ i k ω = 1} = ENNReal.ofReal (p i)
  coin_indep : ∀ i k, Indep (MeasurableSpace.comap (χ i k) inferInstance)
    (F k ⊔ ⨆ t, MeasurableSpace.comap (ξs i k (t + 1)) inferInstance) P
  sample_meas : ∀ i k t, Measurable[F (k + 1)] (ξs i k t)
  sample_law : ∀ i k t, Measure.map (ξs i k (t + 1)) P = μξ
  sample_iid : ∀ i k, iIndepFun (fun t => ξs i k (t + 1)) P
  sample_indep : ∀ i k, Indep (⨆ t, MeasurableSpace.comap (ξs i k (t + 1)) inferInstance) (F k) P
  x0_feas : G.Feasible x0
  init : ∀ ω, x 0 ω = x0
  step : ∀ k ω i, x (k + 1) ω i = if χ i k ω = 1 then
      saIter (proj i) (fun t z => saDir gψ mu i (x k ω) (ξs i k t ω) z) mu (x k ω i) (j i k ω)
    else x k ω i

end LeiBR.Rand


