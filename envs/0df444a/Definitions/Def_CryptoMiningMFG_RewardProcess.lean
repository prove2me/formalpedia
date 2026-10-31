-- Prove2me | Definitions.Def_CryptoMiningMFG_RewardProcess
-- name    : CryptoMiningMFG_RewardProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:58:21.786358+00:00
-- url     : https://prove2.me/theorems/4ffb1ff9-1bb6-4cd0-b9fe-52f574678829
-- title:
--   Reward counting process with intensity $\mathcal K\alpha/(\alpha+M\bar\alpha)$ and wealth $X$
-- statement:
--   Fix a mean hash rate $\bar\alpha$, a control $\varphi$ and a start time $t$. The miner's rewards arrive at the jumps of a counting process $N$ whose intensity, while the hash rate in force is $\alpha_s$, is the reward intensity of eq. (2.2):
--
--   $$
--   \lambda_s=\begin{cases}\mathcal K\,\dfrac{\alpha_s}{\alpha_s+M\bar\alpha_s}, & \alpha_s>0,\\[4pt] 0, & \alpha_s=0.\end{cases}
--   $$
--
--   The process is constructed from i.i.d. exponential clocks $E_0,E_1,\dots\sim\mathrm{Exp}(1)$: with $\tau_0=t$, the $(j+1)$-st reward comes at the first time $s\ge\tau_j$ with
--
--   $$
--   \int_{(\tau_j,s]}\lambda_u\,du\ \ge\ E_j,
--   $$
--
--   and never if there is no such time. $N_s$ counts the rewards in $(t,s]$, and the hash rate in force at time $s$ is $\varphi_j(s;\tau_1,\dots,\tau_j)$ for $\tau_j<s\le\tau_{j+1}$. The miner's **wealth**, started at $(t,x)$, follows eq. (2.3), $dX_s=-c\,\alpha_s\,ds+r\,dN_s$:
--
--   $$
--   X_s=x-c\int_{(t,s]}\alpha_u\,du+r\,N_s .
--   $$
--
--   This is the dynamics of an individual miner facing the population; every expectation in the mission is over the clocks.
--
--   **Formalization Note** $N_s$ is counted in $\mathbb N\cup\{\infty\}$; since $\lambda\le\mathcal K$ on $[t_0,T]$ it is finite almost surely. The real wealth uses $N_s$ as a natural number and is meaningless on the null event $N_s=\infty$, which every expectation excludes explicitly. A clock $E_j\le0$ (a null event) produces a reward at $\tau_j$ itself. Mining takes place over $[t_0,T]$, where $\bar\alpha$ is given: the intensity is $0$ at times outside $[t_0,T]$.
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, eq. (2.2) and footnote 13 p.9 (jump intensity), eq. (2.3) p.9 (wealth dynamics)

import Mathlib
import Definitions.Def_CryptoMiningMFG_Model
import Definitions.Def_CryptoMiningMFG_Control

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CryptoMiningMFG

/-- The exponential distribution with rate `1` is a probability measure. -/
instance isProbabilityMeasure_expMeasure_one : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- The i.i.d. `Exp(1)` clocks `E₀, E₁, …` that drive a miner's reward process: the infinite
product of the exponential distribution with rate `1`. -/
noncomputable def clockLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => expMeasure 1)

/-- The time of the last of `j` rewards received at times `τ`, and the start time `t` when
`j = 0`. -/
def lastTime (t : ℝ) : (j : ℕ) → (Fin j → ℝ) → ℝ
  | 0, _ => t
  | k + 1, τ => τ (Fin.last k)

namespace Control

variable (P : Model) (abar : ℝ → ℝ) (u : Control) (t : ℝ)

/-- **Reward intensity**, eq. (2.2), p.9 of Li, Reppen, Sircar, arXiv:1912.01952v2:
`λ = 𝒦 α / (α + M ᾱ_s)` if the hash rate in force `α = φ_j(s; τ)` is positive, and `0` if it is
`0`, while `j` rewards have been received at times `τ`.

**Formalization Note.** Mining takes place over the period `[t0, T]` (p.8), and `ᾱ` is only
given there: the intensity is `0` at times `s ∉ [t0, T]`. Without this cut-off a mean hash rate
with `α + M ᾱ_s → 0` just after `T` would make the cumulative intensity infinite immediately
after `T`, place infinitely many rewards at time `T`, and turn `E[e^{−γ X_T}]` into the junk
value `0`. -/
noncomputable def intensity (j : ℕ) (τ : Fin j → ℝ) (s : ℝ) : ℝ :=
  if s ∈ Icc P.t0 P.T ∧ 0 < u.φ j s τ then P.K * u.φ j s τ / (u.φ j s τ + P.M * abar s) else 0

/-- Cumulative intensity `∫_{(τ_j, s]} λ_v dv` since the last reward (or since the start time
`t` if there is none). -/
noncomputable def cumIntensity (j : ℕ) (τ : Fin j → ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Ioc (lastTime t j τ) s, ENNReal.ofReal (u.intensity P abar j τ v)

open Classical in
/-- The time of the `(j+1)`-st reward given the first `j` reward times `τ` and the clock value
`e`: the first time `s ≥ τ_j` at which the cumulative intensity since `τ_j` reaches `e`, or `none`
if it never does. -/
noncomputable def nextReward (j : ℕ) (τ : Fin j → ℝ) (e : ℝ) : Option ℝ :=
  if {s : ℝ | lastTime t j τ ≤ s ∧ ENNReal.ofReal e ≤ u.cumIntensity P abar t j τ s}.Nonempty then
    some (sInf {s : ℝ | lastTime t j τ ≤ s ∧ ENNReal.ofReal e ≤ u.cumIntensity P abar t j τ s})
  else none

/-- The reward history driven by the clocks `E` for a miner starting at time `t`:
`history E j = some τ` with `τ` the first `j` reward times if at least `j` rewards ever occur, and
`none` otherwise. The `(j+1)`-st reward uses the clock `E j`. -/
noncomputable def history (E : ℕ → ℝ) : (j : ℕ) → Option (Fin j → ℝ)
  | 0 => some Fin.elim0
  | j + 1 => (history E j).bind fun τ =>
      (u.nextReward P abar t j τ (E j)).map fun s => Fin.snoc (α := fun _ => ℝ) τ s

/-- `rewardTime E j` is the time `τ_j` of the `j`-th reward (`τ₀ = t`), and `⊤` if fewer than `j`
rewards ever occur. -/
noncomputable def rewardTime (E : ℕ → ℝ) (j : ℕ) : WithTop ℝ :=
  (u.history P abar t E j).elim ⊤ fun τ => ((lastTime t j τ : ℝ) : WithTop ℝ)

/-- `N_s`: the number of rewards received in `(t, s]`, i.e. the number of `j ≥ 1` with
`τ_j ≤ s`, counted in `ℕ∞` (it is finite almost surely). -/
noncomputable def rewardCount (E : ℕ → ℝ) (s : ℝ) : ℕ∞ :=
  {j : ℕ | 1 ≤ j ∧ u.rewardTime P abar t E j ≤ ((s : ℝ) : WithTop ℝ)}.encard

open Classical in
/-- `α_s`: the hash rate in force at time `s`, i.e. `φ_j(s; τ₁, …, τ_j)` for `τ_j < s ≤ τ_{j+1}`
(the rule of the last reward strictly before `s`), and `0` for `s ≤ t` or after an accumulation of
rewards. At most one term of the sum is nonzero. -/
noncomputable def rateAt (E : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' j : ℕ, (u.history P abar t E j).elim 0 fun τ =>
    if lastTime t j τ < s ∧ ((s : ℝ) : WithTop ℝ) ≤ u.rewardTime P abar t E (j + 1) then
      u.φ j s τ else 0

/-- The **wealth** `X_s` of a miner who starts at time `t` with wealth `x`, eq. (2.3), p.9:
`dX_s = −c α_s ds + r dN_s`, i.e. `X_s = x − c ∫_{(t, s]} α_v dv + r N_s`.

**Formalization Note.** The cumulative hash rate is a lower Lebesgue integral and `N_s` is read
through `ℕ∞.toNat`; both are finite almost surely (the intensity is at most `𝒦` on `[t0, T]`).
On the null event `N_s = ∞` this real number is meaningless, and every expectation below sets the
integrand to `0` there. -/
noncomputable def wealth (x : ℝ) (E : ℕ → ℝ) (s : ℝ) : ℝ :=
  x - P.c * (∫⁻ v in Ioc t s, ENNReal.ofReal (u.rateAt P abar t E v)).toReal
    + P.r * ((u.rewardCount P abar t E s).toNat : ℝ)

end Control

end CryptoMiningMFG


