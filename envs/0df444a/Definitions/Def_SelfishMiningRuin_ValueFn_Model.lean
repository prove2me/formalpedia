-- Prove2me | Definitions.Def_SelfishMiningRuin_ValueFn_Model
-- name    : SelfishMiningRuin_ValueFn_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:22.906021+00:00
-- url     : https://prove2.me/theorems/ee2a2e70-2fbd-4272-8b4c-2acb64c97448
-- title:
--   Selfish mining states, rewards, surplus and exponential-horizon value function
-- statement:
--   A miner pays operating costs at rate $c>0$ and receives $b>0$ for each rewarded block. Network blocks arrive at Poisson rate $\lambda>0$. The state $z\in\{0,1,0^*\}$ records whether the miner has no withheld block, one withheld block, or a public fork. At each block, $\xi$ records whether the miner found it and $\zeta$ whether a competing miner extends the miner's branch of a fork. Their Bernoulli probabilities are $p$ and $q$. The transition and reward maps encode the six cases in the paper's rule (16).
--
--   For initial surplus $u$, let $N_s$ count blocks by time $s$, let $Z_k$ be the state before block $k+1$, and let $f$ be the number of rewarded blocks. The surplus and ruin time are
--
--   $$
--   R_s=u-cs+b\sum_{k=0}^{N_s-1}f(Z_k,\xi_{k+1},\zeta_{k+1}),\qquad
--   \tau_u=\inf\{s\ge0:R_s=0\}.
--   $$
--
--   The fixed-horizon value is $V_z(u,s)=\mathbb E[R_s\mathbf1_{\{\tau_u>s\}}]$ for a chain started at $z$. The exponential-horizon value is
--
--   $$
--   \widehat V_z(u,t)=\int V_z(u,s)\,d\operatorname{Exp}(1/t)(s),
--   $$
--
--   where $t>0$ is the mean horizon. This model is shared by the goal and the differential-system milestone.
--
--   **Formalization Note** The Poisson process is built from independent exponential interarrival times, and marks are indexed from zero in Lean. Ruin time takes values in the extended nonnegative reals.
-- source:
--   Albrecher & Goffard, On the profitability of selfish blockchain mining under consideration of ruin, arXiv:2010.12577v1, pp. 3, 5, 8–9, 11, equations (1), (3), (9), (15), (16), (19)

import Mathlib

set_option autoImplicit false

namespace SelfishMiningRuin.ValueFn

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The withheld-block state: no block, one block, or a public fork. -/
inductive St where
  | zero | one | fork
  deriving DecidableEq, Inhabited

/-- The state transition on the next discovery, as in the bullets on pp. 8–9. -/
def step : St → Bool → Bool → St
  | .zero, true, _ => .one
  | .zero, false, _ => .zero
  | .one, true, _ => .zero
  | .one, false, _ => .fork
  | .fork, _, _ => .zero

/-- The number of paid blocks at one discovery, equation (16). -/
def reward : St → Bool → Bool → ℕ
  | .zero, _, _ => 0
  | .one, true, _ => 2
  | .one, false, _ => 0
  | .fork, true, _ => 2
  | .fork, false, true => 1
  | .fork, false, false => 0

/-- Bernoulli law on Bool, with `true` of probability `r`. -/
noncomputable def bern (r : ℝ) : Measure Bool :=
  ENNReal.ofReal r • Measure.dirac true + ENNReal.ofReal (1 - r) • Measure.dirac false

/-- Joint i.i.d. law of the positive interarrival times and two independent marks. -/
structure Primitives {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam p q : ℝ) (W : ℕ → Ω → ℝ) (ξ ζ : ℕ → Ω → Bool) : Prop where
  indep : iIndepFun (fun n ω => (W n ω, ξ n ω, ζ n ω)) P
  law : ∀ n, HasLaw (fun ω => (W n ω, ξ n ω, ζ n ω))
    ((expMeasure lam).prod ((bern p).prod (bern q))) P

/-- Block `n` arrives at the sum of its first `n` interarrival times. -/
def arrival {Ω : Type*} (W : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, W k ω

/-- Number of blocks found by time `s`. -/
noncomputable def blocks {Ω : Type*} (W : ℕ → Ω → ℝ) (s : ℝ) (ω : Ω) : ℕ :=
  {n : ℕ | 1 ≤ n ∧ arrival W n ω ≤ s}.ncard

/-- The chain at block index `k`, with `k = 0` the given initial state. -/
def chain {Ω : Type*} (ξ ζ : ℕ → Ω → Bool) (z : St) (ω : Ω) : ℕ → St
  | 0 => z
  | k + 1 => step (chain ξ ζ z ω k) (ξ k ω) (ζ k ω)

/-- The selfish miner's surplus process, equation (15). -/
noncomputable def surplus {Ω : Type*} (W : ℕ → Ω → ℝ) (ξ ζ : ℕ → Ω → Bool)
    (c b u s : ℝ) (z : St) (ω : Ω) : ℝ :=
  u - c * s + b * ∑ k ∈ Finset.range (blocks W s ω),
    (reward (chain ξ ζ z ω k) (ξ k ω) (ζ k ω) : ℝ)

/-- First time at which the surplus reaches zero; `⊤` if it never does. -/
noncomputable def ruinTime {Ω : Type*} (W : ℕ → Ω → ℝ) (ξ ζ : ℕ → Ω → Bool)
    (c b u : ℝ) (z : St) (ω : Ω) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ s : ℝ, 0 ≤ s ∧ surplus W ξ ζ c b u s z ω = 0 ∧
    r = ENNReal.ofReal s}

/-- Fixed-horizon expected surplus under the ruin constraint, equation (3). -/
noncomputable def V {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℕ → Ω → ℝ) (ξ ζ : ℕ → Ω → Bool)
    (c b u s : ℝ) (z : St) : ℝ :=
  ∫ ω, (if ENNReal.ofReal s < ruinTime W ξ ζ c b u z ω
    then surplus W ξ ζ c b u s z ω else 0) ∂P

/-- Expected surplus at an independent exponential horizon of mean `t`, equation (19). -/
noncomputable def Vhat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℕ → Ω → ℝ) (ξ ζ : ℕ → Ω → Bool)
    (c b u t : ℝ) (z : St) : ℝ :=
  ∫ s, V P W ξ ζ c b u s z ∂(expMeasure t⁻¹)

end SelfishMiningRuin.ValueFn


