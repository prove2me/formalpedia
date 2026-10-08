-- Prove2me | Definitions.Def_SongZipkinFluct_FixedCost_Model
-- name    : SongZipkinFluct_FixedCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:22.900413+00:00
-- url     : https://prove2.me/theorems/27637770-15d1-4876-a310-5965e58405e9
-- title:
--   §1–§2 — the fluctuating-demand inventory model: data, standing hypotheses, lead-time demand law, C(i, y) and the myopic cost G⁺(i, y)
-- statement:
--   This file sets up the continuous-review inventory model of Song and Zipkin in which the demand rate is modulated by a Markov chain describing the "state of the world".
--
--   **Data.** The world is a continuous-time Markov chain $A$ on a countable, nonempty state space $I$ with generator $Q = (q_{ij})$; write $q_i = -q_{ii}$. While $A = i$, unit demands arrive as a Poisson process with rate $\lambda_i$. Unmet demand is fully backlogged. Orders arrive after a random lead time $L$ with law $F_L$. The costs are a fixed order cost $\bar K$, a unit order cost $\bar c$ (paid when the order arrives), a holding cost rate $h$ and a backorder penalty rate $p$; $\alpha$ is the discount rate and $\mu$ the uniformization rate.
--
--   **Standing hypotheses.**
--   1. $q_{ij} \ge 0$ for $j \ne i$ and $q_i = \sum_{j \ne i} q_{ij}$ (a convergent series);
--   2. $\lambda_i \ge 0$, and $q^* = \sup_i q_i$ and $\lambda^* = \sup_i \lambda_i$ are finite;
--   3. $\mu > 0$ and $\mu \ge q^* + \lambda^*$;
--   4. $\alpha > 0$, $\bar c \ge 0$, $\bar K \ge 0$, $h > 0$, $p > 0$;
--   5. $F_L$ is a probability law on $[0, \infty)$, and $L$ is independent of the world and of the demand.
--
--   **Derived quantities.** With $\tilde F_L(\alpha) = E[e^{-\alpha L}]$,
--   $$
--   c = \bar c\,\tilde F_L(\alpha),\qquad K = \bar K\,\tilde F_L(\alpha),\qquad \beta = \frac{1}{\mu+\alpha},\qquad \gamma = \beta\mu,\qquad \hat C(x) = \begin{cases} -px, & x < 0,\\ hx, & x \ge 0.\end{cases}
--   $$
--   Let $f_i(d \mid l)$ be the probability that $d$ units are demanded in $(0, l]$ given $A(0) = i$, and $g_i(d \mid \alpha) = E[e^{-\alpha L} f_i(d \mid L)]$. The expected discounted inventory cost rate at the end of a lead time, when the world is in state $i$ and the inventory position is $y \in \mathbb Z$, is
--   $$
--   C(i, y) = E\big[e^{-\alpha L}\hat C(y - D^i_L)\big] = \sum_{d \ge 0} g_i(d \mid \alpha)\,\hat C(y - d),
--   $$
--   and the **myopic cost function** is
--   $$
--   G^+(i, y) = (1-\gamma)\,c\,y + \beta\,C(i, y).
--   $$
--   Finally $\delta(z) = 0$ for $z = 0$ and $1$ for $z > 0$, and $\Delta f(i, x) = f(i, x+1) - f(i, x)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The hypotheses $h, p, \alpha > 0$, $\bar c, \bar K \ge 0$, $\mu > 0$ and the independence of $L$ are the paper's standing conventions, not printed as hypotheses. The paper never constructs the Markov-modulated Poisson demand; $f_i(d \mid l)$ is defined through uniformization at rate $\mu$: with $u_n(i, d)$ the $n$-step probability that the jump chain on $I \times \mathbb N$ that moves $(i, d) \to (i, d+1)$ with probability $\lambda_i/\mu$, $(i, d) \to (j, d)$ with probability $q_{ij}/\mu$ ($j \ne i$) and stays otherwise, started at $(i, 0)$, has count $d$, $f_i(d \mid l) = \sum_n e^{-\mu l}(\mu l)^n/n!\,u_n(i, d)$. This is the standard exact representation, not a theorem of the paper. The structure `Model` carries no instance arguments; statements assume $I$ countable, nonempty and with decidable equality.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, pp. 353–355, §1–§2; p. 361, (16)

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Model

open MeasureTheory

namespace SongZipkinFluct.FixedCost

/-- The data of the fluctuating-demand inventory model of Song and Zipkin,
*Inventory Control in a Fluctuating Demand Environment*, Oper. Res. 41(2):351–370 (1993),
DOI 10.1287/opre.41.2.351, §1, pp. 353–354.

* `Q i j` is the generator `(q_ij)` of the world chain `A` on the countable state space `I`;
* `lam i` is the Poisson demand rate `λ_i` while `A = i`;
* `μ` is the uniformization rate of §2, p. 354;
* `α` is the discount rate;
* `leadLaw` is the law `F_L` of the lead time `L`;
* `cbar`, `Kbar` are the actual unit and fixed order costs `c̄`, `K̄`;
* `h`, `p` are the holding and backorder-penalty cost rates.

The standing hypotheses are collected separately in `Model.Standing`. -/
structure Model (I : Type*) where
  Q : I → I → ℝ
  lam : I → ℝ
  μ : ℝ
  α : ℝ
  leadLaw : Measure ℝ
  cbar : ℝ
  Kbar : ℝ
  h : ℝ
  p : ℝ

namespace Model

variable {I : Type*}

/-- `q_i = −q_ii`, the total jump rate out of world state `i` (p. 353). -/
def qrate (M : Model I) (i : I) : ℝ := -M.Q i i

/-- The standing hypotheses of §1–§2 (pp. 353–355).

Formalization Note: `h > 0`, `p > 0`, `α > 0`, `c̄ ≥ 0`, `K̄ ≥ 0`, `μ > 0` and the lead time
being a.s. finite and nonnegative are not printed as hypotheses in the paper but are its
standing conventions; the lead time is independent of the world and of the demand, which is
built into the definition of the lead-time demand law `discDemandMass` below. The
generator is conservative: `q_i = Σ_{j ≠ i} q_ij` (a convergent series). The suprema
`q* = sup_i q_i` and `λ* = sup_i λ_i` are finite (`BddAbove`, p. 353), and the uniformization
rate satisfies `μ ≥ q* + λ*` (p. 354). -/
structure Standing [DecidableEq I] (M : Model I) : Prop where
  offdiag_nonneg : ∀ i j, j ≠ i → 0 ≤ M.Q i j
  conservative : ∀ i, HasSum (fun j => if j = i then 0 else M.Q i j) (M.qrate i)
  lam_nonneg : ∀ i, 0 ≤ M.lam i
  q_bdd : BddAbove (Set.range M.qrate)
  lam_bdd : BddAbove (Set.range M.lam)
  μ_pos : 0 < M.μ
  μ_ge : (⨆ i, M.qrate i) + (⨆ i, M.lam i) ≤ M.μ
  α_pos : 0 < M.α
  lead_prob : IsProbabilityMeasure M.leadLaw
  lead_nonneg : ∀ᵐ l ∂M.leadLaw, 0 ≤ l
  cbar_nonneg : 0 ≤ M.cbar
  Kbar_nonneg : 0 ≤ M.Kbar
  h_pos : 0 < M.h
  p_pos : 0 < M.p

/-- The Laplace transform of the lead time at the discount rate, `F̃_L(α) = E[e^{−αL}]`
(p. 353–354). -/
noncomputable def lapL (M : Model I) : ℝ := ∫ l, Real.exp (-M.α * l) ∂M.leadLaw

/-- The discounted unit order cost `c = E[e^{−αL} c̄] = c̄ F̃_L(α)` (p. 354). -/
noncomputable def c (M : Model I) : ℝ := M.cbar * M.lapL

/-- The discounted fixed order cost `K = E[e^{−αL} K̄] = K̄ F̃_L(α)` (p. 354). -/
noncomputable def K (M : Model I) : ℝ := M.Kbar * M.lapL

/-- `β = 1/(μ + α)` (p. 355). -/
noncomputable def β (M : Model I) : ℝ := 1 / (M.μ + M.α)

/-- `γ = βμ` (p. 355). -/
noncomputable def γ (M : Model I) : ℝ := M.β * M.μ

/-- The inventory cost rate `Ĉ(x) = −px` for `x < 0` and `hx` otherwise (p. 354). -/
noncomputable def Chat (M : Model I) (x : ℝ) : ℝ := if x < 0 then -M.p * x else M.h * x

/-- One step of the uniformized jump chain on `I × ℕ` (world state, demand count), seen
through first-step analysis: `uStep M u i d` is the probability that the count after `n + 1`
steps from `(i, 0)` equals `d`, given `u j d' =` the same probability after `n` steps from
`(j, 0)`. From `(i, d)` the chain moves to `(i, d + 1)` with probability `λ_i/μ`, to `(j, d)`
with probability `q_ij/μ` (`j ≠ i`), and stays with probability `1 − (λ_i + q_i)/μ`. -/
noncomputable def uStep [DecidableEq I] (M : Model I) (u : I → ℕ → ℝ) (i : I) (d : ℕ) : ℝ :=
  (if d = 0 then 0 else M.lam i / M.μ * u i (d - 1))
    + (∑' j, if j = i then 0 else M.Q i j / M.μ * u j d)
    + (1 - (M.lam i + M.qrate i) / M.μ) * u i d

/-- `demandSteps M n i d`: probability that the uniformized chain started at `(i, 0)` has demand
count `d` after `n` steps. -/
noncomputable def demandSteps [DecidableEq I] (M : Model I) : ℕ → I → ℕ → ℝ
  | 0 => fun _ d => if d = 0 then 1 else 0
  | n + 1 => M.uStep (demandSteps M n)

/-- `f_i(d | l)`: the probability mass function of the demand `D(l)` in `(0, l]` given
`A(0) = i` (§5, p. 361), defined through uniformization at rate `μ`:
`f_i(d | l) = Σ_n e^{−μl} (μl)^n / n! · u_n(i, d)`.

Formalization Note: the paper never constructs the Markov-modulated Poisson process; this is
the standard exact representation of its counting law by uniformization (the paper's own
device, §2 p. 354 and §4.1 p. 359). It is a definition, not a theorem of the paper. -/
noncomputable def demandMass [DecidableEq I] (M : Model I) (i : I) (d : ℕ) (l : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-M.μ * l) * (M.μ * l) ^ n / (n.factorial : ℝ) * M.demandSteps n i d

/-- `g_i(d | α) = E[e^{−αL} f_i(d | L)]` ((16), p. 361): the discounted mass function of the
lead-time demand `D^i_L`. The lead time `L` with law `F_L` is independent of the world and the
demand, which is what this formula presupposes. -/
noncomputable def discDemandMass [DecidableEq I] (M : Model I) (i : I) (d : ℕ) : ℝ :=
  ∫ l, Real.exp (-M.α * l) * M.demandMass i d l ∂M.leadLaw

/-- `C(i, y) = E[e^{−αL} Ĉ(y − D^i_L)] = Σ_d g_i(d | α) Ĉ(y − d)` (p. 354 and (16), p. 361). -/
noncomputable def C [DecidableEq I] (M : Model I) (i : I) (y : ℤ) : ℝ :=
  ∑' d : ℕ, M.discDemandMass i d * M.Chat ((y : ℝ) - (d : ℝ))

/-- The myopic cost function `G⁺(i, y) = (1 − γ) c y + β C(i, y)` (p. 355). -/
noncomputable def Gplus [DecidableEq I] (M : Model I) (i : I) (y : ℤ) : ℝ :=
  (1 - M.γ) * M.c * y + M.β * M.C i y

end Model

/-- The difference operator in the second variable, `Δf(i, x) = f(i, x + 1) − f(i, x)`
(p. 354). -/
def diff {I : Type*} (f : I → ℤ → ℝ) (i : I) (x : ℤ) : ℝ := f i (x + 1) - f i x

end SongZipkinFluct.FixedCost


