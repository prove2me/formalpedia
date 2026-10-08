-- Prove2me | Definitions.Def_SongZipkinFluct_Monotone_Model
-- name    : SongZipkinFluct_Monotone_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:42.703297+00:00
-- url     : https://prove2.me/theorems/2750d92e-a2ba-4a51-a8be-bb029eb3cfce
-- title:
--   §1–§2 — the fluctuating-demand inventory model: lead-time demand, C(i, y) and the myopic cost G⁺(i, y)
-- statement:
--   This file sets up the continuous-review inventory model of Song and Zipkin (1993) in which the demand rate is driven by a Markov chain describing the "state of the world".
--
--   **Data.** Let $\mathbf I$ be a countable, nonempty set of world states. The world is a continuous-time Markov chain $A$ on $\mathbf I$ with generator $Q = (q_{ij})$; write $q_i = -q_{ii}$, $q^* = \sup_i q_i$ and $\lambda^* = \sup_i \lambda_i$. While $A = i$, demand arrives as a Poisson process of rate $\lambda_i$. Further data are a uniformization rate $\mu$, a discount rate $\alpha$, the law $F_L$ of the lead time $L$, the actual unit and fixed order costs $\bar c$ and $\bar K$, and the holding and penalty cost rates $h$ and $p$.
--
--   **Standing hypotheses.** $q_{ij} \ge 0$ for $j \ne i$ and $q_i = \sum_{j \ne i} q_{ij}$; $\lambda_i \ge 0$; $q^*$ and $\lambda^*$ are finite; $\mu > 0$ and $\mu \ge q^* + \lambda^*$; $\alpha > 0$; $F_L$ is a probability law on $[0,\infty)$; $\bar c, \bar K \ge 0$ and $h, p > 0$. **Assumption 1** is the separate condition $\alpha \bar c < p$.
--
--   **Derived quantities.** $\tilde F_L(\alpha) = E[e^{-\alpha L}]$, $c = \bar c\,\tilde F_L(\alpha)$, $K = \bar K\,\tilde F_L(\alpha)$, $\beta = 1/(\mu+\alpha)$, $\gamma = \beta\mu$, $\delta(z) = 0$ for $z = 0$ and $1$ for $z > 0$, and
--   $$\hat C(x) = \begin{cases} -px, & x < 0,\\ hx, & x \ge 0.\end{cases}$$
--   Let $f_i(d \mid l)$ be the probability that $d$ demands occur in $(0, l]$ given $A(0) = i$, and $D^i_L$ the demand during the lead time, with $P(D^i_L = d) = E[f_i(d \mid L)]$. With $g_i(d \mid \alpha) = E[e^{-\alpha L} f_i(d \mid L)]$,
--   $$C(i,y) = E\big[e^{-\alpha L}\hat C(y - D^i_L)\big] = \sum_{d \ge 0} g_i(d \mid \alpha)\,\hat C(y-d), \qquad G^+(i,y) = (1-\gamma)c\,y + \beta\,C(i,y)$$
--   for integer inventory positions $y$. $G^+$ is the **myopic cost function**. The difference operator acts on the second variable: $\Delta f(i,x) = f(i,x+1) - f(i,x)$. Finally, $y$ is *the smallest minimizer* of a function $f : \mathbb Z \to \mathbb R$ if $f(y) \le f(z)$ for all $z$ and no smaller integer has this property.
--
--   These are the objects in which all results of §4 of the paper are stated.
--
--   **Formalization Note.** The paper never constructs the Markov-modulated Poisson demand process. Here $f_i(d \mid l) = \sum_n e^{-\mu l}(\mu l)^n/n!\, u_n(i,d)$, where $u_n(i,d)$ is the probability that the jump chain uniformized at rate $\mu$ (a demand with probability $\lambda_i/\mu$, a move to $j \ne i$ with probability $q_{ij}/\mu$, nothing otherwise) has counted $d$ demands after $n$ jumps from world state $i$. This is the standard exact representation for bounded rates. The lead time is independent of the world and the demand, as display (16) presupposes. The conditions $\alpha, \mu, h, p > 0$ and $\bar c, \bar K \ge 0$ are not printed in the paper but are needed.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, pp. 353–356, §1–§2 (C(i, y) p. 354, G⁺ p. 355, Assumption 1 p. 356) and p. 361, display (16)

import Mathlib

open MeasureTheory

namespace SongZipkinFluct.Monotone

/-- **The fluctuating-demand inventory model** (Song and Zipkin, Oper. Res. 41(2):351–370 (1993),
DOI 10.1287/opre.41.2.351, §1, pp. 353–354; §2, pp. 354–355).

The data of the model, for a countable set `I` of world states:
* `Q i j = q_ij`, the infinitesimal generator of the world chain `A`;
* `lam i = λ_i`, the Poisson demand rate while `A = i`;
* `μ`, the uniformization rate (`μ ≥ q* + λ*`, p. 354);
* `α`, the discount rate;
* `leadLaw = F_L`, the law of the lead time `L` (a probability measure on `[0, ∞)`);
* `cbar = c̄`, `Kbar = K̄`, the actual unit and fixed order costs;
* `h`, `p`, the holding and penalty cost rates.

The standing hypotheses are the separate predicate `Model.Standing`. -/
structure Model (I : Type) where
  /-- the generator `(q_ij)` of the world chain `A` -/
  Q : I → I → ℝ
  /-- the demand rate `λ_i` in world state `i` -/
  lam : I → ℝ
  /-- the uniformization rate `μ` -/
  μ : ℝ
  /-- the discount rate `α` -/
  α : ℝ
  /-- the lead-time law `F_L` -/
  leadLaw : Measure ℝ
  /-- the actual unit order cost `c̄` -/
  cbar : ℝ
  /-- the actual fixed order cost `K̄` -/
  Kbar : ℝ
  /-- the holding cost rate `h` -/
  h : ℝ
  /-- the penalty (backorder) cost rate `p` -/
  p : ℝ

namespace Model

variable {I : Type} (M : Model I)

/-- `q_i = −q_ii` (p. 353). -/
def q (i : I) : ℝ := -M.Q i i

/-- `q* = sup_i q_i` (p. 353). Finite under `Standing` (`q_bdd`). -/
noncomputable def qStar : ℝ := ⨆ i, M.q i

/-- `λ* = sup_i λ_i` (p. 353). Finite under `Standing` (`lam_bdd`). -/
noncomputable def lamStar : ℝ := ⨆ i, M.lam i

/-- **Standing hypotheses** (§1, p. 353; §2, pp. 354–355), together with the implicit ones the paper
uses without printing them.

* `Q` is a conservative generator: `q_ij ≥ 0` for `j ≠ i` and `q_i = −q_ii = Σ_{j≠i} q_ij`;
* `λ_i ≥ 0`; `q* = sup_i q_i` and `λ* = sup_i λ_i` are finite (p. 353);
* `μ > 0` and `μ ≥ q* + λ*` (p. 354);
* `α > 0`;
* `F_L` is a probability law on `[0, ∞)` (the lead time is a finite nonnegative random variable);
* `c̄ ≥ 0`, `K̄ ≥ 0`, `h > 0`, `p > 0`.

**Formalization Note.** `α > 0`, `μ > 0`, `h > 0`, `p > 0`, `c̄, K̄ ≥ 0` are not printed but are
needed (Lemma 2 (3) fails at `h = 0` or `p = 0`). The independence of `L` from the world and the
demand is built into the definition of `discDemandMass` (display (16), p. 361). Assumption 1
(`α c̄ < p`) is not part of `Standing`; it is the separate predicate `Assumption1`. -/
structure Standing : Prop where
  offdiag_nonneg : ∀ i j, i ≠ j → 0 ≤ M.Q i j
  conservative : ∀ i, HasSum (fun j : {j : I // j ≠ i} => M.Q i j) (M.q i)
  lam_nonneg : ∀ i, 0 ≤ M.lam i
  q_bdd : BddAbove (Set.range M.q)
  lam_bdd : BddAbove (Set.range M.lam)
  μ_pos : 0 < M.μ
  μ_ge : M.qStar + M.lamStar ≤ M.μ
  α_pos : 0 < M.α
  lead_prob : IsProbabilityMeasure M.leadLaw
  lead_nonneg : M.leadLaw (Set.Iio 0) = 0
  cbar_nonneg : 0 ≤ M.cbar
  Kbar_nonneg : 0 ≤ M.Kbar
  h_pos : 0 < M.h
  p_pos : 0 < M.p

/-- **Assumption 1** (p. 356): `α c̄ < p`. -/
def Assumption1 : Prop := M.α * M.cbar < M.p

/-- `F̃_L(α) = E[e^{−αL}]`, the Laplace transform of the lead time at `α` (p. 353–354). -/
noncomputable def Ftilde : ℝ := ∫ l, Real.exp (-M.α * l) ∂M.leadLaw

/-- `c = E[e^{−αL} c̄] = c̄ F̃_L(α)` (p. 354). -/
noncomputable def c : ℝ := M.cbar * M.Ftilde

/-- `K = E[e^{−αL} K̄] = K̄ F̃_L(α)` (p. 354). -/
noncomputable def K : ℝ := M.Kbar * M.Ftilde

/-- `β = 1/(μ + α)` (p. 355). -/
noncomputable def β : ℝ := 1 / (M.μ + M.α)

/-- `γ = βμ` (p. 355). -/
noncomputable def γ : ℝ := M.β * M.μ

/-- `Ĉ(x) = −px` if `x < 0`, `hx` otherwise (p. 354). -/
noncomputable def Chat (x : ℝ) : ℝ := if x < 0 then -M.p * x else M.h * x

/-- `demandStep n i d`: the probability that the uniformized jump chain of the world-and-demand
process, started in world state `i` with zero demand, has counted exactly `d` demands after `n` jumps.
One jump from world state `i` is a demand (probability `λ_i/μ`), a move of the world to `j ≠ i`
(probability `q_ij/μ`) or nothing (probability `1 − (λ_i + q_i)/μ`) (§2, p. 355). The recursion
conditions on the first jump. -/
noncomputable def demandStep : ℕ → I → ℕ → ℝ
  | 0, _, d => if d = 0 then 1 else 0
  | n + 1, i, d =>
      M.lam i / M.μ * (if d = 0 then 0 else demandStep n i (d - 1))
      + ∑' j : {j : I // j ≠ i}, M.Q i j / M.μ * demandStep n j d
      + (1 - (M.lam i + M.q i) / M.μ) * demandStep n i d

/-- `f_i(d | l)`, the probability that the demand `D(l)` in `(0, l]` equals `d`, given `A(0) = i`
(§5, p. 361, below (16)). Defined by uniformization at rate `μ`:
`f_i(d | l) = Σ_n e^{−μl} (μl)^n / n! · demandStep n i d`.

**Formalization Note.** The paper never constructs the Markov-modulated Poisson demand process.
Uniformization (§2, p. 354) is the standard exact representation of such a process with bounded
rates; this is a definition, not a theorem of the paper. -/
noncomputable def demandMass (i : I) (d : ℕ) (l : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-M.μ * l) * (M.μ * l) ^ n / (n.factorial : ℝ) * M.demandStep n i d

/-- `g_i(d | α) = E[e^{−αL} f_i(d | L)]` (display (16), p. 361), with `L ~ F_L` independent of the
world and the demand. -/
noncomputable def discDemandMass (i : I) (d : ℕ) : ℝ :=
  ∫ l, Real.exp (-M.α * l) * M.demandMass i d l ∂M.leadLaw

/-- The law of the lead-time demand `D^i_L` (p. 353): `P(D^i_L = d) = E[f_i(d | L)]`. -/
noncomputable def leadDemandMass (i : I) (d : ℕ) : ℝ :=
  ∫ l, M.demandMass i d l ∂M.leadLaw

/-- `C(i, y) = E[e^{−αL} Ĉ(y − D^i_L)] = Σ_d g_i(d | α) Ĉ(y − d)` (§2, p. 354; (16), p. 361). -/
noncomputable def costC (i : I) (y : ℤ) : ℝ :=
  ∑' d : ℕ, M.discDemandMass i d * M.Chat ((y : ℝ) - (d : ℝ))

/-- The myopic cost function `G⁺(i, y) = (1 − γ) c y + β C(i, y)` (p. 355). -/
noncomputable def Gplus (i : I) (y : ℤ) : ℝ :=
  (1 - M.γ) * M.c * (y : ℝ) + M.β * M.costC i y

end Model

/-- `δ(z) = 0` if `z = 0`, `1` if `z > 0` (p. 354); only used at `z ≥ 0`. -/
def δ (z : ℤ) : ℝ := if z = 0 then 0 else 1

/-- The difference operator in the second variable, `Δf(i, x) = f(i, x + 1) − f(i, x)` (p. 354). -/
def Δ {I : Type} (f : I → ℤ → ℝ) (i : I) (x : ℤ) : ℝ := f i (x + 1) - f i x

/-- `y` is **the smallest value that minimizes** `f` (pp. 356–358): `y` minimizes `f` over `ℤ` and
no smaller integer does. -/
def IsSmallestMinimizer (f : ℤ → ℝ) (y : ℤ) : Prop :=
  IsLeast {y : ℤ | ∀ z, f y ≤ f z} y

end SongZipkinFluct.Monotone


