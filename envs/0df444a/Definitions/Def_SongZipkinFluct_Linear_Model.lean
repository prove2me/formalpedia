-- Prove2me | Definitions.Def_SongZipkinFluct_Linear_Model
-- name    : SongZipkinFluct_Linear_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:20.886075+00:00
-- url     : https://prove2.me/theorems/9a98d11f-e652-417d-8b26-70f186790984
-- title:
--   §1–§2 — the fluctuating-demand model: lead-time demand law, discounted cost rate C(i, y), myopic cost G⁺(i, y), integer convexity
-- statement:
--   This file fixes the model of Song and Zipkin (§1–§2, pp. 353–355, and display (16), p. 361) and the cost functions every later statement uses.
--
--   **Data and standing assumptions.**
--
--   1. The **world** $A=\{A(t):t\ge0\}$ is a continuous-time Markov chain on a countable, nonempty state space $\mathbf I$ with generator $Q=(q_{ij})$: $q_{ij}\ge0$ for $j\ne i$, the off-diagonal rates out of each $i$ are summable, and $q_i=-q_{ii}=\sum_{j\ne i}q_{ij}$.
--   2. When $A=i$, unit demands arrive at rate $\lambda_i\ge0$. Both $q^*=\sup_i q_i$ and $\lambda^*=\sup_i\lambda_i$ are finite.
--   3. The **uniformization rate** $\mu>0$ satisfies $\mu\ge q^*+\lambda^*$; the **discount rate** is $\alpha>0$.
--   4. The **lead time** $L$ has a law $F_L$ on $[0,\infty)$ and is independent of the world and of demand. Only its marginal law enters; lead times of successive orders need not be independent.
--   5. The actual unit and fixed order costs are $\bar c\ge0$ and $\bar K\ge0$; the holding and penalty cost rates are $h>0$ and $p>0$.
--
--   **Assumption 1** (p. 356) is the separate condition $\alpha\bar c<p$; it is not part of the model.
--
--   **Derived quantities.** With $\tilde F_L(\alpha)=E[e^{-\alpha L}]$, the discounted order costs are $c=\bar c\tilde F_L(\alpha)$ and $K=\bar K\tilde F_L(\alpha)$, the order indicator is $\delta(0)=0$ and $\delta(z)=1$ for $z>0$, and $\beta=1/(\mu+\alpha)$, $\gamma=\beta\mu$. The inventory cost rate is $\hat C(x)=-px$ for $x<0$ and $\hat C(x)=hx$ otherwise.
--
--   **Lead-time demand.** Let $u_n(i,d)$ be the probability that the uniformized chain on $\mathbf I\times\mathbb N$, started at $(i,0)$, has counted $d$ demands after $n$ steps, where one step moves $(i,d)$ to $(i,d+1)$ with probability $\lambda_i/\mu$, to $(j,d)$ with probability $q_{ij}/\mu$ ($j\ne i$), and stays with probability $1-(\lambda_i+q_i)/\mu$. The mass function of the demand $D(l)$ in $(0,l]$ given $A(0)=i$ and its discounted mixture over $L$ are
--
--   $$f_i(d\mid l)=\sum_{n\ge0}e^{-\mu l}\frac{(\mu l)^n}{n!}\,u_n(i,d),\qquad g_i(d\mid\alpha)=E\big[e^{-\alpha L}f_i(d\mid L)\big].$$
--
--   **Cost functions.** The expected discounted inventory cost rate at the end of a lead time and the myopic cost are
--
--   $$C(i,y)=E\big[e^{-\alpha L}\hat C(y-D^i_L)\big]=\sum_{d\ge0}g_i(d\mid\alpha)\,\hat C(y-d),\qquad G^+(i,y)=(1-\gamma)cy+\beta C(i,y),$$
--
--   for a world state $i$ and an integer inventory position $y$.
--
--   **Vocabulary.** $\Delta f(i,x)=f(i,x+1)-f(i,x)$ is the forward difference in the integer variable; a function $f:\mathbb Z\to\mathbb R$ is (integer) convex when $\Delta f$ is nondecreasing; it is coercive when $f(y)\to+\infty$ as $y\to+\infty$ and as $y\to-\infty$; and $y$ is a smallest minimizer of $f$ when it is the least integer at which $f$ attains its global minimum.
--
--   These are the cost data of the dynamic programs (1), (2) and (10) used throughout the paper.
--
--   **Formalization Note** The paper never constructs the Markov-modulated Poisson process; $f_i(d\mid l)$ is defined by uniformization at the model's rate $\mu$, the exact standard representation for bounded rates. The expectations defining $\tilde F_L(\alpha)$, $g_i$ and $C$ are a Bochner integral and series; they are finite under the standing assumptions (bounded integrands, $E[e^{-\alpha L}D^i_L]\le\lambda^*/(\alpha e)$), which is mathematics, not an extra hypothesis. The indicator $\delta$ is only applied to nonnegative order sizes. Smallest minimizers are stated through `IsLeast`, never through an integer infimum. The positivity of $h$, $p$, $\alpha$, $\mu$, the nonnegativity of $\bar c,\bar K$ and the independence of $L$ are implicit in the paper and stated here explicitly.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, pp. 353–355, §1–§2

import Mathlib

open scoped NNReal

namespace SongZipkinFluct.Linear

/-- Song--Zipkin, §1--§2, pp. 353--355. The world has countably many states.
The lead-time law is on nonnegative finite times; it is independent of the world and
demand processes. Only the marginal law `F_L` enters (p. 353--354, the Hadley--Whitin
approach); lead times of successive orders need not be independent. Positivity of the cost rates and discount rate is implicit in the
paper's coercivity and infinite-horizon arguments. -/
structure Model (I : Type*) [Countable I] [Nonempty I] [DecidableEq I] where
  Q : I → I → ℝ
  lam : I → ℝ
  μ : ℝ
  α : ℝ
  leadLaw : MeasureTheory.Measure ℝ≥0
  cbar : ℝ
  Kbar : ℝ
  h : ℝ
  p : ℝ
  Q_off_nonneg : ∀ i j, i ≠ j → 0 ≤ Q i j
  Q_conservative : ∀ i, Summable (fun j : {j : I // j ≠ i} => Q i j.1) ∧
    -Q i i = ∑' j : {j : I // j ≠ i}, Q i j.1
  lam_nonneg : ∀ i, 0 ≤ lam i
  q_bdd : BddAbove (Set.range (fun i => -Q i i))
  lam_bdd : BddAbove (Set.range lam)
  μ_pos : 0 < μ
  μ_bound : sSup (Set.range (fun i => -Q i i)) + sSup (Set.range lam) ≤ μ
  α_pos : 0 < α
  lead_prob : MeasureTheory.IsProbabilityMeasure leadLaw
  cbar_nonneg : 0 ≤ cbar
  Kbar_nonneg : 0 ≤ Kbar
  h_pos : 0 < h
  p_pos : 0 < p

variable {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]

/-- Assumption 1, p. 356. It is deliberately separate from `Model`. -/
def Model.Assumption1 (M : Model I) : Prop := M.α * M.cbar < M.p

/-- The Laplace transform of the lead-time law, §1 p. 354. -/
noncomputable def Model.leadTransform (M : Model I) : ℝ :=
  ∫ l : ℝ≥0, Real.exp (-M.α * (l : ℝ)) ∂M.leadLaw

/-- Discounted unit order cost, §1 p. 354. -/
noncomputable def Model.c (M : Model I) : ℝ := M.cbar * M.leadTransform

/-- Discounted fixed order cost, §1 p. 354. -/
noncomputable def Model.K (M : Model I) : ℝ := M.Kbar * M.leadTransform

/-- The order indicator of §1 p. 354, for feasible nonnegative order sizes. -/
def delta (z : ℤ) : ℝ := if z = 0 then 0 else 1

/-- The event-time discount coefficient, §2 p. 355. -/
noncomputable def Model.beta (M : Model I) : ℝ := 1 / (M.μ + M.α)

/-- The one-event discount factor, §2 p. 355. -/
noncomputable def Model.gamma (M : Model I) : ℝ := M.beta * M.μ

/-- Holding/backlog cost rate `Ĉ`, §1 p. 354. -/
def Model.inventoryRate (M : Model I) (x : ℤ) : ℝ :=
  if x < 0 then -M.p * (x : ℝ) else M.h * (x : ℝ)

/-- Probability of `d` demands in `n` steps of the uniformized chain, starting in
world state `i`; §2 p. 354 and §4.1 p. 359. The chain has demand, world-jump and
self-loop probabilities respectively `λᵢ/μ`, `qᵢⱼ/μ`, and `1-(λᵢ+qᵢ)/μ`. -/
noncomputable def Model.jumpDemandMass (M : Model I) : ℕ → I → ℕ → ℝ
  | 0, _, d => if d = 0 then 1 else 0
  | n + 1, i, d =>
      M.lam i / M.μ * (if d = 0 then 0 else M.jumpDemandMass n i (d - 1)) +
      (∑' j : {j : I // j ≠ i}, M.Q i j.1 / M.μ * M.jumpDemandMass n j.1 d) +
      (1 - (M.lam i + -M.Q i i) / M.μ) * M.jumpDemandMass n i d

/-- Probability of `d` demands during a fixed lead time `l`, via Poisson
uniformization, §1 p. 353 and §4.1 p. 359. -/
noncomputable def Model.demandMass (M : Model I) (i : I) (d : ℕ) (l : ℝ≥0) : ℝ :=
  ∑' n : ℕ, Real.exp (-(M.μ * (l : ℝ))) *
    (M.μ * (l : ℝ)) ^ n / (n.factorial : ℝ) * M.jumpDemandMass n i d

/-- `gᵢ(d|α)=E[e^{-αL} fᵢ(d|L)]`, display (16), p. 361.
Independence of `L` from world and demand is built into this mixture. -/
noncomputable def Model.discDemandMass (M : Model I) (i : I) (d : ℕ) : ℝ :=
  ∫ l : ℝ≥0, Real.exp (-M.α * (l : ℝ)) * M.demandMass i d l ∂M.leadLaw

/-- Expected discounted inventory cost rate `C(i,y)`, §2 p. 354 and (16) p. 361. -/
noncomputable def Model.C (M : Model I) (i : I) (y : ℤ) : ℝ :=
  ∑' d : ℕ, M.discDemandMass i d * M.inventoryRate (y - (d : ℤ))

/-- The myopic cost `G⁺(i,y)`, display (2), p. 355. -/
noncomputable def Model.Gplus (M : Model I) (i : I) (y : ℤ) : ℝ :=
  (1 - M.gamma) * M.c * (y : ℝ) + M.beta * M.C i y

/-- The integer forward difference `Δf(i,x)`, §1 p. 354. -/
def Delta (f : I → ℤ → ℝ) (i : I) (x : ℤ) : ℝ := f i (x + 1) - f i x

/-- Integer convexity is monotonicity of forward differences; Lemma 1 p. 355. -/
def IntConvex (f : ℤ → ℝ) : Prop :=
  ∀ y : ℤ, f (y + 1) - f y ≤ f (y + 2) - f (y + 1)

/-- Divergence at both ends of the integer line, Lemma 2 p. 355. -/
def CoerciveInt (f : ℤ → ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop Filter.atTop ∧
  Filter.Tendsto f Filter.atBot Filter.atTop

/-- A smallest global minimizer, as in p. 356. -/
def SmallestMinimizer (f : ℤ → ℝ) (y : ℤ) : Prop :=
  IsLeast {z : ℤ | ∀ w : ℤ, f z ≤ f w} y

end SongZipkinFluct.Linear


