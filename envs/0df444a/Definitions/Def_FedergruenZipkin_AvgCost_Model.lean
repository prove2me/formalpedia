-- Prove2me | Definitions.Def_FedergruenZipkin_AvgCost_Model
-- name    : FedergruenZipkin_AvgCost_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:18:44.482962+00:00
-- url     : https://prove2.me/theorems/45a60981-0f7d-473f-ad08-68046621591e
-- title:
--   The capacitated inventory model of §2 (Assumptions 1–4), policies, average cost, strong optimality, the operators R, S, S_L, Q, Q_L and the hitting sums H_ι
-- statement:
--   This file sets up the periodic-review inventory model of Federgruen and Zipkin (1986) with a limited production capacity and a finite storage capacity, together with every object used by the mission.
--
--   **Data and standing assumptions (§2).** One-period demands $D_0, D_1, \dots$ are independent copies of a random variable $D$ with values in $\{0,1,2,\dots\}$ and probability mass function $p(j) = \Pr\{D = j\}$. Write $\mu = E(D)$ and $P(j) = \Pr\{D \le j\}$. The production capacity is a positive integer $b$, and $G : \mathbb Z \to \mathbb R$ is the one-period expected cost as a function of the inventory level after ordering. The model assumes:
--
--   1. (Assumption 1) $G \ge 0$, $G$ is convex, and $G(y) \to \infty$ as $|y| \to \infty$;
--   2. (Assumption 2) the characteristic function $\theta \mapsto E e^{i\theta D}$ is analytic at the origin;
--   3. $0 < \mu$;
--   4. (Assumption 3) $G(y) \le A + B|y|^\rho$ for all $y$, for a positive integer $\rho$ and positive constants $A$, $B$;
--   5. (Assumption 4) $b > \mu$ and $P(b) < 1$.
--
--   **Dynamics and policies.** With inventory $x$ at the start of a period and storage capacity $U$, an order brings the inventory to $y \in Y(x) = \{y : x \le y \le x + b,\ y \le U\}$; then demand $D$ is subtracted, $x' = y - D$ (stockouts are backordered). A one-period policy $\delta$ is *feasible* if $\delta(x) \in Y(x)$ for every $x \le U$. It lies in $\Delta_L$ if moreover $\delta(x) = x + b$ for $x \le L$. A Markov policy is a sequence $\pi = (\pi_0, \pi_1, \dots)$ of feasible one-period policies. The *critical-number policy* with critical number $\bar y$ is
--   $$\delta[\bar y](x) = \max\bigl(x, \min(\bar y, x + b)\bigr):$$
--   it orders up to $\bar y$ when possible and to capacity otherwise, and it does not order when $x \ge \bar y$.
--
--   **Costs.** $E\{G(y_i) \mid x_0 = x, \pi\}$ is defined through the transition operator $P[\delta]w(x) = E\,w(\delta(x) - D)$, and the expected $t$-period cost is $E\{\sum_{i=0}^{t-1} G(y_i) \mid x_0 = x, \pi\}$, with values in $[0, \infty]$. A stationary policy $\delta$ is *strongly optimal with average cost $g$* if it is feasible, if
--   $$\lim_{t\to\infty} t^{-1} E\Bigl\{\sum_{i=0}^{t-1} G(y_i) \Bigm| x_0 = x, \delta\Bigr\} = g \quad\text{for every } x \le U,$$
--   and if every Markov policy $\pi$ satisfies $\liminf_{t\to\infty} t^{-1} E\{\sum_{i=0}^{t-1} G(y_i) \mid x_0 = x, \pi\} \ge g$ for every $x \le U$.
--
--   **Operators.** For a real function $v$ on the integers,
--   $$Rv(y) = G(y) + E\,v(y - D),\qquad Sv(x) = \min_{y \in Y(x)} Rv(y),\qquad S_L v(x) = \min_{y \in Y_L(x)} Rv(y),$$
--   where $Y_L(x) = \{x + b\}$ for $x \le L$ and $Y_L(x) = Y(x)$ otherwise; and $Qv(x) = Sv(x) - Sv(\bar y^\infty)$, $Q_L v(x) = S_L v(x) - S_L v(\bar y^\infty)$, where $\bar y^\infty$ is the smallest global minimizer of $G$. The optimality equation (6), $g + v(x) = Sv(x)$ for $x \le U$, is expressed with an explicitly attained minimum. A function $v$ lies in the class $V$ if $|v(x)| \le A + B|x|^{\rho+3}$ for $x \le U$, $v(x+1) \le v(x)$ for $x < \bar y^\infty$, and $v$ is convex on $x \le U$.
--
--   **Hitting sums (§3).** For an interval $\iota = [l, u]$ let $\Delta_\iota$ be the feasible policies with $\delta(x) = x + b$ for $x \le l$ and $\delta(x) = x$ for $u \le x \le U$. With $T(\iota)$ the first period $t \ge 1$ with $x_t \in \iota$, and $v \ge 0$,
--   $$H_\iota v(x) = \sup_{\delta \in \Delta_\iota} E\Bigl\{\sum_{t=0}^{T(\iota)-1} v(y_t) \Bigm| x_0 = x, \delta\Bigr\}.$$
--   The composite operator $P[\sigma_0]P[\sigma_1]\cdots P[\sigma_n]$ of a finite sequence of policies is also defined.
--
--   These are the objects of the paper's Lemmas 3–5, Corollaries 1–2 and Theorem 1.
--
--   **Formalization Note** The per-unit order cost $c$ is omitted: the paper sets $c = 0$ without loss of generality (p. 195), after which its strengthened condition $\lim_{y\to-\infty}[cy + G(y)] = \infty$ is Assumption 1(a). Convexity on the integers is the second-difference inequality, and "$|y| \to \infty$" is the cofinite filter on $\mathbb Z$. The storage capacity $U$ and $\bar y^\infty$ are explicit parameters of every statement, not fields. Expected policy costs and the hitting sums are $[0,\infty]$-valued, so no summability side condition is needed for them; $H_\iota$ is defined for nonnegative functions only (the paper applies it to $v1$, $G$ and $|v|$), and its maximum is a supremum. $Sv(x)$ is a real infimum over the finite nonempty set $Y(x)$ and is only used for $x \le U$. Policies are deterministic; Markov policies are memoryless and possibly nonstationary, as in the paper.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, pp. 195-198, §2 (Assumptions 1-4, the operators R, S, S_L, Q, Q_L), p. 197-198 (Δ_ι, T(ι), H_ι), p. 200 (P[δ]), p. 202 (the class V), p. 203 eq. (7) (strong optimality)

import Mathlib

namespace FedergruenZipkin.AvgCost

open scoped ENNReal
open Filter Topology

/-- The capacitated periodic-review inventory model of Federgruen and Zipkin (1986), §2,
pp. 195–196, with its standing Assumptions 1–4. The per-unit order cost `c` is absent: the paper
sets `c = 0` without loss of generality (p. 195). The storage capacity `U` is not a field; it is an
explicit parameter of every definition and theorem. -/
structure Model where
  /-- `p j = Pr{D = j}`, the probability mass function of the one-period demand `D` -/
  p : ℕ → ℝ
  p_nonneg : ∀ j, 0 ≤ p j
  p_sum : HasSum p 1
  /-- Assumption 2: the characteristic function `θ ↦ E e^{iθD}` is analytic at the origin -/
  charfun_analytic : AnalyticAt ℝ
    (fun θ : ℝ => ∑' j : ℕ, ((p j : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ) * (j : ℂ))) 0
  /-- `0 < μ = E(D)` (p. 195) -/
  mean_pos : 0 < ∑' j : ℕ, (j : ℝ) * p j
  /-- `b`, the production capacity (limit on order size), a positive integer -/
  b : ℕ
  b_pos : 0 < b
  /-- Assumption 4(a): `b > μ` -/
  mean_lt_b : ∑' j : ℕ, (j : ℝ) * p j < b
  /-- Assumption 4(b): `P(b) = Pr{D ≤ b} < 1` -/
  cdf_b_lt_one : ∑ j ∈ Finset.range (b + 1), p j < 1
  /-- `G(y)`, the one-period expected cost at inventory level `y` after ordering -/
  G : ℤ → ℝ
  /-- Assumption 1(b): `G` is nonnegative -/
  G_nonneg : ∀ y, 0 ≤ G y
  /-- Assumption 1(b): `G` is convex (second differences are nonnegative) -/
  G_convex : ∀ y, G y - G (y - 1) ≤ G (y + 1) - G y
  /-- Assumption 1(a): `G(y) → ∞` as `|y| → ∞` -/
  G_coercive : Tendsto G cofinite atTop
  /-- Assumption 3: the growth exponent `ρ`, a positive integer -/
  ρ : ℕ
  ρ_pos : 0 < ρ
  /-- Assumption 3: `G(y) ≤ A + B |y|^ρ` for positive constants `A`, `B` -/
  G_growth : ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ y, G y ≤ A + B * |(y : ℝ)| ^ ρ

/-- Discrete convexity of `v` on the states `x ≤ U`. -/
def ConvexBelow (U : ℤ) (v : ℤ → ℝ) : Prop :=
  ∀ x : ℤ, x + 1 ≤ U → v x - v (x - 1) ≤ v (x + 1) - v x

/-- A one-period policy `δ` is feasible: `δ(x) ∈ Y(x) = {y : x ≤ y ≤ x + b, y ≤ U}` for every
state `x ≤ U` (values above `U` are irrelevant). -/
def Feasible (M : Model) (U : ℤ) (δ : ℤ → ℤ) : Prop :=
  ∀ x ≤ U, x ≤ δ x ∧ δ x ≤ x + M.b ∧ δ x ≤ U

/-- `δ ∈ Δ_L`: `δ` is feasible for the restricted action sets `Y_L(x)`, so it orders to capacity
(`δ(x) = x + b`) whenever `x ≤ L`. -/
def FeasibleL (M : Model) (U L : ℤ) (δ : ℤ → ℤ) : Prop :=
  Feasible M U δ ∧ ∀ x ≤ L, δ x = x + M.b

/-- The critical-number policy `δ[ȳ]` with critical number `ȳ`: order up to `ȳ` when possible,
otherwise order to capacity `b`; never order when `x ≥ ȳ`. -/
def critNum (M : Model) (ybar : ℤ) : ℤ → ℤ :=
  fun x => max x (min ybar (x + M.b))

/-- The transition operator `P[δ]w(x) = E w(δ(x) − D)` on nonnegative extended functions. -/
noncomputable def P (M : Model) (δ : ℤ → ℤ) (w : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (M.p j) * w (δ x - j)

/-- `periodCost M π i x = E{G(y_i) | x_0 = x, π}` for a Markov policy `π = (π 0, π 1, …)`, where
`y_t = π t (x_t)` and `x_{t+1} = y_t − D_t`. -/
noncomputable def periodCost (M : Model) : (ℕ → ℤ → ℤ) → ℕ → ℤ → ℝ≥0∞
  | π, 0, x => ENNReal.ofReal (M.G (π 0 x))
  | π, i + 1, x => P M (π 0) (periodCost M (fun t => π (t + 1)) i) x

/-- `totalCost M π t x = E{∑_{i=0}^{t-1} G(y_i) | x_0 = x, π}`. -/
noncomputable def totalCost (M : Model) (π : ℕ → ℤ → ℤ) (t : ℕ) (x : ℤ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range t, periodCost M π i x

/-- The stationary policy `δ` is strongly (average-cost) optimal with average cost `g`: it is
feasible, its average cost converges to `g` from every initial state `x ≤ U`, and every feasible
Markov policy has, from every initial state `x ≤ U`, a lim-inf average cost at least `g`. -/
def StronglyOptimal (M : Model) (U : ℤ) (δ : ℤ → ℤ) (g : ℝ) : Prop :=
  Feasible M U δ ∧
  (∀ x ≤ U, Tendsto (fun t : ℕ => totalCost M (fun _ => δ) t x / (t : ℝ≥0∞)) atTop
      (𝓝 (ENNReal.ofReal g))) ∧
  ∀ π : ℕ → ℤ → ℤ, (∀ t, Feasible M U (π t)) → ∀ x ≤ U,
    ENNReal.ofReal g ≤ liminf (fun t : ℕ => totalCost M π t x / (t : ℝ≥0∞)) atTop

/-- The operator `Rv(y) = G(y) + E v(y − D)`. -/
noncomputable def R (M : Model) (v : ℤ → ℝ) (y : ℤ) : ℝ :=
  M.G y + ∑' j : ℕ, M.p j * v (y - j)

/-- The value-iteration operator `Sv(x) = inf{Rv(y) : y ∈ Y(x)}`, meaningful for `x ≤ U`, where
`Y(x)` is finite and nonempty. -/
noncomputable def S (M : Model) (U : ℤ) (v : ℤ → ℝ) (x : ℤ) : ℝ :=
  ⨅ y : {y : ℤ // x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U}, R M v y

/-- The restricted value-iteration operator `S_L v(x) = inf{Rv(y) : y ∈ Y_L(x)}`. -/
noncomputable def SL (M : Model) (U L : ℤ) (v : ℤ → ℝ) (x : ℤ) : ℝ :=
  if x ≤ L then R M v (x + M.b) else S M U v x

/-- The reduced operator `Qv(x) = Sv(x) − Sv(ȳ^∞)`. -/
noncomputable def Q (M : Model) (U yInf : ℤ) (v : ℤ → ℝ) (x : ℤ) : ℝ :=
  S M U v x - S M U v yInf

/-- The reduced restricted operator `Q_L v(x) = S_L v(x) − S_L v(ȳ^∞)`. -/
noncomputable def QL (M : Model) (U L yInf : ℤ) (v : ℤ → ℝ) (x : ℤ) : ℝ :=
  SL M U L v x - SL M U L v yInf

/-- The optimality equation (6), `g + v(x) = min{Rv(y) : y ∈ Y(x)}` for every `x ≤ U`, stated
with explicit attainment of the minimum. -/
def OptEq (M : Model) (U : ℤ) (g : ℝ) (v : ℤ → ℝ) : Prop :=
  ∀ x ≤ U, (∀ y, x ≤ y → y ≤ x + M.b → y ≤ U → g + v x ≤ R M v y) ∧
    ∃ y, x ≤ y ∧ y ≤ x + M.b ∧ y ≤ U ∧ g + v x = R M v y

/-- `δ ∈ Δ_ι` for `ι = [l, u]`: `δ` is feasible, orders to capacity for `x ≤ l`, and does not
order for `u ≤ x ≤ U`. -/
def DeltaIota (M : Model) (U l u : ℤ) (δ : ℤ → ℤ) : Prop :=
  Feasible M U δ ∧ (∀ x ≤ l, δ x = x + M.b) ∧ ∀ x, u ≤ x → x ≤ U → δ x = x

/-- The taboo transition operator of `δ`, which kills every path that enters `ι`. -/
noncomputable def tabooP (M : Model) (δ : ℤ → ℤ) (ι : Set ℤ) (w : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (M.p j) * Set.indicator ιᶜ w (δ x - j)

/-- `hitSum M δ ι v x = E{∑_{t=0}^{T(ι)-1} v(y_t) | x_0 = x, δ}`, where `T(ι)` is the first
period `t ≥ 1` with `x_t ∈ ι`: the `t`-th term is `E{v(y_t); T(ι) > t}`. -/
noncomputable def hitSum (M : Model) (δ : ℤ → ℤ) (ι : Set ℤ) (v : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ∑' t : ℕ, (tabooP M δ ι)^[t] (fun z => v (δ z)) x

/-- `H_ι v(x) = sup_{δ ∈ Δ_ι} E{∑_{t=0}^{T(ι)-1} v(y_t) | x_0 = x, δ}` for `ι = [l, u]` and a
nonnegative function `v`. -/
noncomputable def H (M : Model) (U l u : ℤ) (v : ℤ → ℝ≥0∞) (x : ℤ) : ℝ≥0∞ :=
  ⨆ δ : ℤ → ℤ, ⨆ (_ : DeltaIota M U l u δ), hitSum M δ (Set.Icc l u) v x

/-- The composite operator `P[σ 0] P[σ 1] ⋯ P[σ n]` of a finite sequence of one-period policies. -/
noncomputable def Pcomp (M : Model) : (ℕ → ℤ → ℤ) → ℕ → (ℤ → ℝ≥0∞) → ℤ → ℝ≥0∞
  | σ, 0, w => P M (σ 0) w
  | σ, n + 1, w => P M (σ 0) (Pcomp M (fun s => σ (s + 1)) n w)

/-- `v ∈ V`: `v ∈ V_{ρ+3}` (growth `O(|x|^{ρ+3})` on `x ≤ U`), `v` is nonincreasing below
`ȳ^∞` (`v(x+1) ≤ v(x)` for `x < ȳ^∞`), and `v` is convex on `x ≤ U`. -/
def InV (M : Model) (U yInf : ℤ) (v : ℤ → ℝ) : Prop :=
  (∃ A B : ℝ, ∀ x ≤ U, |v x| ≤ A + B * |(x : ℝ)| ^ (M.ρ + 3)) ∧
  (∀ x, x < yInf → v (x + 1) ≤ v x) ∧ ConvexBelow U v

end FedergruenZipkin.AvgCost


