-- Prove2me | Definitions.Def_SustainableFashion_Variety_Setting
-- name    : SustainableFashion_Variety_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:53.473557+00:00
-- url     : https://prove2.me/theorems/34bdb362-62bb-4377-b28a-8ce5d82db5fe
-- title:
--   §3.1–§3.2, pp. 8–11 — parameters, expected profit (1), feasibility, optimal solutions, m_E, nearest-style distance on the circle
-- statement:
--   This file sets up the fast-fashion model of Long and Nasiry.
--
--   **Parameters.** A parameter vector $P=(a,\theta,\gamma,\beta,k,k',\bar n)$ collects the consumers' base value $a$, their sensitivity $\theta$ to quality and $\gamma$ to fashion, the design cost $\beta$ per style, the pre-season unit production cost $\tfrac k2u^2$ and the in-season (quick-response) unit cost $\tfrac{k'}2u^2$ of a product of quality $u$, and the upper end $\bar n$ of the market size $n\sim U(0,\bar n)$. The parameters are **admissible** when
--   $$0<k<k',\qquad \theta>0,\qquad \gamma>0,\qquad \beta>0,\qquad \bar n>0;$$
--   $a\in\mathbb R$ is unrestricted.
--
--   **Expected profit.** For $m$ styles, quality $u$ and pre-season inventory $q$ per style, the firm's expected profit is problem (1) of the paper,
--   $$\mathbb E\Pi(m,u,q)=\Big(a+\theta u+\frac\gamma2-\frac{\gamma}{4m}\Big)\frac{\bar n}{2}-m\frac k2u^2q-\frac{k'}{2}u^2\frac{(\bar n-q)^2}{2\bar n}-\beta m .$$
--   A decision is **feasible** when $m\ge 1$ (a real number), $u\ge 0$ and $0\le q\le\bar n$. A feasible $(m,u,q)$ is **optimal** when no feasible decision has a larger expected profit. For a given $m$, a pair $(u,q)$ with $u\ge0$, $0\le q\le\bar n$ is **optimal given $m$** when it maximises $\mathbb E\Pi(m,\cdot,\cdot)$ over such pairs.
--
--   **The root $m_E$.** $m_E(P)$ is the smallest root on $[1,k'/k]$ of
--   $$-\frac{\theta^2k'(k'-km)}{2km^2(2k'-km)^2}+\frac{\gamma}{8m^2}-\frac{\beta}{\bar n}=0$$
--   (Proposition 3(iii)).
--
--   **Styles on a circle.** Styles and the fashion trend live on a circle of unit circumference (Salop's circular city). For $m\ge1$ style locations $t_1,\dots,t_m$ and a trend location $x$, $|t^*-x|$ denotes the shortest arc distance from $x$ to the nearest style, and $\mathbb E|t^*-x|$ its expectation when $x$ is uniform on the circle. The equally spaced configuration places style $i$ at $i/m$, $i=0,\dots,m-1$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The circle is Mathlib's `AddCircle (1 : ℝ)`: its distance is the arc distance and its Haar measure `volume` has total mass $1$, so the integral over it is the expectation under the uniform trend. The nearest distance is a minimum over the nonempty finite index set `Fin m` (`[NeZero m]`). `mE` is a real infimum: it equals the smallest root whenever a root exists (the root set is closed and contained in $[1,k'/k]$) and is $0$ when there is none; it is used only where the paper asserts the root is the optimum. The number of styles $m$ is a real number in problem (1), as in the paper's analysis of §4.2 (e.g. $m^*=\sqrt{\bar n\gamma/(8\beta)}$).
-- source:
--   Long & Nasiry, Sustainability in the Fast Fashion Industry, SSRN 3486502 author's manuscript (2021; MSOM doi:10.1287/msom.2021.1054), §3.1 (pp. 8–9), §3.2 problem (1) (pp. 10–11), Proposition 3(iii) (p. 15)

import Mathlib

namespace SustainableFashion.Variety

/-- The primitive data of the model of Long & Nasiry, §3.1 (pp. 8–9): base value `a`, quality
sensitivity `θ`, fashion sensitivity `γ`, design cost per style `β`, pre-season unit-cost
coefficient `k` (unit cost `(k/2) u²`), quick-response unit-cost coefficient `k'`
(unit cost `(k'/2) u²`), and the upper end `nbar` of the market size `n ∼ U(0, nbar)`. -/
structure Params where
  a : ℝ
  θ : ℝ
  γ : ℝ
  β : ℝ
  k : ℝ
  k' : ℝ
  nbar : ℝ

/-- Admissible parameters: `0 < k < k'` (p. 9, "k′ > k"), `θ > 0`, `n̄ > 0` (`n ∼ U(0, n̄)`), and
`β > 0`, `γ > 0` (the case of Table 1 and Proposition 4, p. 16). The base value `a` is free. -/
def Params.Admissible (P : Params) : Prop :=
  0 < P.k ∧ P.k < P.k' ∧ 0 < P.θ ∧ 0 < P.γ ∧ 0 < P.β ∧ 0 < P.nbar

/-- The firm's expected profit, problem (1) (p. 11), for `m` styles, quality `u` and
inventory `q` per style:
`(a + θu + γ/2 − γ/(4m)) n̄/2 − m (k/2) u² q − (k'/2) u² (n̄ − q)²/(2n̄) − βm`. -/
noncomputable def expProfit (P : Params) (m u q : ℝ) : ℝ :=
  (P.a + P.θ * u + P.γ / 2 - P.γ / (4 * m)) * (P.nbar / 2) - m * (P.k / 2) * u ^ 2 * q
    - (P.k' / 2) * u ^ 2 * ((P.nbar - q) ^ 2 / (2 * P.nbar)) - P.β * m

/-- Feasible decisions of problem (1): a real number of styles `m ≥ 1`, quality `u ≥ 0`, and
inventory per style `0 ≤ q ≤ n̄`. -/
def Feasible (P : Params) (m u q : ℝ) : Prop :=
  1 ≤ m ∧ 0 ≤ u ∧ 0 ≤ q ∧ q ≤ P.nbar

/-- `(m, u, q)` is an optimal solution of problem (1): feasible, and no feasible decision has a
larger expected profit. -/
def IsOptimal (P : Params) (m u q : ℝ) : Prop :=
  Feasible P m u q ∧ ∀ m' u' q', Feasible P m' u' q' → expProfit P m' u' q' ≤ expProfit P m u q

/-- For a given number of styles `m`, `(u, q)` maximises the expected profit (1) over quality
`u ≥ 0` and inventory `0 ≤ q ≤ n̄` (Proposition 2, "Suppose m is given"). -/
def IsOptimalGiven (P : Params) (m u q : ℝ) : Prop :=
  (0 ≤ u ∧ 0 ≤ q ∧ q ≤ P.nbar) ∧
    ∀ u' q', 0 ≤ u' → 0 ≤ q' → q' ≤ P.nbar → expProfit P m u' q' ≤ expProfit P m u q

/-- `m_E` of Proposition 3(iii) (p. 15): the smallest root on `[1, k'/k]` of
`−θ² k' (k' − k m) / (2 k m² (2k' − k m)²) + γ/(8m²) − β/n̄ = 0`
(the infimum of the set of roots; this set is closed, so the infimum is a root whenever one
exists; it is `0` when there is no root). -/
noncomputable def mE (P : Params) : ℝ :=
  sInf {m : ℝ | m ∈ Set.Icc 1 (P.k' / P.k) ∧
    -(P.θ ^ 2 * P.k' * (P.k' - P.k * m)) / (2 * P.k * m ^ 2 * (2 * P.k' - P.k * m) ^ 2)
      + P.γ / (8 * m ^ 2) - P.β / P.nbar = 0}

/-- The circle of unit circumference on which styles and the fashion trend are located (§3.1,
p. 8). Its distance is the shortest arc distance and its `volume` is the uniform probability
measure. -/
abbrev Circle := AddCircle (1 : ℝ)

/-- For `m ≥ 1` style locations `t₁, …, t_m` on the circle and a trend location `x`, the arc
distance `|t* − x|` from `x` to the nearest style. -/
noncomputable def nearestDist {m : ℕ} [NeZero m] (t : Fin m → Circle) (x : Circle) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => dist (t i) x)

/-- The expected nearest-style distance `E|t* − x|` when the trend `x` is uniform on the circle. -/
noncomputable def expNearestDist {m : ℕ} [NeZero m] (t : Fin m → Circle) : ℝ :=
  ∫ x, nearestDist t x

/-- `m` styles at equal distances `1/m` from each other: `t_i = i/m`, `i = 0, …, m − 1`. -/
noncomputable def equalSpacing (m : ℕ) : Fin m → Circle :=
  fun i => (((i : ℕ) : ℝ) / m : ℝ)

end SustainableFashion.Variety


