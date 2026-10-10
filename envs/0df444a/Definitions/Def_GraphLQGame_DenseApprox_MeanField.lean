-- Prove2me | Definitions.Def_GraphLQGame_DenseApprox_MeanField
-- name    : GraphLQGame_DenseApprox_MeanField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:24:53.760126+00:00
-- url     : https://prove2.me/theorems/309cac9e-6b05-4df0-b1ed-26a2efc7bc55
-- title:
--   The mean-field control $\alpha^{\mathrm{MF}}$ (7.4), its profile, the deviation bounds $\epsilon^G_v$ and $\epsilon_G$ of Theorem 2.11, control energy and own-state cost
-- statement:
--   Fix $T,\sigma,c>0$ and a finite simple graph $G$ on $V=\{1,\dots,n\}$.
--
--   1. The **mean-field control** (7.4) is
--   $$\alpha^{\mathrm{MF}}(t,y)=\frac{-cy}{1+c(T-t)},\qquad t\in[0,T],\ y\in\mathbb R,$$
--   and the **mean-field profile** gives player $v$ the control $\alpha^{\mathrm{MF}}_v(t,x)=\alpha^{\mathrm{MF}}(t,x_v)$, which depends only on the player's own state.
--   2. The **deviation bounds** of Theorem 2.11 are
--   $$\epsilon^G_v=\begin{cases}\sigma^2\frac{cT}{1+cT}\sqrt{\frac{cT(2+cT)}{\deg_G(v)}}&\deg_G(v)\ge1,\\0&\deg_G(v)=0,\end{cases}\qquad \epsilon_G=\sigma^2\frac{cT}{1+cT}\sqrt{\frac{cT(2+cT)}{1\vee\delta(G)}},$$
--   where $\delta(G)=\min_v\deg_G(v)$ is the minimal degree and $a\vee b=\max\{a,b\}$.
--   3. For a solution $\boldsymbol X$ of the state equation for a profile $\boldsymbol\alpha$, the **control energy** of player $i$ is $\mathbb E\int_0^T|\alpha_i(t,\boldsymbol X(t))|^2dt$ and its **own-state cost** is $\frac12\mathbb E\big[\int_0^T|\alpha_i(t,\boldsymbol X(t))|^2dt+c|X_i(T)|^2\big]$.
--
--   The energy and the own-state cost are the quantities $\mathbb E\int_0^T|\beta(t,\boldsymbol Y(t))|^2dt$ and $\frac12\mathbb E[\int_0^T|\beta(t,\boldsymbol Y(t))|^2dt+c|Y_v(T)|^2]$ of the three-step proof of Theorem 2.11 (§7.2, p. 41).
--
--   **Formalization Note** Vertices are `Fin n`: the paper's $\{1,\dots,n\}$ become $\{0,\dots,n-1\}$. Outside $[0,T]$ the formula for $\alpha^{\mathrm{MF}}$ is evaluated with Lean's total division, a value no statement uses. The degree is cast to a real number before dividing. Mathlib's minimal degree is $0$ on the empty graph ($n=0$), where $1\vee\delta(G)=1$ and every statement about players is vacuous. Energy and own-state cost are $[0,\infty]$-valued lower Lebesgue integrals.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), Theorem 2.11, p. 10 (α^MF_v, ε^G, ε_G, footnote 2); (7.4), p. 39; §7.2, p. 41 (Steps (1)–(3))

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GraphLQGame_Equilibrium_Game

open MeasureTheory
open scoped ENNReal NNReal

namespace GraphLQGame.DenseApprox

open EthierKurtz

/-- The mean-field control (7.4) (Lacker–Soret, arXiv:2005.14102v2, Lemma 7.2, p. 39; also
Theorem 2.11, p. 10): `α^MF(t, y) = −c y / (1 + c (T − t))`, for `t ∈ [0, T]` and `y ∈ ℝ`.

Formalization Note: time is real. For `t ∈ [0, T]` and `c > 0` the denominator is at least `1`;
outside `[0, T]` the formula is evaluated with Lean's total division (`x / 0 = 0`), a value that
no statement uses, since admissibility and costs only look at `t ∈ [0, T]`. -/
noncomputable def alphaMF (c T t y : ℝ) : ℝ :=
  -(c * y) / (1 + c * (T - t))

/-- The mean-field control profile of Theorem 2.11 (p. 10): player `v` uses
`α^MF_v(t, x) = α^MF(t, x_v) = −c x_v / (1 + c (T − t))`, which depends only on its own state.
Vertices `1, …, n` of the paper are `Fin n`. -/
noncomputable def mfProfile {n : ℕ} (c T : ℝ) : Fin n → ℝ → SDEState n → ℝ :=
  fun v t x => alphaMF c T t (x v)

/-- The vector of deviation bounds `ε^G = (ε^G_v)_v` of Theorem 2.11 (p. 10):
`ε^G_v = σ² (cT/(1+cT)) √(cT(2+cT)/deg_G(v))` if `deg_G(v) ≥ 1`, and `ε^G_v = 0` if
`deg_G(v) = 0`. The degree is cast to `ℝ` before dividing. -/
noncomputable def epsG {n : ℕ} (σ c T : ℝ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v : Fin n) : ℝ :=
  if G.degree v = 0 then 0
  else σ ^ 2 * (c * T / (1 + c * T)) * Real.sqrt (c * T * (2 + c * T) / (G.degree v : ℝ))

/-- The scalar deviation bound `ε_G` of Theorem 2.11 (p. 10):
`ε_G = σ² (cT/(1+cT)) √(cT(2+cT)/(1 ∨ δ(G)))`, where `δ(G) = min_v deg_G(v)` is the minimal degree
and `a ∨ b = max{a, b}` (footnote 2, p. 10).

Formalization Note: `δ(G)` is Mathlib's `SimpleGraph.minDegree`, which is `0` when the vertex type
is empty (`n = 0`); then `1 ∨ δ(G) = 1` and every statement about players is vacuous. -/
noncomputable def epsScalar {n : ℕ} (σ c T : ℝ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ℝ :=
  σ ^ 2 * (c * T / (1 + c * T)) *
    Real.sqrt (c * T * (2 + c * T) / ((max 1 G.minDegree : ℕ) : ℝ))

/-- The expected control energy `E ∫₀ᵀ |α_i(t, X(t))|² dt` of player `i` under a solution `S` of
the state equation (2.1) for the profile `a` (the quantity `E ∫₀ᵀ |β(t, Y(t))|² dt` of §7.2,
p. 41, when `a` is the deviated profile and `i = v`).

Formalization Note: an `ℝ≥0∞`-valued lower Lebesgue integral. -/
noncomputable def energy {n : ℕ} (T : ℝ) {σ : ℝ} {x0 : SDEState n}
    {a : Fin n → ℝ → SDEState n → ℝ} (S : GraphLQGame.Equilibrium.StateSol n T σ x0 a) (i : Fin n) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((a i t (S.X t ω)) ^ 2)) ∂S.P

/-- Player `i`'s own-state GraphLQGame.Equilibrium.cost `½ E[∫₀ᵀ |α_i(t, X(t))|² dt + c |X_i(T)|²]` under a solution `S`
for the profile `a`: the bracket of Steps (1) and (3) of §7.2 (p. 41),
`½ E[∫₀ᵀ |β(t, Y(t))|² dt + c |Y_v(T)|²]`, when `a` is the deviated profile and `i = v`. It is
the GraphLQGame.Equilibrium.cost (2.3) the player would pay without neighbours.

Formalization Note: an `ℝ≥0∞`-valued lower Lebesgue integral, like `cost`. -/
noncomputable def ownCost {n : ℕ} (c T : ℝ) {σ : ℝ} {x0 : SDEState n}
    {a : Fin n → ℝ → SDEState n → ℝ} (S : GraphLQGame.Equilibrium.StateSol n T σ x0 a) (i : Fin n) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (1 / 2) *
      ((∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((a i t (S.X t ω)) ^ 2)) +
        ENNReal.ofReal (c * (S.X T ω i) ^ 2)) ∂S.P

end GraphLQGame.DenseApprox


