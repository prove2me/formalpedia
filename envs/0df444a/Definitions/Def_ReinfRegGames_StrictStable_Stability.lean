-- Prove2me | Definitions.Def_ReinfRegGames_StrictStable_Stability
-- name    : ReinfRegGames_StrictStable_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:07:45.857978+00:00
-- url     : https://prove2.me/theorems/aa569445-a86e-4825-a581-94d3444dcf4c
-- title:
--   Definition 5.1 and (5.1), pp. 21–22 — strict Nash equilibria, im Q, and stationarity, Lyapunov stability, attraction and asymptotic stability under (RL)
-- statement:
--   Fix a finite game and penalty functions $h_k$ as in the model file, and let $x^*\in\mathcal X$.
--
--   1. **Strict equilibrium (p. 21).** $x^*$ is a strict Nash equilibrium if it is a mixed profile and (5.1) is strict for all unilateral deviations:
--   $$u_k(x_k;x^*_{-k})<u_k(x^*)\qquad\text{for every } k \text{ and every } x_k\in\Delta(\mathcal A_k),\ x_k\neq x^*_k.$$
--   2. **Image of $Q$.** $x^*\in\operatorname{im}Q$ if $x^*_k=Q_k(y_k)$ for some score profile $y$.
--   3. **Stationary (Definition 5.1(1)).** $x^*\in\operatorname{im}Q$, and every orbit $x(t)=Q(y(t))$ of (RL) with $x(0)=x^*$ has $x(t)=x^*$ for all $t\ge0$.
--   4. **Lyapunov stable (Definition 5.1(2)).** For every $\varepsilon>0$ there is $\delta>0$ such that every orbit of (RL) with $\|x(0)-x^*\|<\delta$ satisfies $\|x(t)-x^*\|<\varepsilon$ for all $t\ge0$.
--   5. **Attracting (Definition 5.1(3)).** There is $\delta>0$ such that every orbit of (RL) with $\|x(0)-x^*\|<\delta$ satisfies $x(t)\to x^*$ as $t\to\infty$.
--   6. **Asymptotically stable (Definition 5.1(4)).** Lyapunov stable and attracting.
--
--   Because (RL) evolves in the dual space of scores and $Q$ is neither injective nor surjective, these notions are stated on the trajectories of play $x(t)=Q(y(t))$ rather than on a flow on $\mathcal X$; they are the notions in which Theorem 5.2 is formulated.
--
--   **Formalization Note** Neighbourhoods of $x^*$ in $\mathcal X$ are encoded by balls of the sup metric on $\prod_k\mathbb R^{\mathcal A_k}$; every $x(t)$ lies in $\mathcal X$, so these balls intersected with $\mathcal X$ are exactly the relative neighbourhoods, and the "for every neighbourhood $U$ there is a neighbourhood $V$" of Definition 5.1 is the equivalent $\varepsilon$–$\delta$ form. The requirement $x(0)\in V\cap\operatorname{im}Q$ of Definition 5.1 is automatic for orbits (Remark 5.1) and is not repeated. Strict equilibria are not required to be pure in the definition; purity is a consequence (see the milestone on the proof of Theorem 5.2, Part IV). Deviations range over all mixed strategies, exactly as in (5.1).
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 21–22, (5.1), the definition of strict equilibrium (p. 21), Definition 5.1 (1)–(4), Remark 5.1

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.StrictStable

/-- `x*` is a **strict (Nash) equilibrium** (p. 21): `x*` is a mixed profile and (5.1) holds
strictly for every unilateral deviation, i.e. `u_k(x_k; x*_{-k}) < u_k(x*)` for every player `k`
and every mixed strategy `x_k ≠ x*_k` of `k`. Purity is not built in. -/
def IsStrictNash {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (xstar : ∀ k, A k → ℝ) : Prop :=
  AGT.IsMixedProfile xstar ∧
    ∀ (k : ι) (τ : A k → ℝ), AGT.IsLottery τ → τ ≠ xstar k →
      AGT.expectedPayoff u (Function.update xstar k τ) k < AGT.expectedPayoff u xstar k

/-- `x* ∈ im Q` (Definition 5.1(1), p. 21): there is a score profile `y` with `x*_k = Q_k(y_k)`
for every player `k`. -/
def InImQ {ι : Type*} {A : ι → Type*} [∀ k, Fintype (A k)]
    (h : ∀ k, (A k → ℝ) → ℝ) (xstar : ∀ k, A k → ℝ) : Prop :=
  ∃ y : ∀ k, A k → ℝ, ∀ k, ReinfRegGames.Extinction.IsChoice (h k) (y k) (xstar k)

/-- **Definition 5.1(1)** (p. 21): `x*` is stationary under (RL) if `x* ∈ im Q` and every orbit
`x(t) = Q(y(t))` of (RL) with `x(0) = x*` satisfies `x(t) = x*` for all `t ≥ 0`. -/
def IsStationary {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (xstar : ∀ k, A k → ℝ) : Prop :=
  InImQ h xstar ∧
    ∀ y x : ℝ → ∀ k, A k → ℝ, ReinfRegGames.Extinction.IsRLOrbit u h y x → x 0 = xstar → ∀ t, 0 ≤ t → x t = xstar

/-- **Definition 5.1(2)** (p. 21): `x*` is Lyapunov stable under (RL): for every `ε > 0` there is
`δ > 0` such that every orbit `x(t) = Q(y(t))` of (RL) with `x(0)` within `δ` of `x*` stays within
`ε` of `x*` for all `t ≥ 0`. Distances are those of `∀ k, A k → ℝ` (sup metric); since orbits lie
in `X`, the balls play the role of the neighbourhoods of `x*` in `X`. -/
def IsLyapunovStable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (xstar : ∀ k, A k → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y x : ℝ → ∀ k, A k → ℝ, ReinfRegGames.Extinction.IsRLOrbit u h y x →
    dist (x 0) xstar < δ → ∀ t, 0 ≤ t → dist (x t) xstar < ε

/-- **Definition 5.1(3)** (p. 21): `x*` is attracting under (RL): there is `δ > 0` such that every
orbit `x(t) = Q(y(t))` of (RL) with `x(0)` within `δ` of `x*` converges to `x*` as `t → ∞`. -/
def IsAttracting {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (xstar : ∀ k, A k → ℝ) : Prop :=
  ∃ δ > 0, ∀ y x : ℝ → ∀ k, A k → ℝ, ReinfRegGames.Extinction.IsRLOrbit u h y x →
    dist (x 0) xstar < δ → Filter.Tendsto x Filter.atTop (nhds xstar)

/-- **Definition 5.1(4)** (p. 21): `x*` is asymptotically stable under (RL) if it is Lyapunov
stable and attracting. -/
def IsAsymptoticallyStable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (xstar : ∀ k, A k → ℝ) : Prop :=
  IsLyapunovStable u h xstar ∧ IsAttracting u h xstar

end ReinfRegGames.StrictStable


