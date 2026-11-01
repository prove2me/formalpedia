-- Prove2me | Definitions.Def_TimeVaryingGames_ContinuousGame
-- name    : TimeVaryingGames_ContinuousGame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:33.813414+00:00
-- url     : https://prove2.me/theorems/1126cfb1-d70c-4627-841b-a198690d2568
-- title:
--   Continuous games: action space, individual payoff gradients, Nash equilibria, strict monotonicity
-- statement:
--   Let $\mathcal N$ be a finite set of players. Player $i\in\mathcal N$ chooses an action $x_i$ from a set $\mathcal K_i$ in a finite-dimensional real normed space $\mathcal X_i$, and $\mathcal Y_i=\mathcal X_i^*$ is its dual, with dual norm $\|y\|_*=\sup\{\langle y,x\rangle:\|x\|\le 1\}$. Each player has a payoff function $u_i$ of the action profile $x=(x_i;x_{-i})$, which the player wants to **maximize**.
--
--   1. The **action space** is $\mathcal K=\prod_{i\in\mathcal N}\mathcal K_i$.
--   2. The **individual payoff gradient** of player $i$ is
--   $$v_i(x)=\nabla_{x_i}u_i(x_i;x_{-i})\in\mathcal Y_i,$$
--   the derivative of $u_i$ at $x$ along the $i$-th factor, viewed as an element of the dual; $v(x)=(v_1(x),\dots,v_N(x))$ and $\langle v(x),z\rangle=\sum_i\langle v_i(x),z_i\rangle$.
--   3. A profile $x^*\in\mathcal K$ is a **Nash equilibrium** if $u_i(x^*_i;x^*_{-i})\ge u_i(x_i;x^*_{-i})$ for all $x_i\in\mathcal K_i$ and all $i\in\mathcal N$.
--   4. The game is **strictly monotone** if
--   $$\langle v(x')-v(x),x'-x\rangle<0\qquad\text{for all }x,x'\in\mathcal K,\ x'\ne x.$$
--
--   These are the objects of a continuous game in the sense of Rosen; strict monotonicity is the strict form of the diagonal concavity condition (DC), and it is the hypothesis under which the game has a unique Nash equilibrium.
--
--   **Formalization Note** The payoff gradient is `(fderiv ℝ (u i) x).comp (ContinuousLinearMap.single ℝ E i)`, an element of `E i →L[ℝ] ℝ`, whose operator norm is the dual norm. The pairing is evaluation; no inner product is assumed. Every statement using $v_i$ assumes $u_i$ differentiable on an open neighbourhood of $\mathcal K$, so the junk value of `fderiv` at non-differentiable points never enters.
-- source:
--   Duvocelle, Mertikopoulos, Staudigl, Vermeulen, Multi-Agent Online Learning in Time-Varying Games, arXiv:1809.03066v3, §2.2–2.3, pp.4–5, eqs. (1), (2), (NE), (DC), strictly monotone (1) on p.5

import Mathlib

namespace TimeVaryingGames

/-- **The action space of a continuous game.**
Duvocelle, Mertikopoulos, Staudigl, Vermeulen, *Multi-Agent Online Learning in Time-Varying
Games*, arXiv:1809.03066v3, §2.2, p.4: "writing K := ∏_{i∈N} K_i for the game's action space".

The set of action profiles `x = (x_i)_i` with `x_i ∈ K_i` for every player `i`. -/
def profiles {ι : Type*} {E : ι → Type*} (K : ∀ i, Set (E i)) : Set (∀ i, E i) :=
  Set.pi Set.univ K

/-- **Individual payoff gradient** `v_i(x) = ∇_{x_i} u_i(x_i; x_{-i})`.
arXiv:1809.03066v3, §2.2, p.4, eq. (1): "we will write v_i(x) for the individual payoff gradient
of the i-th player"; "we will also adopt the established convention of treating v_i(x) as an
element of the dual space Y_i := X_i^* of X_i".

**Formalization Note.** `v_i(x)` is the Fréchet derivative of `u_i` at the profile `x`,
restricted to the `i`-th factor: `(fderiv ℝ (u i) x) ∘ single i`. It is an element of the dual
`E i →L[ℝ] ℝ`, whose operator norm is the paper's dual norm `‖·‖_*`; the pairing `⟨y, z⟩` is the
evaluation `y z`. The payoffs are used only on an open neighbourhood of the action space on which
they are differentiable (a hypothesis of every statement), so the junk value `0` of `fderiv` at a
point of non-differentiability never matters. -/
noncomputable def partialGradient {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (u : ι → (∀ j, E j) → ℝ) (i : ι) (x : ∀ j, E j) : E i →L[ℝ] ℝ :=
  (fderiv ℝ (u i) x).comp (ContinuousLinearMap.single ℝ E i)

/-- **Nash equilibrium** (NE).
arXiv:1809.03066v3, §2.3, p.4: "an action profile x* ∈ K that is resilient to unilateral
deviations, i.e., u_i(x*_i; x*_{-i}) ≥ u_i(x_i; x*_{-i}) for all x_i ∈ K_i and all i ∈ N."

Players **maximize** their payoffs `u_i`. The deviation `(x_i; x*_{-i})` is
`Function.update xs i y`. -/
def IsNash {ι : Type*} [DecidableEq ι] {E : ι → Type*} (K : ∀ i, Set (E i))
    (u : ι → (∀ j, E j) → ℝ) (xs : ∀ i, E i) : Prop :=
  xs ∈ profiles K ∧ ∀ i, ∀ y ∈ K i, u i (Function.update xs i y) ≤ u i xs

/-- **Strictly monotone game**: (DC) holding strictly when `x' ≠ x`.
arXiv:1809.03066v3, §2.3, pp.4–5: "⟨v(x') − v(x), x' − x⟩ ≤ 0 for all x, x' ∈ K. (DC)" and
"(1) Strictly monotone if (DC) holds as a strict inequality when x' ≠ x."

**Formalization Note.** The profile pairing is `⟨v(x), z⟩ = ∑_i ⟨v_i(x), z_i⟩`, evaluation of
the dual elements `v_i(x)` on the components `z_i`. -/
def IsStrictlyMonotone {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    (K : ∀ i, Set (E i)) (u : ι → (∀ j, E j) → ℝ) : Prop :=
  ∀ x ∈ profiles K, ∀ x' ∈ profiles K, x' ≠ x →
    ∑ i, (partialGradient u i x' - partialGradient u i x) (x' i - x i) < 0

end TimeVaryingGames


