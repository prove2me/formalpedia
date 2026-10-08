-- Prove2me | Definitions.Def_UncoupledDyn_Finite_Setting
-- name    : UncoupledDyn_Finite_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:07:58.929161+00:00
-- url     : https://prove2.me/theorems/b25855d4-6daa-4d55-bd78-a5720ead3784
-- title:
--   §I and §III, pp. 1830–1833 — three-player 2×2×2 games, mixed profiles, Nash equilibrium, dynamics, uncoupled (2), Nash-convergent, fn. 7 neighborhood, Jordan's family
-- statement:
--   This file fixes the setting of Hart and Mas-Colell's three-player example (§I and §III).
--
--   **Games.** There are three players, each with two pure strategies, called $0$ (top row, left column, left matrix) and $1$ (bottom row, right column, right matrix). A pure profile is $s=(s^1,s^2,s^3)\in\{0,1\}^3$. A game $\Gamma$ is identified with its triple of payoff functions $(u^1,u^2,u^3)$, $u^i:\{0,1\}^3\to\mathbb R$.
--
--   **States.** The state space is the set of mixed profiles $X=[0,1]^3$, where $x^i$ is the probability that player $i$ plays strategy $0$. The mixed extension of $u^i$ is
--   $$u^i(x)=\sum_{s\in\{0,1\}^3}\Big(\prod_{j=1}^3 p_j(s^j)\Big)\,u^i(s),\qquad p_j(0)=x^j,\ p_j(1)=1-x^j .$$
--   A **Nash equilibrium** is an $\bar x\in X$ such that $u^i(y,\bar x^{-i})\le u^i(\bar x)$ for every player $i$ and every $y\in[0,1]$.
--
--   **Jordan's family $\mathcal U_0$.** For $a=(a^1,a^2,a^3)$, player $i$ receives $a^i$ when it plays $0$ and the next player $i+1$ (mod 3) plays $1$, receives $1$ when it plays $1$ and the next player plays $0$, and $0$ otherwise. This is the payoff table of p. 1833 (player 1 the row, player 2 the column, player 3 the matrix):
--
--   | | left | right | | left | right |
--   |---|---|---|---|---|---|
--   | top | $0,0,0$ | $a^1,1,0$ | | $0,a^2,1$ | $a^1,0,1$ |
--   | bottom | $1,0,a^3$ | $0,1,a^3$ | | $1,a^2,0$ | $0,0,0$ |
--
--   (left matrix on the left, right matrix on the right). Jordan's game $\Gamma_0$ is the member with $a^1=a^2=a^3=1$.
--
--   **Neighborhoods (fn. 7).** $\Gamma$ lies in the $\varepsilon$-neighborhood of $\Gamma_0$ when $|u^i(s)-u_0^i(s)|<\varepsilon$ for all pure profiles $s$ and all players $i$.
--
--   **Dynamics.** A dynamic is a map $F$ assigning to a state $x$ and a game $\Gamma$ the velocity $\dot x=F(x;\Gamma)\in\mathbb R^3$. A **solution** for $\Gamma$ is a curve $x:[0,\infty)\to X$ with $\dot x(t)=F(x(t);\Gamma)$ for all $t\ge 0$ (one-sided at $t=0$). The **Jacobian** $J$ of $F(\cdot;\Gamma)$ at $x$ is the $3\times 3$ matrix $J_{kl}=\partial F^k/\partial x^l$, the derivative being taken within $X$.
--
--   **Uncoupled (display (2), p. 1831).** $F$ is uncoupled for a family $\mathcal U$ if, for every player $i$ and all $\Gamma,\Gamma'\in\mathcal U$ in which player $i$ has the same payoff function $u^i$, $F^i(x;\Gamma)=F^i(x;\Gamma')$ at every $x\in X$: player $i$'s motion depends on the game only through $u^i$.
--
--   **Nash-convergent (p. 1831).** $F$ is Nash-convergent for $\mathcal U$ if for every $\Gamma\in\mathcal U$ and every Nash equilibrium $\bar x$ of $\Gamma$: $F(\bar x;\Gamma)=0$; $F(\cdot;\Gamma)$ is $C^1$ on $X$; all eigenvalues of the Jacobian at $\bar x$ have negative real parts; and every solution converges to $\bar x$ as $t\to\infty$.
--
--   These objects are the vocabulary of Theorem 1 in its §III case and of all milestones of this mission.
--
--   **Formalization Note.** Players are indexed $0,1,2$ (the page's player $i$ is index $i-1$), and "the next player" is $i+1$ in `Fin 3`. A game is a function `Fin 3 → (Fin 3 → Fin 2) → ℝ`; two games give player $i$ the same payoff function exactly when `G i = G' i`. Values of $F$ outside $X$ are never used: solutions are required to stay in $X$, and uncoupledness is required only at states in $X$. The C¹ and Jacobian conditions, which the page imposes on the class of dynamics considered, are clauses of `NashConvergent`; the two readings give the same theorem. The Jacobian is `fderivWithin` on $X$ (unique since $X$ is convex with nonempty interior). Stability of the Jacobian uses the published `FatkhullinPolyak.Discrete.IsHurwitz` on `Fin 3`-indexed matrices, so no reindexing is needed. The table is encoded by the mismatch rule of fn. 13; a cell-by-cell check against the printed table was compiled outside the mission.
-- source:
--   Hart and Mas-Colell, Uncoupled Dynamics Do Not Lead to Nash Equilibrium, Amer. Econ. Rev. 93(5) (2003), pp. 1830–1833, §I (1)–(2), fn. 5, fn. 7, §III and fn. 13

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace UncoupledDyn.Finite

/-- A pure-strategy profile of the three-player, two-strategy games of §III (Hart–Mas-Colell 2003,
p. 1833). Players are `Fin 3` (the page's player `i` is index `i - 1`); strategy `0` is the top row /
left column / left matrix, strategy `1` the bottom row / right column / right matrix. -/
abbrev Profile := Fin 3 → Fin 2

/-- A game, identified with its triple of payoff functions `uⁱ : Π Sʲ → ℝ` (§I, p. 1830):
`G i s` is player `i`'s payoff at the pure profile `s`. -/
abbrev Game := Fin 3 → Profile → ℝ

/-- The state space `X = Π Δ(Sⁱ)` (§I, §III): `x i ∈ [0, 1]` is the probability that player `i`
plays strategy `0` (top row, left column, left matrix). -/
def X : Set (Fin 3 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 1)

/-- The mixed extension: player `i`'s expected payoff when the players randomize independently,
player `j` playing strategy `0` with probability `x j`. -/
noncomputable def expPayoff (G : Game) (i : Fin 3) (x : Fin 3 → ℝ) : ℝ :=
  ∑ s : Profile, (∏ j, (if s j = 0 then x j else 1 - x j)) * G i s

/-- `x` is a (mixed-strategy) Nash equilibrium of `G`: `x ∈ X` and no player gains by a unilateral
deviation to any other mixed strategy `y ∈ [0, 1]`. -/
def IsNash (G : Game) (x : Fin 3 → ℝ) : Prop :=
  x ∈ X ∧ ∀ i, ∀ y ∈ Set.Icc (0 : ℝ) 1, expPayoff G i (Function.update x i y) ≤ expPayoff G i x

/-- Jordan's family `𝒰₀` (§III, p. 1833): player `i` (0-based) receives `a i` when it plays `0` and
the next player `i + 1` (mod 3) plays `1`, receives `1` when it plays `1` and the next player plays
`0`, and `0` otherwise (fn. 13: each player wants to mismatch the next one). This rule reproduces the
eight cells of the printed table, rows = player 1, columns = player 2, matrices = player 3:
left matrix `(0,0,0) (a¹,1,0) / (1,0,a³) (0,1,a³)`, right matrix `(0,a²,1) (a¹,0,1) / (1,a²,0) (0,0,0)`. -/
def jordanGame (a : Fin 3 → ℝ) : Game := fun i s =>
  if s i = 0 ∧ s (i + 1) = 1 then a i
  else if s i = 1 ∧ s (i + 1) = 0 then 1
  else 0

/-- Jordan's game `Γ₀`: all `aⁱ = 1` (§III, p. 1833). -/
def Gamma0 : Game := jordanGame (fun _ => 1)

/-- Footnote 7, p. 1831: `G` lies in the `ε`-neighborhood of `G0`, i.e. `|uⁱ(s) − u₀ⁱ(s)| < ε` for
every pure profile `s` and every player `i`. -/
def IsNear (G G0 : Game) (ε : ℝ) : Prop :=
  ∀ i, ∀ s : Profile, |G i s - G0 i s| < ε

/-- Uncoupled dynamic for the family `U` (display (2), p. 1831): `F x G` is the velocity `ẋ`;
for every player `i`, if two games of `U` give player `i` the same payoff function, then at every
state `x ∈ X` player `i`'s component of the velocity is the same in both games. -/
def Uncoupled (U : Set Game) (F : (Fin 3 → ℝ) → Game → (Fin 3 → ℝ)) : Prop :=
  ∀ G ∈ U, ∀ G' ∈ U, ∀ i, G i = G' i → ∀ x ∈ X, F x G i = F x G' i

/-- `x : ℝ → ℝ³` is a solution of `ẋ = F(x; G)` on `[0, ∞)` that stays in the state space `X`. -/
def IsSolution (F : (Fin 3 → ℝ) → Game → (Fin 3 → ℝ)) (G : Game) (x : ℝ → (Fin 3 → ℝ)) : Prop :=
  ∀ t, 0 ≤ t → x t ∈ X ∧ HasDerivWithinAt x (F (x t) G) (Set.Ici 0) t

/-- The Jacobian matrix of `F(·; G)` at `x`, derivative taken within `X`:
entry `(k, l)` is `∂Fᵏ/∂xˡ`. -/
noncomputable def jac (F : (Fin 3 → ℝ) → Game → (Fin 3 → ℝ)) (G : Game) (x : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun k l => (fderivWithin ℝ (fun y => F y G) X x) (Pi.single l 1) k

/-- Nash-convergent dynamic for `U` (§I, p. 1831): for every game `G ∈ U` and every Nash
equilibrium `xbar` of `G`, `xbar` is a rest point, `F(·; G)` is `C¹` on `X`, the Jacobian at `xbar`
has all eigenvalues with negative real part, and every solution in `X` converges to `xbar`. -/
def NashConvergent (U : Set Game) (F : (Fin 3 → ℝ) → Game → (Fin 3 → ℝ)) : Prop :=
  ∀ G ∈ U, ∀ xbar, IsNash G xbar →
    F xbar G = 0 ∧ ContDiffOn ℝ 1 (fun y => F y G) X ∧
    FatkhullinPolyak.Discrete.IsHurwitz (jac F G xbar) ∧
    ∀ x : ℝ → (Fin 3 → ℝ), IsSolution F G x → Filter.Tendsto x Filter.atTop (nhds xbar)

end UncoupledDyn.Finite


