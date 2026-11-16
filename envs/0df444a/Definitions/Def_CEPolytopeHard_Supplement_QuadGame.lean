-- Prove2me | Definitions.Def_CEPolytopeHard_Supplement_QuadGame
-- name    : CEPolytopeHard_Supplement_QuadGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:10:19.441978+00:00
-- url     : https://prove2.me/theorems/0af75131-add3-4436-8649-e16be951c83c
-- title:
--   Two-player quadratic concave game on $[0,1]^d$ (Section 2.3)
-- statement:
--   A **two-player quadratic game on $[0,1]^d$** has strategy sets $X_1=X_2=[0,1]^d$; player $1$ plays $x$, player $2$ plays $y$, and the opponent of player $i$ plays $x_{-i}$. Its utilities have the form
--
--   $$
--   u_i(x_i,x_{-i}) \;=\; c_i(x_{-i}) + b_i(x_{-i})^\top x_i - x_i^\top A_i(x_{-i})\,x_i ,
--   $$
--
--   where $c_i$, $b_i\in\mathbb R^d$ and $A_i\in\mathbb R^{d\times d}$ are arbitrary functions of the opponent's strategy. The **own-strategy gradient** is $\nabla_{x_i}u_i = b_i(x_{-i}) - (A_i+A_i^\top)(x_{-i})\,x_i$.
--
--   The game is **valid** (a quadratic concave game in the sense of Section 2.3) when
--
--   1. $A_i(z)$ is symmetric positive semidefinite for every $z\in[0,1]^d$, so $u_i$ is concave in the player's own strategy;
--   2. every $u_i$ takes values in $[0,1]$ on $[0,1]^d\times[0,1]^d$;
--   3. every $u_i$ is continuous on $[0,1]^d\times[0,1]^d$.
--
--   It has **bounded gradients** when $\|\nabla_{x_i}u_i(x)\|_2\le 1$ (unnormalized Euclidean norm) at every profile of $[0,1]^d\times[0,1]^d$, the promise of the black-box model of Section 2.1.
--
--   This is the game class of Theorems 2 and 3.
--
--   **Formalization Note** The opponent-only term $c_i(x_{-i})$ is not in the paper's display but is allowed by its words ("a quadratic concave function in $x_i$"), is present in the paper's imitation game (Proposition 3.6), and never changes a deviation gain. Continuity is the standing convention of concave games. Players are indexed $0,1$ and the opponent of $i$ is `i.rev`.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.3, p.11 (quadratic games, $u_i : X \to [0,1]$); Section 2.1, p.10 (gradient promise); Theorems 2 and 3, p.5

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard.Supplement

open Matrix

/-- A **two-player quadratic game on `[0,1]^d`**, given by its quadratic representation
(Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria
Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256
6aec500a…7820, Section 2.3, p.11: "We will call a game quadratic if u_i is a quadratic concave
function in x_i for every fixed opponent profile x_{−i}, i.e., if
u_i(x_i, x_{−i}) = b_i(x_{−i})^⊤x_i − x_i^⊤A_i(x_{−i})x_i, where b_i : X_{−i} → R^{d_i} and
A_i : X_{−i} → S^{d_i}_+ are arbitrary functions"; Theorems 2 and 3, p.5, with
`X_1 = X_2 = [0,1]^d`).

Players are `Fin 2` (player `0` plays `x`, player `1` plays `y`); a profile is
`p : Fin 2 → Fin d → ℝ`, and the opponent of player `i` is `i.rev`. For each player `i` and each
opponent strategy `z`, the game stores a constant `c i z`, a linear coefficient `b i z` and a
matrix `A i z`; player `i`'s utility at `p` is `c + bᵀ p_i − p_iᵀ A p_i` with the data evaluated
at the opponent's strategy.

**Formalization Note** The additive term `c i z`, which depends only on the opponent, is not in
the paper's display but is allowed by its words ("a quadratic concave function in x_i") and is
used by the paper's own imitation game (Proposition 3.6, `−‖x − y‖²` has the term `−‖y‖²`); it
does not change any deviation gain. Indices are 0-based. -/
structure QuadGame (d : ℕ) where
  /-- the term of player `i`'s utility that depends only on the opponent's strategy -/
  c : Fin 2 → (Fin d → ℝ) → ℝ
  /-- the linear coefficient `b_i(x_{−i})` -/
  b : Fin 2 → (Fin d → ℝ) → Fin d → ℝ
  /-- the quadratic coefficient `A_i(x_{−i})` -/
  A : Fin 2 → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ

/-- the strategy set `[0,1]^d` of each player (coordinatewise) -/
def box (d : ℕ) : Set (Fin d → ℝ) := Set.Icc 0 1

namespace QuadGame

variable {d : ℕ}

/-- player `i`'s utility `u_i(p) = c_i(p_{−i}) + b_i(p_{−i})^⊤ p_i − p_i^⊤ A_i(p_{−i}) p_i` -/
def utility (G : QuadGame d) (i : Fin 2) (p : Fin 2 → Fin d → ℝ) : ℝ :=
  G.c i (p i.rev) + G.b i (p i.rev) ⬝ᵥ p i - p i ⬝ᵥ (G.A i (p i.rev) *ᵥ p i)

/-- the gradient of player `i`'s utility in her own strategy,
`∇_{p_i} u_i(p) = b_i(p_{−i}) − (A_i(p_{−i}) + A_i(p_{−i})^⊤) p_i` -/
def ownGrad (G : QuadGame d) (i : Fin 2) (p : Fin 2 → Fin d → ℝ) : Fin d → ℝ :=
  G.b i (p i.rev) - (G.A i (p i.rev) + (G.A i (p i.rev))ᵀ) *ᵥ p i

/-- A **valid quadratic concave game** (Section 2.3, p.11): for every opponent strategy in
`[0,1]^d` the matrix `A_i` is symmetric positive semidefinite (`A_i : X_{−i} → S^{d}_+`), so
`u_i` is concave in the player's own strategy; every utility takes values in `[0,1]` on
`[0,1]^d × [0,1]^d` ("u_i : X → [0, 1]"); and every utility is continuous on
`[0,1]^d × [0,1]^d`.

**Formalization Note** Continuity is the standing convention of concave games (the paper's own
games are continuous); without it a game may have no approximate correlated equilibrium. -/
def Valid (G : QuadGame d) : Prop :=
  (∀ i : Fin 2, ∀ z ∈ box d, (G.A i z).PosSemidef) ∧
  (∀ (i : Fin 2) (p : Fin 2 → Fin d → ℝ), (∀ j, p j ∈ box d) → G.utility i p ∈ Set.Icc 0 1) ∧
  ∀ i : Fin 2, ContinuousOn (G.utility i) {p | ∀ j, p j ∈ box d}

/-- The **gradient promise** of the black-box model (Section 2.1, p.10: "we assume that
‖∇f(x)‖₂ ≤ 1 for all x", with the unnormalized Euclidean norm): on `[0,1]^d × [0,1]^d`,
`∑_k (∇_{p_i} u_i(p))_k² ≤ 1` for both players. -/
def GradBounded (G : QuadGame d) : Prop :=
  ∀ (i : Fin 2) (p : Fin 2 → Fin d → ℝ), (∀ j, p j ∈ box d) → ∑ k, (G.ownGrad i p k) ^ 2 ≤ 1

end QuadGame

end CEPolytopeHard.Supplement


