-- Prove2me | Definitions.Def_StochFictPlay_Potential_PotentialGame
-- name    : StochFictPlay_Potential_PotentialGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:34.193243+00:00
-- url     : https://prove2.me/theorems/34c05ea6-f121-4b05-b94c-cd8f182fdcc2
-- title:
--   Potential games, the function $\Pi$ of Proposition 4.1, and tangent critical points
-- statement:
--   Let $G$ be a $p$ player normal form game with utilities $u^\alpha$ on the pure profiles $S$.
--
--   1. **Potential game.** $G$ is a potential game if $u^\alpha(s) = u^\beta(s)$ for all players $\alpha,\beta$ and all $s \in S$: all players always receive the same payoff.
--   2. **The function $\Pi$.** For deterministic perturbations $V^\alpha$ and a reference player $\alpha_0$,
--   $$\Pi(x^1,\dots,x^p) = \sum_{s\in S}\Big(u^{\alpha_0}(s)\prod_\alpha x^\alpha_{s^\alpha}\Big) - \sum_\alpha V^\alpha(x^\alpha).$$
--   The paper takes $\alpha_0$ to be player 1.
--   3. **Tangent critical point.** $x$ is a critical point of a function $\Phi$ on $\Sigma$ if for every direction $\theta$ with $\sum_i \theta^\alpha_i = 0$ for each player $\alpha$, the derivative of $h \mapsto \Phi(x + h\theta)$ at $h = 0$ exists and equals $0$.
--
--   These are the objects of §4.2: in potential games $\Pi$ is a strict Lyapunov function for (PV), and its critical points are the rest points of (PV).
--
--   **Formalization Note** This is the identical-payoff definition of the paper, not the Monderer–Shapley exact-potential definition (footnote 7 explains why the restriction is harmless). Player 1 is index $0$. Only directional derivatives along the tangent space are used, so $\Phi$ need only be meaningful on the planes $\sum_i x^\alpha_i = 1$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, §4.2, pp. 16-17: definition of a potential game (p. 16) and the function Π of Proposition 4.1 (p. 17); critical points, Appendix, proof of Proposition 4.2, p. 27

import Mathlib
import Definitions.Def_StochFictPlay_Potential_Game

namespace StochFictPlay.Potential

/-- A **potential game** in the sense of Hofbauer–Sandholm (2002), manuscript p. 16: all players
always receive the same payoff, `u^α(s) = u^β(s)` for all players `α, β` and all pure profiles
`s`. (Not the Monderer–Shapley exact-potential definition; see footnote 7, p. 17.) -/
def IsPotentialGame {p : ℕ} {n : Fin p → ℕ} (u : (α : Fin p) → Profile n → ℝ) : Prop :=
  ∀ α β : Fin p, ∀ s : Profile n, u α s = u β s

/-- The function of Proposition 4.1 (manuscript p. 17):
`Π(x¹, …, x^p) = ∑_{s ∈ S} (u^{α₀}(s) ∏_α x^α_{s^α}) − ∑_α V^α(x^α)`. The paper uses player 1's
utility `u¹`; the reference player `α₀` is a parameter (player 1 is `⟨0, _⟩ : Fin p`), and in a
potential game every choice gives the same function. -/
noncomputable def potentialFn {p : ℕ} {n : Fin p → ℕ} (V : (α : Fin p) → (Fin (n α) → ℝ) → ℝ)
    (u : (α : Fin p) → Profile n → ℝ) (α₀ : Fin p) (x : Mixed n) : ℝ :=
  ∑ s : Profile n, u α₀ s * ∏ α, x α (s α) - ∑ α, V α (x α)

/-- `x` is a **critical point of `Φ` on `Σ`** (manuscript p. 27, proof of Proposition 4.2): the
derivative of `Φ` at `x` vanishes in every direction `θ` tangent to `Σ`, i.e. every
`θ` with `∑_i θ^α_i = 0` for each player `α`. Directional derivatives only, so `Φ` need only
be defined along the planes `∑_i x^α_i = 1`. -/
def IsTangentCritical {p : ℕ} {n : Fin p → ℕ} (Φ : Mixed n → ℝ) (x : Mixed n) : Prop :=
  ∀ θ : Mixed n, (∀ α, ∑ i, θ α i = 0) → HasDerivAt (fun h : ℝ => Φ (x + h • θ)) 0 0

end StochFictPlay.Potential


