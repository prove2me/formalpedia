-- Prove2me | Definitions.Def_OptHedgeGames_Interpolation
-- name    : OptHedgeGames_Interpolation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:29.600571+00:00
-- url     : https://prove2.me/theorems/9e15c72f-5902-4da0-b1db-c085ad138382
-- title:
--   The interpolation (39) $Y,L$, the frozen curves $\bar Y,\bar L$, and the window sums $\delta_{t_0},u_{t_0}$
-- statement:
--   In the two-player run, for every integer $j\ge1$ and $s\in[j,j+1]$ let $g^j=2\ell_2^j-\ell_2^{j-1}$ be the **score direction** of round $j$, and
--   $$
--   Y(s)=E_{x_2^j}[-\eta(s-j)g^j],\qquad L(s)=AY(s).
--   $$
--   Fix an integer $W\ge1$ and an anchor $t_0\ge2$. Freezing player 2's losses at $\ell_2^{t_0}$ gives the **comparison curves**
--   $$
--   \bar Y(s)=E_{x_2^{t_0}}[-\eta(s-t_0)\ell_2^{t_0}],\qquad \bar L(s)=A\bar Y(s).
--   $$
--   The movement of player 2's losses over the window $[t_0,t_0+3W]$ is measured by
--   $$
--   \delta_{t_0}=\sum_{r=t_0-1}^{t_0+3W-2}\|\ell_2^{r+1}-\ell_2^r\|_\infty,\qquad u_{t_0}=\sum_{r=t_0-1}^{t_0+3W-2}\|\ell_2^{r+1}-\ell_2^r\|_\infty^2.
--   $$
--   These curves turn the discrete sums of the regret analysis into integrals, on which a Bernstein inequality for exponential sums applies.
--
--   **Formalization Note** $Y$ uses $j=\lfloor s\rfloor$ with `Nat.floor`, and at an integer $s$ it reads the round $s$ with local time $0$, which agrees with the left limit. Derivatives are `deriv`: $L$ may have corners at the integers, so statements that read $L'$ pointwise exclude integers, and the integrals are unaffected.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), (39), p.21; Windows and the frozen curve, p.22

import Mathlib
import Definitions.Def_OptHedgeGames_TwoPlayerRun

open scoped Matrix

namespace OptHedgeGames

/-- The **score direction** of round `j ≥ 1` of player 2, `gʲ = 2ℓʲ₂ − ℓʲ⁻¹₂`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), above (39), p.21).

**Formalization Note** `j - 1` is natural-number subtraction, read only at `j ≥ 1`. -/
noncomputable def Game.score {n : ℕ} (G : Game n) (η : ℝ) (j : ℕ) : Fin n → ℝ :=
  fun b => 2 * G.l2 η j b - G.l2 η (j - 1) b

/-- The **interpolated strategy (39)** of player 2: `Y(s) = E_{xʲ₂}[−η(s − j)gʲ]` for
`s ∈ [j, j + 1]`, `j ≥ 1` (manuscript sha256 383e3793…, (39), p.21).

**Formalization Note** `j = ⌊s⌋₊`, so each `s ≥ 1` reads the round containing it. At an integer
`s = j + 1` the definition takes the round `j + 1` with local time `0`, giving `xʲ⁺¹₂`, which is also
the left limit, as the paper notes (`Y(j + 1) = xʲ⁺¹₂`). Values at `s < 1` are unused. -/
noncomputable def Game.Y {n : ℕ} (G : Game n) (η s : ℝ) : Fin n → ℝ :=
  tilt (G.x2 η ⌊s⌋₊) (fun b => -η * (s - (⌊s⌋₊ : ℝ)) * G.score η ⌊s⌋₊ b)

/-- The **interpolated losses (39)** of player 1, `L(s) = AY(s)`
(manuscript sha256 383e3793…, (39), p.21). -/
noncomputable def Game.L {n : ℕ} (G : Game n) (η s : ℝ) : Fin n → ℝ :=
  G.A *ᵥ G.Y η s

/-- The **frozen comparison curve** `Ȳ(s) = E_{x^{t₀}₂}[−η(s − t₀)ℓ^{t₀}₂]`
(manuscript sha256 383e3793…, Windows and the frozen curve, p.22). -/
noncomputable def Game.Ybar {n : ℕ} (G : Game n) (η : ℝ) (t₀ : ℕ) (s : ℝ) : Fin n → ℝ :=
  tilt (G.x2 η t₀) (fun b => -η * (s - (t₀ : ℝ)) * G.l2 η t₀ b)

/-- The **frozen comparison curve** `L̄(s) = AȲ(s)`
(manuscript sha256 383e3793…, Windows and the frozen curve, p.22). -/
noncomputable def Game.Lbar {n : ℕ} (G : Game n) (η : ℝ) (t₀ : ℕ) (s : ℝ) : Fin n → ℝ :=
  G.A *ᵥ G.Ybar η t₀ s

/-- The **movement of player 2's losses over the window**,
`δ_{t₀} = Σ_{r=t₀−1}^{t₀+3W−2} ∥ℓʳ⁺¹₂ − ℓʳ₂∥_∞`
(manuscript sha256 383e3793…, Windows and the frozen curve, p.22).

**Formalization Note** `∥·∥_∞` is Mathlib's supremum norm on `Fin n → ℝ`. The natural-number
subtractions are true subtractions under the paper's `t₀ ≥ 2`, `W ≥ 1`. -/
noncomputable def Game.delta {n : ℕ} (G : Game n) (η : ℝ) (W t₀ : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc (t₀ - 1) (t₀ + 3 * W - 2), ‖G.l2 η (r + 1) - G.l2 η r‖

/-- The **squared movement of player 2's losses over the window**,
`u_{t₀} = Σ_{r=t₀−1}^{t₀+3W−2} ∥ℓʳ⁺¹₂ − ℓʳ₂∥²_∞`
(manuscript sha256 383e3793…, Windows and the frozen curve, p.22). -/
noncomputable def Game.u {n : ℕ} (G : Game n) (η : ℝ) (W t₀ : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc (t₀ - 1) (t₀ + 3 * W - 2), ‖G.l2 η (r + 1) - G.l2 η r‖ ^ 2

end OptHedgeGames


