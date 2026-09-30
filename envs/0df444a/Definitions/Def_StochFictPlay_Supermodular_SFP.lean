-- Prove2me | Definitions.Def_StochFictPlay_Supermodular_SFP
-- name    : StochFictPlay_Supermodular_SFP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:17:33.632988+00:00
-- url     : https://prove2.me/theorems/1cf52336-0196-4020-b0f1-f1980cce1894
-- title:
--   Standard stochastic fictitious play
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space and $\varepsilon^\alpha_t : \Omega \to \mathbb R^{n^\alpha}$ ($t \in \mathbb N$, $\alpha$ a player) random vectors.
--
--   1. **Shock family.** Each $\varepsilon^\alpha_t$ is measurable with density $f^\alpha$, and the whole family $(\varepsilon^\alpha_t)_{t,\alpha}$ is independent over time and across players.
--   2. **The process.** Fix an initial pure profile $s_1$ and let $\zeta_1 = (e_{s_1^1}, \dots, e_{s_1^p})$. For $t \ge 1$ let
--   $$Z_t = \frac1t \sum_{u=1}^t \zeta_u,$$
--   and let $\zeta_{t+1}^\alpha = e_i$ where $i$ maximizes $U^\alpha_k(Z_t^{-\alpha}) + (\varepsilon_t^\alpha)_k$ over $k$.
--
--   Then, conditionally on $Z_t = z$, player $\alpha$ plays $i$ at time $t+1$ with probability $\tilde B^\alpha_i(z^{-\alpha})$, which is eq. (12). $Z_t \in \Sigma$ records the empirical frequencies of play.
--
--   **Formalization Note** The process is defined pathwise from the shocks. Ties in the argmax are broken by the smallest index; they have probability zero because each shock has a density. The shock $\varepsilon_t$ produces $\zeta_{t+1}$; $\varepsilon_0$ and the value at $t = 0$ are unused. The independence requirement covers the unused $\varepsilon_0$, which is harmless.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, pp. 10-11, eqs. (11)-(12)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_Game

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- The standard basis vector `e_i` of the smallest maximizer `i` of `v`: coordinate `i` is `1`
iff `v i` is maximal and every smaller index has a strictly smaller value, else `0`. For
`k ≥ 1` exactly one coordinate is `1` (argmax with ties broken by the smallest index). -/
noncomputable def argmaxVec {k : ℕ} (v : Fin k → ℝ) : Fin k → ℝ :=
  fun i => if (∀ j, v j ≤ v i) ∧ (∀ j, j < i → v j < v i) then 1 else 0

/-- The mixed-strategy representation `(e_{s^1}, …, e_{s^p})` of a pure profile `s`. -/
noncomputable def pureVec {p : ℕ} {n : Fin p → ℕ} (s : Profile n) : Mixed n :=
  fun α => Pi.single (s α) (1 : ℝ)

/-- The pure strategies chosen at time `t + 1` in standard SFP, (12) (manuscript p. 10), as
basis vectors: player `α` plays the (smallest) maximizer of `U^α_k(z^{−α}) + (ε^α_t)_k`, given
beliefs `z` and the time-`t` shocks `εt`. -/
noncomputable def sfpChoice {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (u : (α : Fin p) → Profile n → ℝ) (z : Mixed n)
    (εt : (α : Fin p) → Ω → (Fin (n α) → ℝ)) (ω : Ω) : Mixed n :=
  fun α => argmaxVec (fun k => payoffVec u z α k + εt α ω k)

/-- Cumulative play `∑_{u=1}^t ζ_u` of standard stochastic fictitious play (11)–(12),
pp. 10–11. `ζ_1 = e(s₁)` is the arbitrary initial pure profile, and for `t ≥ 1`,
`ζ_{t+1}` is the best response to beliefs `Z_t = (1/t) ∑_{u ≤ t} ζ_u` under the shocks `ε t`.
The value at `t = 0` is `0` and is never used. -/
noncomputable def sfpCum {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) : ℕ → Ω → Mixed n
  | 0 => fun _ => 0
  | 1 => fun _ => pureVec s₁
  | (t + 2) => fun ω =>
      sfpCum u s₁ ε (t + 1) ω +
        sfpChoice u ((1 / ((t + 1 : ℕ) : ℝ)) • sfpCum u s₁ ε (t + 1) ω) (ε (t + 1)) ω

/-- The beliefs `Z_t = (1/t) ∑_{u=1}^t ζ_u ∈ Σ` of standard SFP, (11) (p. 10), for `t ≥ 1`. -/
noncomputable def sfpBelief {Ω : Type*} {p : ℕ} {n : Fin p → ℕ}
    (u : (α : Fin p) → Profile n → ℝ) (s₁ : Profile n)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) (t : ℕ) (ω : Ω) : Mixed n :=
  (1 / (t : ℝ)) • sfpCum u s₁ ε t ω

/-- The shocks of standard SFP (p. 10): each `ε t α` has the density `f α`, and the family is
independent over time `t` and across players `α`. -/
def IsShockFamily {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ} {n : Fin p → ℕ}
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (ε : ℕ → (α : Fin p) → Ω → (Fin (n α) → ℝ)) : Prop :=
  (∀ t α, Measurable (ε t α)) ∧
  (∀ t α, P.map (ε t α) = volume.withDensity (f α)) ∧
  iIndepFun (β := fun i : ℕ × Fin p => Fin (n i.2) → ℝ) (fun i ω => ε i.1 i.2 ω) P

end StochFictPlay.Supermodular


