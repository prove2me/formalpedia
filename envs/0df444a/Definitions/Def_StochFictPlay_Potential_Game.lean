-- Prove2me | Definitions.Def_StochFictPlay_Potential_Game
-- name    : StochFictPlay_Potential_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:08:05.0099+00:00
-- url     : https://prove2.me/theorems/a4111991-e26c-47d5-9e61-6a8a24172012
-- title:
--   Finite normal-form games, perturbed best responses, the dynamics (P) and (PV), and stochastic fictitious play
-- statement:
--   A $p$ player normal form game has strategy sets $S^\alpha = \{0,\dots,n^\alpha - 1\}$ and utilities $u^\alpha : S \to \mathbb R$ on the pure profiles $S = \prod_\beta S^\beta$. Mixed profiles $x = (x^1,\dots,x^p)$ live in $\prod_\alpha \mathbb R^{n^\alpha}$, and $\Sigma = \prod_\alpha \Delta S^\alpha$.
--
--   1. **Payoff vector.** $U^\alpha_{i}(x^{-\alpha}) = \sum_{s \in S,\ s^\alpha = i} u^\alpha(s) \prod_{\beta\neq\alpha} x^\beta_{s^\beta}$.
--   2. **Perturbed best response.** $\tilde B^\alpha(x^{-\alpha}) = C^\alpha(U^\alpha(x^{-\alpha}))$, where $C^\alpha$ is the choice function of player $\alpha$'s shock density $f^\alpha$.
--   3. **Dynamics.** $(P)\ \dot x^\alpha = \tilde B^\alpha(x^{-\alpha}) - x^\alpha$, and, for maps $\tilde C^\alpha$ (perturbed best responses of deterministic perturbations $V^\alpha$), $(PV)\ \dot x^\alpha = \tilde C^\alpha(U^\alpha(x^{-\alpha})) - x^\alpha$.
--   4. **Shocks.** Random vectors $\varepsilon^\alpha_t$ ($t \in \mathbb N$, $\alpha$ a player) on a probability space, $\varepsilon^\alpha_t$ with density $f^\alpha$, independent over time and across players.
--   5. **Stochastic fictitious play.** From an arbitrary initial pure profile $s_1$, $\zeta_1 = (e_{s_1^1},\dots,e_{s_1^p})$, and for $t \ge 1$ player $\alpha$ plays at time $t+1$ the pure strategy maximizing $U^\alpha_k(Z_t^{-\alpha}) + (\varepsilon^\alpha_t)_k$ over $k$, where the beliefs are the time averages
--   $$Z_t = \frac1t \sum_{u=1}^t \zeta_u .$$
--
--   These are the objects of §§3.1–3.3: Theorem 6.1 is a statement about the random process $Z_t$, and (P) is its mean dynamic.
--
--   **Formalization Note** Indices are 0-based. Fields are defined on the whole ambient space $\prod_\alpha\mathbb R^{n^\alpha}$, so that their derivatives are ordinary Fréchet derivatives. The payoff vector takes the full profile and does not depend on $x^\alpha$. The argmax in the choice rule breaks ties by the smallest index; ties have probability zero because the shocks have densities. The shock $\varepsilon_t$ determines $\zeta_{t+1}$, as in (12); $\varepsilon_0$ is unused, and the value of the cumulative sum at $t = 0$ is $0$ and is never used. Densities may differ across players.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, §3.1-3.3, pp. 9-11: the normal form game and payoff vectors (p. 9), perturbed best responses and standard stochastic fictitious play, eqs. (11)-(12) (p. 10), the dynamic (P) (p. 11); (PV), p. 14

import Mathlib
import Definitions.Def_StochFictPlay_Potential_ChoiceModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StochFictPlay.Potential

/-- Pure strategy profiles `S = ∏_β S^β` of a `p`-player game in which player `α` has the
strategies `Fin (n α)` (the paper's `{1, …, n^α}`, 0-based here); manuscript p. 9. -/
abbrev Profile {p : ℕ} (n : Fin p → ℕ) := (α : Fin p) → Fin (n α)

/-- The ambient space `∏_α ℝ^{n^α}` in which mixed strategy profiles live. -/
abbrev Mixed {p : ℕ} (n : Fin p → ℕ) := (α : Fin p) → Fin (n α) → ℝ

/-- The mixed strategy profiles `Σ = ∏_β ∆S^β` (p. 9). -/
def mixedProfiles {p : ℕ} (n : Fin p → ℕ) : Set (Mixed n) :=
  {x | ∀ α, x α ∈ stdSimplex ℝ (Fin (n α))}

/-- The profiles of interior mixed strategies `∏_β int(∆S^β)`. -/
def interiorProfiles {p : ℕ} (n : Fin p → ℕ) : Set (Mixed n) :=
  {x | ∀ α, x α ∈ openSimplex (n α)}

/-- Player `α`'s payoff vector (p. 9):
`U^α_{s^α}(x^{−α}) = ∑_{s^{−α}} u^α(s^α, s^{−α}) ∏_{β ≠ α} x^β_{s^β}`. It is written as a sum
over full profiles `s` with `s α = i`, and does not depend on `x α`. -/
noncomputable def payoffVec {p : ℕ} {n : Fin p → ℕ} (u : (α : Fin p) → Profile n → ℝ)
    (x : Mixed n) (α : Fin p) : Fin (n α) → ℝ :=
  fun i => ∑ s : Profile n,
    if s α = i then u α s * ∏ β ∈ Finset.univ.erase α, x β (s β) else 0

/-- Player `α`'s perturbed best response `B̃^α(x^{−α}) = C^α(U^α(x^{−α}))` (p. 10), where
`C^α = choiceProb (f α)` is the choice function of the shock density `f α`. -/
noncomputable def pbr {p : ℕ} {n : Fin p → ℕ} (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) (x : Mixed n) (α : Fin p) : Fin (n α) → ℝ :=
  choiceProb (f α) (payoffVec u x α)

/-- The vector field of the perturbed best response dynamic
`(P) ẋ^α = B̃^α(x^{−α}) − x^α` (p. 11), on the ambient space. -/
noncomputable def pField {p : ℕ} {n : Fin p → ℕ} (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) : Mixed n → Mixed n :=
  fun x α => pbr f u x α - x α

/-- The vector field of the deterministically perturbed best response dynamic
`(PV) ẋ^α = argmax_{y ∈ int(∆S^α)} (y · U^α(x^{−α}) − V^α(y)) − x^α` (p. 14), with the argmax
supplied as the map `Ct α` (see `IsPerturbedArgmax`). -/
noncomputable def pvField {p : ℕ} {n : Fin p → ℕ}
    (Ct : (α : Fin p) → (Fin (n α) → ℝ) → (Fin (n α) → ℝ))
    (u : (α : Fin p) → Profile n → ℝ) : Mixed n → Mixed n :=
  fun x α => Ct α (payoffVec u x α) - x α

/-- The standard basis vector `e_i` of the smallest maximizer `i` of `v`: coordinate `i` is `1`
iff `v i` is maximal and every smaller index has a strictly smaller value, else `0`. For
`k ≥ 1` exactly one coordinate is `1` (argmax with ties broken by the smallest index). -/
noncomputable def argmaxVec {k : ℕ} (v : Fin k → ℝ) : Fin k → ℝ :=
  fun i => if (∀ j, v j ≤ v i) ∧ (∀ j, j < i → v j < v i) then 1 else 0

/-- The mixed-strategy representation `(e_{s^1}, …, e_{s^p})` of a pure profile `s`. -/
noncomputable def pureVec {p : ℕ} {n : Fin p → ℕ} (s : Profile n) : Mixed n :=
  fun α => Pi.single (s α) (1 : ℝ)

/-- The pure strategies chosen at time `t + 1` in standard SFP, (12) (p. 10), as basis vectors:
player `α` plays the (smallest) maximizer of `U^α_k(z^{−α}) + (ε^α_t)_k`, given beliefs `z`
and the time-`t` shocks `εt`. -/
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

end StochFictPlay.Potential


