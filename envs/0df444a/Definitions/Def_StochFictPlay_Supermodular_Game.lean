-- Prove2me | Definitions.Def_StochFictPlay_Supermodular_Game
-- name    : StochFictPlay_Supermodular_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:15:40.723985+00:00
-- url     : https://prove2.me/theorems/ac3fc0fa-53ba-45a7-84c8-1e51d90b1d71
-- title:
--   Finite normal form game, payoff vectors, perturbed best responses, the dynamic (P), and strict supermodularity
-- statement:
--   A $p$ player normal form game has players $\alpha \in \{0,\dots,p-1\}$; player $\alpha$ has the ordered strategy set $S^\alpha = \{0,\dots,n^\alpha - 1\}$ and a utility function $u^\alpha : S \to \mathbb R$ on pure profiles $S = \prod_\beta S^\beta$.
--
--   1. **Mixed profiles.** $\Delta S^\alpha$ is the probability simplex on $S^\alpha$ and $\Sigma = \prod_\beta \Delta S^\beta$.
--   2. **Payoff vector.** For a mixed profile $x$, player $\alpha$'s payoff vector $U^\alpha(x^{-\alpha}) \in \mathbb R^{n^\alpha}$ has entries
--   $$U^\alpha_i(x^{-\alpha}) = \sum_{s \in S,\ s^\alpha = i} u^\alpha(s) \prod_{\beta \ne \alpha} x^\beta_{s^\beta}.$$
--   3. **Perturbed best response.** Given shock densities $f^\alpha$ with choice functions $C^\alpha$, $\tilde B^\alpha(x^{-\alpha}) = C^\alpha(U^\alpha(x^{-\alpha}))$.
--   4. **The dynamic (P).** $\dot x^\alpha = \tilde B^\alpha(x^{-\alpha}) - x^\alpha$ for every player $\alpha$.
--   5. **Strict supermodularity.** $G$ is (strictly) supermodular if for all distinct players $\alpha \ne \beta$ and all profiles $s, \hat s$ with $s^\alpha > \hat s^\alpha$ and $s^{-\alpha} = \hat s^{-\alpha}$, the difference $u^\alpha(s) - u^\alpha(\hat s)$ is strictly increasing in the common strategy $s^\beta = \hat s^\beta$.
--
--   Strict supermodularity expresses strategic complementarity: the gain from moving to a higher strategy grows when any opponent moves to a higher strategy.
--
--   **Formalization Note** Players and strategies are 0-based (the paper uses $\{1,\dots,n^\alpha\}$ in the same order). Mixed profiles live in the ambient space $\prod_\alpha \mathbb R^{n^\alpha}$, where the payoff vector, $\tilde B$ and the field of (P) are defined everywhere; $U^\alpha$ ignores the coordinate $x^\alpha$. In supermodularity the pair $s, \hat s$ is written as $s$ with player $\alpha$'s strategy set to $i > i'$ and player $\beta$'s strategy set to $k$.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 9 (normal form game, payoff vectors), p. 10 (perturbed best response), p. 11 (dynamic (P)), pp. 18-19 (definition of a (strictly) supermodular game)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel

open MeasureTheory
open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Pure strategy profiles `S = ∏_β S^β` of a `p`-player game in which player `α` has the
strategies `Fin (n α)` (the paper's `{1, …, n^α}`, 0-based here, in the same order);
manuscript p. 9. -/
abbrev Profile {p : ℕ} (n : Fin p → ℕ) := (α : Fin p) → Fin (n α)

/-- The ambient space `∏_α ℝ^{n^α}` in which mixed strategy profiles live. -/
abbrev Mixed {p : ℕ} (n : Fin p → ℕ) := (α : Fin p) → Fin (n α) → ℝ

/-- The mixed strategy profiles `Σ = ∏_β ∆S^β` (p. 9). -/
def mixedProfiles {p : ℕ} (n : Fin p → ℕ) : Set (Mixed n) :=
  {x | ∀ α, x α ∈ stdSimplex ℝ (Fin (n α))}

/-- Player `α`'s payoff vector (p. 9):
`U^α_{s^α}(x^{−α}) = ∑_{s^{−α}} u^α(s^α, s^{−α}) ∏_{β ≠ α} x^β_{s^β}`. It is written as a sum
over full profiles `s` with `s α = i` (each opponent profile counted once), and does not depend
on `x α`. -/
noncomputable def payoffVec {p : ℕ} {n : Fin p → ℕ} (u : (α : Fin p) → Profile n → ℝ)
    (x : Mixed n) (α : Fin p) : Fin (n α) → ℝ :=
  fun i => ∑ s : Profile n,
    if s α = i then u α s * ∏ β ∈ Finset.univ.erase α, x β (s β) else 0

/-- Player `α`'s perturbed best response `B̃^α(x^{−α}) = C^α(U^α(x^{−α}))` (p. 10), where
`C^α = choiceProb (f α)` is the choice function of player `α`'s shock density `f α`. -/
noncomputable def pbr {p : ℕ} {n : Fin p → ℕ} (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) (x : Mixed n) (α : Fin p) : Fin (n α) → ℝ :=
  choiceProb (f α) (payoffVec u x α)

/-- The vector field of the perturbed best response dynamic
`(P) ẋ^α = B̃^α(x^{−α}) − x^α` (p. 11), on the ambient space. -/
noncomputable def pField {p : ℕ} {n : Fin p → ℕ} (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞)
    (u : (α : Fin p) → Profile n → ℝ) : Mixed n → Mixed n :=
  fun x α => pbr f u x α - x α

/-- (Strictly) supermodular game (manuscript pp. 18–19): for all distinct players `α ≠ β` and
all profiles `s`, `ŝ` with `s^α > ŝ^α` and `s^{−α} = ŝ^{−α}`, the difference `u^α(s) − u^α(ŝ)`
is strictly increasing in `s^β = ŝ^β`. Here `s^α = i`, `ŝ^α = i'` with `i' < i`, the common
opponent coordinates are those of an arbitrary profile `s`, and `k` is the common strategy of
player `β`. -/
def IsStrictlySupermodular {p : ℕ} {n : Fin p → ℕ} (u : (α : Fin p) → Profile n → ℝ) : Prop :=
  ∀ α β : Fin p, α ≠ β → ∀ (s : Profile n) (i i' : Fin (n α)), i' < i →
    StrictMono (fun k : Fin (n β) =>
      u α (Function.update (Function.update s α i) β k) -
        u α (Function.update (Function.update s α i') β k))

end StochFictPlay.Supermodular


