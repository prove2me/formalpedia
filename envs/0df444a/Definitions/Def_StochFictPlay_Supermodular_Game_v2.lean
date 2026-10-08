-- Prove2me | Definitions.Def_StochFictPlay_Supermodular_Game_v2
-- name    : StochFictPlay_Supermodular_Game_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:35:04.464413+00:00
-- url     : https://prove2.me/theorems/fb72d984-75f1-4e04-b800-d46707158e65
-- title:
--   Normal form game, payoff vectors, perturbed best response dynamic (P) and strictly supermodular games (re-issued over the corrected choice model)
-- statement:
--   A $p$-player normal form game in which player $\alpha$ has strategies $0,\dots,n^\alpha-1$ (p. 9): pure profiles $S = \prod_\beta S^\beta$, the ambient space $\prod_\alpha \mathbb R^{n^\alpha}$ of mixed profiles and the mixed profiles $\Sigma = \prod_\beta \Delta S^\beta$; player $\alpha$'s payoff vector $U^\alpha_i(x^{-\alpha}) = \sum_{s^{-\alpha}} u^\alpha(i, s^{-\alpha}) \prod_{\beta \ne \alpha} x^\beta_{s^\beta}$; the perturbed best response $\tilde B^\alpha(x^{-\alpha}) = C^\alpha(U^\alpha(x^{-\alpha}))$ (p. 10) with $C^\alpha$ the choice function of player $\alpha$'s shock density; the vector field of the perturbed best response dynamic (P) $\dot x^\alpha = \tilde B^\alpha(x^{-\alpha}) - x^\alpha$ (p. 11); and (strictly) supermodular games (pp. 18–19): for all $\alpha \ne \beta$, all profiles and all $s^\alpha > \hat s^\alpha$ with $s^{-\alpha} = \hat s^{-\alpha}$, $u^\alpha(s) - u^\alpha(\hat s)$ is strictly increasing in the common strategy $s^\beta = \hat s^\beta$.
--
--   **Formalization Note.** Verbatim re-issue of `StochFictPlay_Supermodular_Game` whose only change is that it is built on `StochFictPlay_Supermodular_ChoiceModel_v2`, so that the whole definition chain uses the corrected `IsRegularDensity` (continuous strictly positive shock densities). No declaration changed.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 9 (normal form game, payoff vectors), p. 10 (perturbed best response), p. 11 (dynamic (P)), pp. 18-19 (definition of a (strictly) supermodular game)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel_v2

open MeasureTheory
open scoped ENNReal

/-! Re-issue of `Def_StochFictPlay_Supermodular_Game` on top of the corrected
`Def_StochFictPlay_Supermodular_ChoiceModel_v2` (continuous strictly positive shock densities).
The declarations below are unchanged. -/

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


