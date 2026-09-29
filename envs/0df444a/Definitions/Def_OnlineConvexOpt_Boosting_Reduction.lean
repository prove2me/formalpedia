-- Prove2me | Definitions.Def_OnlineConvexOpt_Boosting_Reduction
-- name    : OnlineConvexOpt_Boosting_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T17:34:07.400098+00:00
-- url     : https://prove2.me/theorems/d3d780ae-c433-49e1-9c9e-69f47971e38d
-- title:
--   γ-weak learnability, the simplex, and the boosting-to-OCO reduction (Algorithm 34)
-- statement:
--   Three declarations. `IsGammaWeaklyLearnable` formalizes Definition 11.1 (p. 186): the
--   concept class `H` is `γ`-weakly-learnable if there is an algorithm returning, with
--   probability `1-δ` for any `δ`, a hypothesis with error at most `1/2-γ`, given enough
--   samples. `Simplex m` is the `m`-dimensional probability simplex $\Delta_m$ (p. 188), the
--   decision set of the reduction's OCO sub-algorithm. `IsBoostingRun S A T Prob h r p hbar`
--   formalizes Algorithm 34 (p. 189): uniform initial distribution `p_1`; at each round, the
--   `{0,1}`-valued cost vector `r_t` records whether the weak learner's round-`t` hypothesis
--   `h_t` (random) errs on each example; `p_{t+1}` is the OCO algorithm's update on the
--   realized cost sequence; and `hbar` is the majority-vote output
--   $\bar h(x) = \mathrm{sign}(\sum_{t=1}^T h_t(x))$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 186, Definition 11.1 (PDF p. 208); p. 188-189, Algorithm 34 (PDF p. 210-211)

import Mathlib

open MeasureTheory

namespace OnlineConvexOpt.Boosting

variable {X : Type*} {m : ℕ}

/-- Definition 11.1 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 186, PDF p. 208). The concept class `H` is `γ`-weakly-learnable if there
is an algorithm `W` accepting a sample `S_m = {(x,y)}` and returning `W(S_m) ∈ H` such that: for
any `δ > 0` there is `m = m(δ)` large enough that for any distribution `D` over pairs `(x,y)`
with `y = h⋆(x)` and `m` samples from `D`, with probability `1-δ`, `error(W(S_m)) ≤ 1/2 - γ`. -/
def IsGammaWeaklyLearnable {Ω : Type*} [MeasurableSpace Ω]
    (GeneralizationError : (X → ℝ) → ℝ) (γ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ W : Ω → (X → ℝ), ∀ Prob : Measure Ω, IsProbabilityMeasure Prob →
    (1 - δ : ℝ) ≤ (Prob {ω | GeneralizationError (W ω) ≤ 1 / 2 - γ}).toReal

/-- The `m`-dimensional probability simplex, `Δ_m` (Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 188, PDF p. 210): the decision set of the
boosting reduction's OCO algorithm. -/
def Simplex (m : ℕ) : Set (Fin m → ℝ) := {q | (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1}

/-- `IsBoostingRun S A γ T Prob h r p hbar` formalizes Algorithm 34 (p. 189, PDF p. 211), the
reduction from boosting to online convex optimization: `p 1` is the uniform distribution over
the sample `S` (indices `1..m`); at every round `t`, `r t ω i` is the round-`t` `{0,1}`-valued
cost vector recording whether `h t ω` (the weak learner's round-`t` call, a random hypothesis)
errs on example `i` (`f_t(p) = r_t^\top p`); `p (t+1) ω` is `A_OCO`'s update on the realized
cost sequence; and `hbar` is the majority-vote output `h̄(x) = \mathrm{sign}(∑_{t=1}^T h_t(x))`.
Indexed from round `1`, matching the book's own `t ∈ [T]`. -/
def IsBoostingRun (S : Fin m → X × ℝ) (A : (ℕ → (Fin m → ℝ) → ℝ) → ℕ → (Fin m → ℝ)) (T : ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    (h : ℕ → Ω → X → ℝ) (r : ℕ → Ω → Fin m → ℝ) (p : ℕ → Ω → Fin m → ℝ)
    (hbar : Ω → X → ℝ) : Prop :=
  (∀ ω : Ω, p 1 ω = fun _ => 1 / (m : ℝ)) ∧
  (∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ ω : Ω, p t ω ∈ Simplex m) ∧
  (∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ ω : Ω, ∀ i : Fin m,
    r t ω i = if h t ω (S i).1 = (S i).2 then (1 : ℝ) else 0) ∧
  (∀ t : ℕ, 1 ≤ t → t < T → ∀ ω : Ω,
    p (t + 1) ω = A (fun τ q => ∑ i : Fin m, r τ ω i * q i) (t + 1)) ∧
  (∀ ω : Ω, hbar ω = fun x => if 0 ≤ ∑ t ∈ Finset.Icc 1 T, h t ω x then (1 : ℝ) else -1)

end OnlineConvexOpt.Boosting


