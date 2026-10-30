-- Prove2me | Definitions.Def_RoslingAssembly_Admissible
-- name    : RoslingAssembly_Admissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:40:03.556696+00:00
-- url     : https://prove2.me/theorems/852d27d6-24ed-44d8-8dea-168ae722331e
-- title:
--   Policy with finite discounted cost
-- statement:
--   A policy has **finite discounted cost** at discount factor $\beta$ if every period cost $c_t$ is integrable and
--   $$\sum_{t\ge1}\beta^{t-1}\,\mathbb E|c_t|<\infty .$$
--   For such policies the objective $\mathbb E\{\sum_t\beta^{t-1}c_t\}$ of (2) is a well-defined real number and equals $\sum_t\beta^{t-1}\mathbb E[c_t]$.
--
--   **Formalization Note** The sum over periods is indexed by $n\in\mathbb N$ with period $t=n+1$; expectations are under the i.i.d. demand law.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 567, Problem P, (2)

import Mathlib
import Definitions.Def_RoslingAssembly_periodCost
import Definitions.Def_RoslingAssembly_pathMeasure
open MeasureTheory

namespace RoslingAssembly

/-- **Policy with finite discounted cost** (p. 567, (2)). Rosling, *Optimal Inventory Policies
for Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 567, Problem P:
"Min_Y E{ Σ_{t=1}^∞ α^{t−1} ( … ) } + constant (2)".

`Admissible net ℓ H p μ Yh pol β` says that the discounted cost (2) of `pol` at discount factor
`β` is a well-defined finite number: every period's cost `c_t` is integrable under the demand
law, and `Σ_{t≥1} β^{t−1} E|c_t| < ∞`. Then
`E{Σ_t β^{t−1} c_t} = Σ_t β^{t−1} E[c_t]`, and both are finite.

**Formalization Note.** The sum over periods is indexed by `n : ℕ` with paper period `t = n + 1`
(discount `β^{t−1} = β^n`). Expectations are over `pathMeasure μ`, the i.i.d. demand law. -/
def Admissible {N : ℕ} [NeZero N] (net : Network N) (ℓ : Fin N → ℕ) (H : Fin N → ℝ) (p : ℝ)
    (μ : Measure ℝ) (Yh : ℤ → Fin N → ℝ) (pol : ℕ → (ℕ → ℝ) → Fin N → ℝ) (β : ℝ) : Prop :=
  (∀ n : ℕ, Integrable (fun ω => periodCost net ℓ H p μ Yh pol β ω ((n : ℤ) + 1))
      (pathMeasure μ)) ∧
    Summable (fun n : ℕ =>
      β ^ n * ∫ ω, |periodCost net ℓ H p μ Yh pol β ω ((n : ℤ) + 1)| ∂(pathMeasure μ))

end RoslingAssembly


