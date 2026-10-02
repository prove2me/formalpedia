-- Prove2me | Definitions.Def_MDPFinance_Stationary_Model
-- name    : MDPFinance_Stationary_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:41:15.210061+00:00
-- url     : https://prove2.me/theorems/b5b7bc75-c77e-4b7d-bbe4-24f9e36a79dd
-- title:
--   A stationary Markov Decision Model
-- statement:
--   A **stationary Markov Decision Model** is a Markov Decision Model (Definition 2.1.1) whose
--   data $(E, A, D, Q, r, g)$ does not depend on the stage $n$: the reward at absolute time $n$
--   is $\beta^n r$ and the terminal reward at time $N$ is $\beta^N g$, for a fixed discount
--   factor $\beta \in (0,1]$. $D(x) := \{a \in A : (x,a) \in D\}$.
--
--   **Formalization Note.** This is the time-homogeneous specialization the book introduces at
--   the start of §2.5; it is a distinct Lean structure from `MDPFinance.Bellman.MarkovDecisionModel`
--   (chunk `02a`)'s non-stationary model, not a special case of it in Lean (both are used in this
--   chunk: the stationary one throughout §2.5-2.6.2, and a restated non-stationary one,
--   `NSMarkovDecisionModel`, for the explicitly non-stationary LQ example of §2.6.3).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 39-40, PDF 54-55, §2.5 introduction (unnumbered)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- A stationary Markov Decision Model (Bäuerle–Rieder, p. 39-40, PDF 54-55, intro to §2.5): the
data `(E, A, D, Q, r, g)` does not depend on the stage `n`; the reward at time `n` is `β^n r` and
the terminal reward at time `N` is `β^N g`, for a discount factor `β ∈ (0,1]`. -/
structure StationaryMarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  /-- `D ⊆ E × A`, the admissible state-action pairs. -/
  D : Set (E × A)
  hD_meas : MeasurableSet D
  /-- `D` contains the graph of a measurable decision rule. -/
  hD_sel : ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D
  /-- The (time-homogeneous) transition kernel `Q(·|x,a)`. -/
  Q : Kernel (E × A) E
  hQ_prob : ∀ xa, IsProbabilityMeasure (Q xa)
  /-- The one-stage reward `r(x,a)`. -/
  r : E × A → ℝ
  hr_meas : Measurable r
  /-- The one-stage terminal/holding reward `g(x)`. -/
  g : E → ℝ
  hg_meas : Measurable g
  /-- The discount factor `β ∈ (0,1]`. -/
  β : ℝ
  hβ_pos : 0 < β
  hβ_le_one : β ≤ 1

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- `D(x) = {a ∈ A | (x,a) ∈ D}`, the admissible actions in state `x`. -/
def StationaryMarkovDecisionModel.Dx (M : StationaryMarkovDecisionModel E A) (x : E) : Set A :=
  {a | (x, a) ∈ M.D}

end MDPFinance.Stationary


