-- Prove2me | Definitions.Def_MDPFinance_Semicontinuous_Operators
-- name    : MDPFinance_Semicontinuous_Operators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:25:04.733805+00:00
-- url     : https://prove2.me/theorems/17f56879-0a49-4814-a764-43acfce187b6
-- title:
--   The operators $L_n$, $T_n^f$, $T_n$, and maximizers of $v$
-- statement:
--   For $v \in \mathrm{IM}(E)$ (a measurable function $E \to [-\infty,\infty)$), define the
--   one-step operators
--   $$
--   L_n v(x,a) := r_n(x,a) + \int v(x')\, Q_n(dx' \mid x,a), \qquad
--   T_n^f v(x) := L_n v(x, f(x)), \qquad
--   T_n v(x) := \sup_{a \in D_n(x)} L_n v(x,a).
--   $$
--   A decision rule $f$ is a **maximizer** of $v$ at time $n$ (Definition 2.3.6) if
--   $T_n^f v = T_n v$, i.e. $f(x)$ attains the supremum defining $T_n v(x)$ at every $x$.
--
--   Every theorem in this mission is about when $T_n$ preserves a regularity class (upper
--   semicontinuity, continuity, or plain measurability) and when a maximizer of $v$ is guaranteed
--   to exist — the two questions the Structure Assumption (SAN) packages together.
--
--   **Formalization Note.** Restated from `MDPFinance.Bellman.IM`/`erealIntegral`/`L`/`T`/`Tf`/
--   `IsMaximizer` (chunk `02a`), identically; see that chunk's `MODERATION_NOTES.md` for the
--   $\infty - \infty$ convention built into `erealIntegral`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 20-21, Definition 2.3.1 and Definition 2.3.6

import Mathlib
import Definitions.Def_MDPFinance_Semicontinuous_Model
import Definitions.Def_MDPFinance_Semicontinuous_Policy

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Semicontinuous

/-- `IM E` (Bäuerle–Rieder p. 19, PDF 34): the measurable functions `E → [-∞, ∞)`. Restated
from `MDPFinance.Bellman.IM` (chunk `02a`). -/
def IM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

/-- The integral `∫ v dμ ∈ [-∞,∞)` of an extended-real-valued function `v ≠ ⊤`, against a
measure `μ`. Restated from `MDPFinance.Bellman.erealIntegral` (chunk `02a`); see that chunk's
`MODERATION_NOTES.md` for the convention (`⊤ + (-⊤) = ⊥` for an a priori `∞ - ∞`). -/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- The operator `L_n` (Bäuerle–Rieder, Definition 2.3.1a, p. 20, PDF 34):
`(L_n v)(x,a) := r_n(x,a) + ∫ v(x') Q_n(dx'|x,a)`. -/
noncomputable def L (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (xa : E × A) :
    EReal :=
  (M.r n xa : EReal) + erealIntegral (M.Q n xa) v

/-- The maximal reward operator `T_n` (Bäuerle–Rieder, Definition 2.3.1c, p. 20, PDF 34):
`(T_n v)(x) := sup_{a ∈ D_n(x)} (L_n v)(x,a)`. -/
noncomputable def T (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx n x, L M n v (x, a)

/-- The operator `T_n^f` (Bäuerle–Rieder, Definition 2.3.1b, p. 20, PDF 34):
`(T_n^f v)(x) := (L_n v)(x, f(x))`. -/
noncomputable def Tf (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (f : E → A) (x : E) :
    EReal :=
  L M n v (x, f x)

/-- `f` is a maximizer of `v` at time `n` (Bäuerle–Rieder, Definition 2.3.6, p. 21, PDF 36):
a decision rule at time `n` with `T_n^f v = T_n v`. -/
def IsMaximizer (M : MarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (f : E → A) : Prop :=
  IsDecisionRule M n f ∧ Tf M n v f = T M n v

end MDPFinance.Semicontinuous


