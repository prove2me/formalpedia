-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_Operators
-- name    : MDPFinance_StructuredModels_Operators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:35:30.059899+00:00
-- url     : https://prove2.me/theorems/9c9f7136-820d-4757-a120-a597d4182bd5
-- title:
--   The Bellman operators $L_n$, $T_n$, $T_n^f$ and maximizers (restated)
-- statement:
--   For a Markov Decision Model $M$, define $(L_n v)(x,a) := r_n(x,a) + \int v(x')\,Q_n(dx'\mid
--   x,a)$, $(T_n v)(x) := \sup_{a \in D_n(x)} (L_n v)(x,a)$, and $(T_n^f v)(x) := (L_n v)(x,f(x))$
--   for a decision rule $f$. A decision rule $f_n$ at time $n$ is a **maximizer** of $v$ if
--   $T_n^{f_n} v = T_n v$ pointwise.
--
--   **Formalization Note.** Restated from `MDPFinance.Bellman`'s identically-named definitions
--   (chunk `02a`), including the `EReal`-valued integral convention `⊤ + (-⊤) := ⊥`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 20-21, Definition 2.3.1/2.3.6

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

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

end MDPFinance.StructuredModels


