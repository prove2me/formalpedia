-- Prove2me | Definitions.Def_MDPFinance_Stationary_Operators
-- name    : MDPFinance_Stationary_Operators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:43:19.064425+00:00
-- url     : https://prove2.me/theorems/96780412-c714-4e37-8414-670e0600f7d6
-- title:
--   Definition 2.5.2's operators $L$, $T^f$, $T$ and maximizers
-- statement:
--   As in Definition 2.3.1, define for $v \in \mathrm{I\!M}(E)$: $(Lv)(x,a) := r(x,a) + \beta
--   \int v(x')\,Q(dx' \mid x,a)$, $(T^f v)(x) := (Lv)(x,f(x))$, $(Tv)(x) := \sup_{a \in D(x)}
--   (Lv)(x,a)$ ($T$ the **maximal reward operator**). $f$ is a **maximizer** of $v$ if $T^f v =
--   Tv$ pointwise.
--
--   **Formalization Note.** Identical in shape to chunk `02a`'s non-stationary operators, minus
--   the time index and with the single discount factor $\beta$ folded directly into $L$
--   (matching the book's own single-$\beta$ stationary convention rather than the non-stationary
--   $r_n := \beta^n r$ used to derive it).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 40, PDF 55, Definition 2.5.2 (operators)

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- `IM E` (Bäuerle–Rieder p. 19, PDF 34): the measurable functions `E → [-∞, ∞)`. Restated,
identically, from `MDPFinance.Bellman.IM` (chunk `02a`)/`MDPFinance.Semicontinuous.IM`
(chunk `02b`)/`MDPFinance.StructuredModels.IM` (chunk `02c`). -/
def IM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

/-- The integral `∫ v dμ ∈ [-∞,∞)` of an extended-real-valued function `v ≠ ⊤`, against a
measure `μ`. Restated, identically, from `MDPFinance.Bellman.erealIntegral` (chunk `02a`); see
that chunk's `MODERATION_NOTES.md` for the convention (`⊤ + (-⊤) = ⊥` for an a priori `∞ - ∞`).
-/
noncomputable def erealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E) (v : E → EReal) :
    EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The operator `L` (Bäuerle–Rieder, p. 40, PDF 55, "as in Definition 2.3.1"):
`(Lv)(x,a) := r(x,a) + β ∫ v(x') Q(dx'|x,a)`. -/
noncomputable def L (M : StationaryMarkovDecisionModel E A) (v : E → EReal) (xa : E × A) :
    EReal :=
  (M.r xa : EReal) + (M.β : EReal) * erealIntegral (M.Q xa) v

/-- The maximal reward operator `T` (Bäuerle–Rieder, p. 40, PDF 55):
`(Tv)(x) := sup_{a ∈ D(x)} (Lv)(x,a)`. -/
noncomputable def T (M : StationaryMarkovDecisionModel E A) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx x, L M v (x, a)

/-- The operator `T^f` (Bäuerle–Rieder, p. 40, PDF 55): `(T^f v)(x) := (Lv)(x, f(x))`. -/
noncomputable def Tf (M : StationaryMarkovDecisionModel E A) (v : E → EReal) (f : E → A) (x : E) :
    EReal :=
  L M v (x, f x)

/-- `f` is a maximizer of `v` (Bäuerle–Rieder, p. 41, Structure Assumption (SAN)(iii)):
`T^f v(x) = Tv(x)` for all `x`. -/
def IsMaximizer (M : StationaryMarkovDecisionModel E A) (v : E → EReal) (f : E → A) : Prop :=
  IsDecisionRule M f ∧ Tf M v f = T M v

end MDPFinance.Stationary


