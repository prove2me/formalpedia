-- Prove2me | Definitions.Def_SingularCardinals_basic
-- name    : SingularCardinals_basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T14:47:22.224337+00:00
-- url     : https://prove2.me/theorems/2c96d0bf-fc6a-4780-a694-290689971715
-- title:
--   GCH and the two forms of the singular cardinals hypothesis
-- statement:
--   Three cardinal-arithmetic hypotheses, stated for cardinals $\kappa$ of a fixed universe. Write $\kappa^+$ for the successor cardinal of $\kappa$ and $\operatorname{cf}\kappa$ for its cofinality. A cardinal $\kappa$ is **singular** if it is infinite and $\operatorname{cf}\kappa<\kappa$; it is a **strong limit** if $\kappa\neq 0$ and $2^\lambda<\kappa$ for every $\lambda<\kappa$.
--
--   1. **GCH** (generalized continuum hypothesis): for every infinite cardinal $\kappa$,
--   $$2^\kappa=\kappa^+.$$
--   2. **SCH** (singular cardinals hypothesis, in the form quoted from Mitchell 1992): for every singular strong limit cardinal $\kappa$,
--   $$2^\kappa=\kappa^+.$$
--   3. **SCH$_2$** (second form): for every singular cardinal $\kappa$,
--   $$2^{\operatorname{cf}\kappa}<\kappa\ \Longrightarrow\ \kappa^{\operatorname{cf}\kappa}=\kappa^+.$$
--
--   These are the hypotheses compared throughout the mission: GCH implies SCH, and the second form implies the first.
--
--   **Formalization Note** Singularity is Mathlib's `Cardinal.IsSingular` (infinite and not regular), cofinality is `κ.ord.cof`, strong limit is Mathlib's `Cardinal.IsStrongLimit` (which counts $\aleph_0$ as a strong limit, harmless here since $\aleph_0$ is regular), and $\kappa^+$ is `Order.succ κ`. The second form reuses the published predicate `JechSetTheory.SCHAt` from `Def_JechStationary`.
-- source:
--   Wikipedia, "Singular cardinals hypothesis", revision oldid=1349753131, https://en.wikipedia.org/w/index.php?title=Singular_cardinals_hypothesis&oldid=1349753131, lead section (first form, quoting Mitchell 1992) and paragraph "Another form of the SCH"; GCH as mentioned in the lead section.

import Mathlib
import Definitions.Def_JechStationary

universe u

namespace SingularCardinals

open Cardinal

/-- The generalized continuum hypothesis: `2 ^ κ = κ⁺` for every infinite cardinal `κ`. -/
def GCH : Prop := ∀ κ : Cardinal.{u}, ℵ₀ ≤ κ → 2 ^ κ = Order.succ κ

/-- The singular cardinals hypothesis, first form (Mitchell 1992): for every singular strong
limit cardinal `κ`, `2 ^ κ = κ⁺`. -/
def SCH : Prop :=
  ∀ κ : Cardinal.{u}, κ.IsSingular → IsStrongLimit κ → 2 ^ κ = Order.succ κ

/-- The singular cardinals hypothesis, second form: for every singular cardinal `κ`,
`2 ^ cf κ < κ` implies `κ ^ cf κ = κ⁺` (this is `JechSetTheory.SCHAt κ` for every `κ`). -/
def SCH₂ : Prop := ∀ κ : Cardinal.{u}, JechSetTheory.SCHAt κ

end SingularCardinals


