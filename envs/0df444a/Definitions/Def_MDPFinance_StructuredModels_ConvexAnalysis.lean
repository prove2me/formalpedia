-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis
-- name    : MDPFinance_StructuredModels_ConvexAnalysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:32:21.947504+00:00
-- url     : https://prove2.me/theorems/a85df1f1-8440-48b7-8a26-1ca69e211978
-- title:
--   Convexity and concavity of $\mathrm{EReal}$-valued functions
-- statement:
--   For a real vector space $E$, a set $s \subseteq E$ and $f : s \to \overline{\mathbb{R}}$
--   ($\mathrm{EReal}$-valued): $f$ is **convex on $s$** if $s$ is convex and $f(\alpha x + \beta y)
--   \leq \alpha f(x) + \beta f(y)$ for all $x,y \in s$, $\alpha,\beta \geq 0$, $\alpha+\beta=1$
--   (with $\alpha, \beta$ cast into $\mathrm{EReal}$ before multiplying); $f$ is **concave on $s$**
--   if the reverse inequality holds.
--
--   **Formalization Note.** Mathlib's `ConvexOn`/`ConcaveOn` require a `Module ℝ` structure on the
--   codomain, which `EReal` (needed since value functions may be $-\infty$) does not have; this
--   definition restates the same inequality using `EReal`'s own multiplication in place of scalar
--   multiplication.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 36-38, PDF 51-53 (convexity/concavity used throughout §2.4.4 without a numbered definition)

import Mathlib

namespace MDPFinance.StructuredModels

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- `f` is convex on `s` (Bäuerle–Rieder uses ordinary convexity/concavity of real- and
`EReal`-valued functions throughout §2.4.4-2.4.5 without stating a numbered definition). Mathlib's
`ConvexOn` requires a `Module ℝ β` on the codomain, which `EReal` does not have (no `SMul ℝ EReal`
instance, since `EReal` is not a vector space); this restates the same defining inequality with
real scalars cast into `EReal` and multiplied there (`EReal` does carry a `Mul`), matching how
this chunk's other definitions already treat `EReal` arithmetic (see `MODERATION_NOTES.md`). -/
def ConvexOnEReal (s : Set E) (f : E → EReal) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y

/-- `f` is concave on `s`, the `EReal`-valued analogue of `ConcaveOn`; see `ConvexOnEReal`. -/
def ConcaveOnEReal (s : Set E) (f : E → EReal) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    (a : EReal) * f x + (b : EReal) * f y ≤ f (a • x + b • y)

end MDPFinance.StructuredModels


