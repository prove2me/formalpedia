-- Prove2me | Definitions.Def_WassChanceCvx_unsafeDist
-- name    : WassChanceCvx_unsafeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:42.717348+00:00
-- url     : https://prove2.me/theorems/5e4813e6-bb49-491d-9b56-121e3349cb28
-- title:
--   Distance $d(\zeta,\mathcal S^c(x))$ to the unsafe set
-- statement:
--   For rows $a$ and right-hand side $\beta$ as in `safeSet`, and $\zeta\in E$,
--
--   $$
--   d\bigl(\zeta,\mathcal S^c\bigr)=\inf\bigl\{\|\zeta-\xi\|:\ \xi\in E,\ \xi\notin\mathcal S(a,\beta)\bigr\}\in[0,\infty].
--   $$
--
--   With $a=A(x)$, $\beta=b(x)$ this is the distance from $\zeta$ to the unsafe set $\mathcal S^c(x)$, whose conditional value-at-risk characterizes $\mathcal X^p$ (Proposition 1).
--
--   **Formalization Note** The infimum is over all of $E$ ($\Xi=\mathbb R^q$) and is Mathlib's extended distance `Metric.infEDist`, so the distance to an empty unsafe set is $+\infty$, not $0$.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Proposition 1, p.6 (display defining d)

import Mathlib
import Definitions.Def_WassChanceCvx_safeSet

namespace WassChanceCvx

/-- **Distance to the unsafe set, `d(ζ, 𝒮ᶜ(x))`.**
Shen, Jiang, arXiv:2111.02486v2, p.6: "`d(ζ, 𝒮ᶜ(x))` represents the distance from `ζ` to the
"unsafe" set `𝒮ᶜ(x)` [CKW18], `d(ζ, 𝒮ᶜ(x)) := inf_{ξ∈Ξ}{‖ζ − ξ‖ : A(x)ξ ≰ b(x)}`, and `Ξ` is the
support of `ξ`."

`unsafeDist a β ζ = inf{‖ζ − ξ‖ : ξ ∈ E, ξ ∉ safeSet a β}` in `[0, ∞]`.

**Formalization Note.** The infimum ranges over all of `E` (`Ξ = ℝ^q`). It is
`Metric.infEDist`, valued in `[0, ∞]`, so the distance to an empty unsafe set is `+∞` (and not
the junk `0` of `Metric.infDist`). -/
noncomputable def unsafeDist {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (a : Fin k → StrongDual ℝ E) (β : Fin k → ℝ) (ζ : E) : ENNReal :=
  Metric.infEDist ζ (safeSet a β)ᶜ

end WassChanceCvx


