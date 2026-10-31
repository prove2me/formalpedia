-- Prove2me | Definitions.Def_FDivToolkit_Cond7
-- name    : FDivToolkit_Cond7
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:01.508257+00:00
-- url     : https://prove2.me/theorems/3745cf7f-fd55-4a12-825b-4a0a61b26ddf
-- title:
--   Condition (7)
-- statement:
--   Condition (7) says that for all $\alpha\in(0,\infty)$ there exists $\epsilon>0$ such that
--   $$
--   \limsup_{|x|\to\infty}|x|^{2+\epsilon}\exp\!\big(H^{-1}(\alpha|x|)\big)f(x)<\infty.
--   $$
--
--   It is a pointwise tail condition that is easier to check than (5).
--
--   **Formalization Note** The limit $|x|\to\infty$ is the filter `cocompact ℝ`, and the finite lim sup is an eventual bound by a constant $C$.
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), display (7), Lemma 2, p.9, and footnote 8

import Definitions.Def_FDivToolkit_IsAdmissibleH

open Filter

namespace FDivToolkit

/-- Condition (7), Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Lemma 2, p.9: for all
`α ∈ (0, ∞)` there exists `ϵ > 0` such that
`lim sup_{|x|→∞} |x|^{2+ϵ} exp(H⁻¹(α|x|)) f(x) < ∞`.

**Formalization Note.** `|x| → ∞` is "the pair of limits `x → ∞` and `x → −∞`" (footnote 8), which is
the filter `cocompact ℝ`. The lim sup of this nonnegative quantity is finite exactly when it is
eventually bounded by a constant `C`. -/
def Cond7 (H f : ℝ → ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ ϵ : ℝ, 0 < ϵ ∧ ∃ C : ℝ,
    ∀ᶠ x in cocompact ℝ, |x| ^ (2 + ϵ) * Real.exp (Hinv H (α * |x|)) * f x ≤ C

end FDivToolkit


