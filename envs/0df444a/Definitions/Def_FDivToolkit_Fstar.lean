-- Prove2me | Definitions.Def_FDivToolkit_Fstar
-- name    : FDivToolkit_Fstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:22:07.148162+00:00
-- url     : https://prove2.me/theorems/350dbf42-8919-420d-acc6-8c0932033543
-- title:
--   The convex conjugate $F^*$ and the function $K$
-- statement:
--   With $F(y)=+\infty$ for $y<0$, the **convex conjugate** of $F$ is
--   $$
--   F^*(x)=\sup_{y\in\mathbb R}\big(xy-F(y)\big),\qquad x\in\mathbb R,
--   $$
--   and $K(\alpha_1,\alpha_2)=\int_{\mathcal S}F^*(\alpha_1+\alpha_2x)f(x)\,dx$.
--
--   These are the objects through which the proof of Proposition 1 connects to the theory of Breuer and Csiszár.
--
--   **Formalization Note** `FstarE` is the supremum over $y\ge0$ in `EReal`, and `Fstar` is its real value; milestone `conjugate_formula` states finiteness. `K` is a Bochner integral; milestone `display_27` states integrability of its integrand under (5).
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), proof of Proposition 1, p.31

import Definitions.Def_FDivToolkit_Fh

open Set
open scoped ENNReal

namespace FDivToolkit

/-- The convex conjugate `F*(x) = sup_{y∈ℝ} (xy − F(y))`, Kruse, Schneider & Schweizer, SSRN 3680475
(Aug 25, 2020), proof of Proposition 1, p.31, where `F(y) = +∞` for `y < 0`.

**Formalization Note.** The supremum is taken in `EReal`, over `y ≥ 0`, since `F = +∞` on `y < 0`
contributes `−∞`. Being in `EReal` it is honest: a real `⨆` would return `0` on an unbounded set.
`x * y` is real, so `x * y − ⊤ = ⊥` is the intended value and no `⊤ − ⊤` arises. -/
noncomputable def FstarE (H : ℝ → ℝ) (x : ℝ) : EReal :=
  ⨆ y ∈ Ici (0 : ℝ), (((x * y : ℝ) : EReal) - ((Fbar H y : ℝ≥0∞) : EReal))

/-- `F*` as the real function `F* : ℝ → ℝ` of the paper (proof of Proposition 1, p.31).

**Formalization Note.** Milestone `conjugate_formula` states that `FstarE H x` is finite, so this
`toReal` loses nothing. -/
noncomputable def Fstar (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  (FstarE H x).toReal

/-- `K(α₁, α₂) = ∫_𝓢 F*(α₁ + α₂x) f(x) dx`, Kruse, Schneider & Schweizer, SSRN 3680475
(Aug 25, 2020), proof of Proposition 1, p.31.

**Formalization Note.** This is a Bochner integral, so it means what the paper says only when the
integrand is integrable. Milestone `display_27` states that it is, under (5). -/
noncomputable def K (H f : ℝ → ℝ) (α : ℝ × ℝ) : ℝ :=
  ∫ x, Fstar H (α.1 + α.2 * x) * f x

end FDivToolkit


