-- Prove2me | Definitions.Def_KallMayerSLP_Bonferroni_vMaxClosedForm
-- name    : KallMayerSLP_Bonferroni_vMaxClosedForm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:02.995152+00:00
-- url     : https://prove2.me/theorems/e2a7ea3d-4d91-4d89-84c2-5385fe2cfb78
-- title:
--   Closed form of the upper Boole–Bonferroni bound
-- statement:
--   The closed form of the upper bound is
--   $$
--   V_{\max}=S_1-\frac{2}{r}S_2.
--   $$
--   It is the optimal value of the maximization counterpart of the linear program (3.14).
--
--   **Formalization Note** As in the book, the value is not capped at $1$, and it can exceed $1$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 4, §3.4, eq. (3.15), p.288 (PDF 297)

import Mathlib

namespace KallMayerSLP.Bonferroni

/-- The upper Boole–Bonferroni bound `V_max = S₁ - (2/r) S₂`.

Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 4, eq. (3.15), p.288 (PDF 297).

**Formalization Note.** The value is not capped at `1`, exactly as in the book: it can exceed `1`. -/
noncomputable def vMaxClosedForm (r : ℕ) (S₁ S₂ : ℝ) : ℝ :=
  S₁ - 2 / (r : ℝ) * S₂

end KallMayerSLP.Bonferroni


