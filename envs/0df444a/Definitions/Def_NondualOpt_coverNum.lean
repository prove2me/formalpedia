-- Prove2me | Definitions.Def_NondualOpt_coverNum
-- name    : NondualOpt_coverNum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:50.503701+00:00
-- url     : https://prove2.me/theorems/924e0d97-3c64-4154-8507-1524666a00fc
-- title:
--   The covering number $N(B_p^d,R\,B_s^d)$
-- statement:
--   For $p,s\in[1,\infty]$ and $R>0$, $N(B_p^d,R\,B_s^d)$ is the least number $N$ of translates $a_1+RB_s^d,\dots,a_N+RB_s^d$ (centres anywhere in $\mathbb R^d$) whose union contains $B_p^d$. Proposition 28 trades these covering numbers against uniform convexity, and Fact 29 bounds them.
--
--   **Formalization Note** Valued in $\mathbb N\cup\{\infty\}$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Proposition 28 and Fact 29, p.39

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_NondualOpt_lpBall

open scoped ENNReal

namespace NondualOpt

/-- The covering number `N(B_p^d, R B_s^d)`: the least number `N` of translates
`a_1 + R B_s^d, …, a_N + R B_s^d` (arbitrary centres in `ℝ^d`) covering `B_p^d`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Proposition 28 (proof) and Fact 29, p.39.

**Formalization Note.** Valued in `ℕ∞` (`⊤` if no finite cover exists, which does not happen for
`R > 0`). -/
noncomputable def coverNum (p s : ℝ≥0∞) (d : ℕ) (R : ℝ) : ℕ∞ :=
  ⨅ (N : ℕ) (a : Fin N → (Fin d → ℝ)) (_ : lpBall p d ⊆ ⋃ i, {x | RegimeDRCVaR.normM s (x - a i) ≤ R}),
      (N : ℕ∞)

end NondualOpt


