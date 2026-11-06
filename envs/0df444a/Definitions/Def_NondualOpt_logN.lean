-- Prove2me | Definitions.Def_NondualOpt_logN
-- name    : NondualOpt_logN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:41.485817+00:00
-- url     : https://prove2.me/theorems/85295c75-fafd-45ef-a04b-c49e0cb4c62a
-- title:
--   Logarithm of a covering number in $[0,\infty]$
-- statement:
--   For a covering number $N\in\mathbb N\cup\{\infty\}$, $\log N$ is its natural logarithm, with $\log\infty=\infty$ (and the value $0$ at $N=0$, the covering number of an empty class).
--
--   **Formalization Note** Valued in $[0,\infty]$, so that entropy integrals are lower Lebesgue integrals with no junk values.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Proposition 20, p.28; Lemma 22, p.30

import Mathlib

open scoped ENNReal

namespace NondualOpt

/-- The natural logarithm of a covering number `N ∈ ℕ ∪ {∞}`, as an extended nonnegative real:
`log ∞ = ∞` and `log N` for finite `N` (with `log 0 = 0`, the value for an empty class).
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Proposition 20, p.28; Lemma 22, p.30.

**Formalization Note.** Covering numbers are `≥ 1` for nonempty classes, so `log N ≥ 0` there; the
`ℝ≥0∞` value lets entropy integrals be lower Lebesgue integrals with no junk value. -/
noncomputable def logN (N : ℕ∞) : ℝ≥0∞ :=
  ENat.recTopCoe ⊤ (fun n : ℕ => ENNReal.ofReal (Real.log n)) N

end NondualOpt


