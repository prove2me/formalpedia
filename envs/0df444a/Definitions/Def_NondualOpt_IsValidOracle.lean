-- Prove2me | Definitions.Def_NondualOpt_IsValidOracle
-- name    : NondualOpt_IsValidOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:15.719292+00:00
-- url     : https://prove2.me/theorems/9a0fe700-7e8c-4dba-96f1-e3c0350aee6b
-- title:
--   A valid adaptive first-order oracle
-- statement:
--   An **adaptive first-order oracle** for $f$ answers the query $x$ at round $t$ with the value $f(x)$ and a vector $O_t(h,x)$ that may depend on the round and on the history $h$ of previous answers. It is **valid** for $(f,p,q^*)$ if at every feasible query $x\in B_p^d$ the vector $O_t(h,x)$ is a valid subgradient answer: $\|O_t(h,x)\|_{q^*}\le1$ and $f(y)\ge f(x)+\langle O_t(h,x),y-x\rangle$ for all $y\in B_p^d$.
--
--   The supremum in the minimax error (4) ranges over such oracles.
--
--   **Formalization Note** Only the subgradient part is a free choice; the value part of every answer is $f(x)$ itself.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, §2, p.7

import Mathlib
import Definitions.Def_NondualOpt_lpBall
import Definitions.Def_NondualOpt_IsOracleAnswer

open scoped ENNReal

namespace NondualOpt

/-- An adaptive first-order oracle for `f` on `X = B_p^d` with subgradients in `H = B_{q∗}^d`.
At round `t`, given the answers `h` already returned and the query `x`, it returns the
subgradient part `O t h x`; the value part of the answer is `f(x)` itself. It is valid when
every answer at a feasible query is an `IsOracleAnswer`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, §2, p.7 ("the supremum ranges over
admissible convex objectives `f` and valid adaptive first-order oracles").

**Formalization Note.** Adaptivity is the dependence of `O` on the round and the history. -/
def IsValidOracle {d T : ℕ} (p qs : ℝ≥0∞) (f : (Fin d → ℝ) → ℝ)
    (O : (t : Fin T) → (Fin t → ℝ × (Fin d → ℝ)) → (Fin d → ℝ) → (Fin d → ℝ)) : Prop :=
  ∀ t h x, x ∈ lpBall p d → IsOracleAnswer p qs f x (O t h x)

end NondualOpt


