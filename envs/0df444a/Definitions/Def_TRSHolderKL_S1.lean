-- Prove2me | Definitions.Def_TRSHolderKL_S1
-- name    : TRSHolderKL_S1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:35.310035+00:00
-- url     : https://prove2.me/theorems/f6e62d56-b5be-449c-87f1-627d1a046fa0
-- title:
--   The solution set $S_1$ of the relaxation (P$_1$)
-- statement:
--   $S_1$ is the set of minimizers of $\tilde f$ over the closed unit ball $\{x:\|x\|\le1\}$. It is a nonempty closed convex set when $\lambda_1<0$; its relation to $S_0$ is Lemma 2.1.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, (P1), p.3

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_ftilde
open RBMSensitivity (E)

namespace TRSHolderKL

/-- `S₁`, the solution set of the relaxation (P₁): the minimizers of `f̃` over the unit
ball, Jiang and Li, arXiv:1911.11955v2, p.3. -/
def S1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : Set (E n) :=
  {x | ‖x‖ ≤ 1 ∧ ∀ y : E n, ‖y‖ ≤ 1 → ftilde A b x ≤ ftilde A b y}

end TRSHolderKL


