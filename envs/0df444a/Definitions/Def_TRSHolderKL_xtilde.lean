-- Prove2me | Definitions.Def_TRSHolderKL_xtilde
-- name    : TRSHolderKL_xtilde
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:55.235992+00:00
-- url     : https://prove2.me/theorems/d47aac56-68be-4899-a648-527109efdc1d
-- title:
--   The point $\tilde x=A^\dagger b$
-- statement:
--   $$
--   \tilde x=A^\dagger b,
--   $$
--   with $(\cdot)^\dagger$ the Moore–Penrose pseudoinverse. In the convex case with $\min_{\mathbb R^n}f=f^*$ the optimal solutions are $\tilde x+d$, $d\in\mathrm{Null}(A)$, $\|\tilde x+d\|\le1$.
--
--   **Formalization Note** The pseudoinverse is the published `HarmonicGames.Decomposition.pinv` of $x\mapsto Ax$.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, p.6

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_HarmonicGames_Decomposition_Pinv
open RBMSensitivity (E)

namespace TRSHolderKL

/-- `x̃ = A†b`, Jiang and Li, arXiv:1911.11955v2, p.6. -/
noncomputable def xtilde {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : E n :=
  HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin A) b

end TRSHolderKL


