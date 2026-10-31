-- Prove2me | Definitions.Def_TRSHolderKL_xbar
-- name    : TRSHolderKL_xbar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:25.98466+00:00
-- url     : https://prove2.me/theorems/35d84c16-0b7a-4bd6-9d08-a22fbcd8c017
-- title:
--   The point $\bar x=(A-\lambda_1I)^\dagger b$
-- statement:
--   $$
--   \bar x=(A-\lambda_1I)^\dagger b,
--   $$
--   where $(\cdot)^\dagger$ is the Moore–Penrose pseudoinverse. In the hard case 2 the optimal solutions are $\bar x+v$ with $v\in\mathrm{Null}(A-\lambda_1I)$ and $\|\bar x+v\|=1$.
--
--   **Formalization Note** The pseudoinverse is the published `HarmonicGames.Decomposition.pinv` of the linear map $x\mapsto (A-\lambda_1I)x$.
-- source:
--   Jiang and Li, Hölderian error bounds and Kurdyka-Łojasiewicz inequality for the trust region subproblem, arXiv:1911.11955v2, p.8; Notation, p.3

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_TRSHolderKL_shiftLin
import Definitions.Def_HarmonicGames_Decomposition_Pinv
open RBMSensitivity (E)

namespace TRSHolderKL

/-- `x̄ = (A − λ₁I)†b`, Jiang and Li, arXiv:1911.11955v2, p.8, with `†` the Moore–Penrose
pseudoinverse (Notation, p.3). -/
noncomputable def xbar {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : E n) : E n :=
  HarmonicGames.Decomposition.pinv (shiftLin A) b

end TRSHolderKL


