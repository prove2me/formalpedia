-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackBeforeHigh
-- name    : ConsistentSubmodular_Deterministic_Certificates_LowRollbackBeforeHigh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:13:55.063659+00:00
-- url     : https://prove2.me/theorems/efb3057b-3535-4db8-afe2-4139d89f1375
-- title:
--   The bivariate polynomial $\beta(x,q)$ for the high-parent before-attainer certificate
-- statement:
--   The before-attainer case with a high parent in low-parameter rollback is settled by the sign of a single bivariate polynomial.
--
--   - `beta x q` is the real number
--   $$\beta(x,q) = (48 - q^3)\,(1-x)^2(1+x) + q^2\,(11x^3 - 14x^2 - 12x + 12) - 4q\,(1-x^2)(13 - 10x).$$
--
--   The file also proves that $\beta(x,q) > 0$ on the feasible parameter triangle ($0 \le x \le 1/2$, $0 \le q \le 1$, and $(1-q) - (2-q)x \ge 0$), together with the multiplier-sign facts used to derive the certificate.
--
--   This polynomial is the algebraic core of one case of the low-parameter rollback analysis, which belongs to the construction of $(3/4, m+3)$-certificates (Theorem 7) via atomic profiles.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackBeforeHigh.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

namespace ConsistentSubmodular.LowRollback

def beta (x q : ℝ) : ℝ :=
  (48 - q ^ 3) * ((1 - x) ^ 2 * (1 + x)) + q ^ 2 * (11 * x ^ 3 - 14 * x ^ 2 - 12 * x + 12)-
    4 * q * (1 - x ^ 2) * (13 - 10 * x)

end ConsistentSubmodular.LowRollback


