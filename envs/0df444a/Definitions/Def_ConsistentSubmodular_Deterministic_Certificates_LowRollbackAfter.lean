-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackAfter
-- name    : ConsistentSubmodular_Deterministic_Certificates_LowRollbackAfter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:14:00.975885+00:00
-- url     : https://prove2.me/theorems/b9bc3d38-f490-4928-9870-df67be332a54
-- title:
--   Polynomials $n_0(k,q)$ and a quartic remainder for the after-attainer certificate
-- statement:
--   The after-attainer case of low-parameter rollback is handled by two explicit polynomials; the scalar credit itself is the `after_margin` of the targets file.
--
--   - `nzero k q` is the quadratic-in-$k$ polynomial
--   $$n_0(k,q) = (q^2 - 8q + 20)\,k^2 + (-7q^2 + 53q - 116)\,k + 10q^2 - 76q + 144.$$
--   - `remainder x q` is the quartic-in-$x$ polynomial
--   $$-(3-q)(2-q)^2 x^4 + 3(q-2)^2 x^3 + (2-q)(5q^2 - 25q + 54)\,x^2 - 3\,(q^3 - 3q^2 - 4q + 4)\,x - 2q^3 + 14q^2 - 20q + 12.$$
--
--   The file also proves the sign facts: for instance $n_0(k,q) < 0$ for $k \le 40/17$, $0 \le q \le 1$ whenever $20 - 11k + (2k-5)q < 0$, and the positivity of the remainder on its feasible range.
--
--   These polynomials close the two-case after-attainer certificate in the low-parameter rollback analysis, part of the proof that every window instance admits a $(3/4, m+3)$-certificate (Theorem 7).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackAfter.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

set_option maxHeartbeats 2000000

namespace ConsistentSubmodular.LowRollback

def nzero (k q : ℝ) : ℝ :=
  (q ^ 2 - 8 * q + 20) * k ^ 2 + (-7 * q ^ 2 + 53 * q - 116) * k + 10 * q ^ 2 - 76 * q + 144

def remainder (x q : ℝ) : ℝ :=
  -(3 - q) * (2 - q) ^ 2 * x ^ 4 + 3 * (q - 2) ^ 2 * x ^ 3 + (2 - q) * (5 * q ^ 2 - 25 * q + 54) * x ^ 2-
    3 * (q ^ 3 - 3 * q ^ 2 - 4 * q + 4) * x - 2 * q ^ 3 + 14 * q ^ 2 - 20 * q + 12

end ConsistentSubmodular.LowRollback


