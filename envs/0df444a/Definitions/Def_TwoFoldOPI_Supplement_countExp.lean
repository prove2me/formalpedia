-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_countExp
-- name    : TwoFoldOPI_Supplement_countExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:54:36.974485+00:00
-- url     : https://prove2.me/theorems/d6da2de5-9c9b-4106-bad4-f3494e585ce3
-- title:
--   The counting exponent $\mathrm{CntExp}_q(x)$
-- statement:
--   For an integer $q\ge2$ and real $x\ge0$,
--   $$\mathrm{CntExp}_q(x)=\inf_{0<z\le1}\Big(\log_q(1+z+\dots+z^{q-1})-x\log_qz\Big).$$
--   It is the exponent in $\mathrm{Count}_q(v,\rho v)=q^{v(\mathrm{CntExp}_q(\rho)+o(1))}$ and enters the thresholds (12) and (18) of Theorems 7.5 and 8.5.
--
--   **Formalization Note** The infimum is over the subtype $(0,1]$; for $x\ge0$ every value is $\ge0$, so the set is bounded below and the infimum is the true one.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.10, p. 22

import Mathlib

namespace TwoFoldOPI

namespace Supplement

/-- **The counting exponent `CntExp_q(x)`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.1, Definition 5.10, p.22: "For a real x ≥ 0, define the counting exponent
CntExp_q(x) := inf_{0<z≤1} ( log_q(1 + z + ⋯ + z^{q−1}) − x log_q z )."

`countExp q x = inf_{0 < z ≤ 1} (log_q(1 + z + ⋯ + z^{q−1}) − x · log_q z)`.

**Formalization Note.** The infimum is a real `⨅` over the subtype `(0, 1]`, which is nonempty.
For `q ≥ 2` and `x ≥ 0` (every use) each value is `≥ 0`: the sum is `≥ 1` and `log_q z ≤ 0`.
So the set is bounded below and the `⨅` is the true infimum, not Lean's junk value. -/
noncomputable def countExp (q : ℕ) (x : ℝ) : ℝ :=
  ⨅ z : Set.Ioc (0 : ℝ) 1,
    (Real.logb q (∑ j ∈ Finset.range q, (z : ℝ) ^ j) - x * Real.logb q (z : ℝ))

end Supplement

end TwoFoldOPI


