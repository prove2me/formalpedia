-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch06_ch6EulerPower
-- name    : RamanujanLostNotebook_PartIII_ch06_ch6EulerPower
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T06:29:56.796978+00:00
-- url     : https://prove2.me/theorems/c60ee034-4e89-4904-b311-442d49fcbe8d
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 6: ch6EulerPower
-- statement:
--   Polynomial equal through degree N to ∏_{k≥1}(1-X^k)^r, for integer r.
--   For r<0, the finite binomial factors are truncated after j=N; every omitted
--   term has degree greater than N. This is an exact coefficient construction,
--   not an analytic approximation or a convergence assumption.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 6.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Polynomial equal through degree N to ∏_{k≥1}(1-X^k)^r, for integer r.
For r<0, the finite binomial factors are truncated after j=N; every omitted
term has degree greater than N. This is an exact coefficient construction,
not an analytic approximation or a convergence assumption. -/
noncomputable def ch6EulerPower (r : ℤ) (N : ℕ) : Polynomial ℤ :=
  ∏ k ∈ Finset.Icc 1 N,
    if 0 ≤ r then (1 - Polynomial.X ^ k) ^ r.toNat else
      ∑ j ∈ Finset.range (N + 1),
        Polynomial.C (Nat.choose (r.natAbs + j - 1) j : ℤ) *
          Polynomial.X ^ (k * j)

end RamanujanLostNotebook.PartIII

end


