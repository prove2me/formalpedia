-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch05_ch05EulerPower
-- name    : RamanujanLostNotebook_PartIII_ch05_ch05EulerPower
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T12:51:25.341192+00:00
-- url     : https://prove2.me/theorems/790892e2-423e-4dd2-bed9-633d07c3d052
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 5: ch05EulerPower
-- statement:
--   Degree-n exact polynomial for the Euler factor ∏_{k≥1}(1-X^(d*k))^r.
--   For negative r the binomial expansion of each reciprocal factor is cut after n;
--   factors and terms beyond degree n cannot affect the requested coefficient.
--   Every use has d>0. This is a finite coefficient device, distinct from analytic eulerF.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 5.

import Mathlib

namespace RamanujanLostNotebook.PartIII

/-- Degree-n exact polynomial for the Euler factor ∏_{k≥1}(1-X^(d*k))^r.
For negative r the binomial expansion of each reciprocal factor is cut after n;
factors and terms beyond degree n cannot affect the requested coefficient.
Every use has d>0. This is a finite coefficient device, distinct from analytic eulerF. -/
noncomputable def ch05EulerPower (d : ℕ) (r : ℤ) (n : ℕ) : Polynomial ℤ :=
  ∏ k ∈ Finset.Icc 1 n,
    if 0 ≤ r then (1 - Polynomial.X ^ (d * k)) ^ r.toNat else
      ∑ j ∈ Finset.range (n + 1),
        Polynomial.C (Nat.choose (r.natAbs + j - 1) j : ℤ) *
          Polynomial.X ^ (d * k * j)

end RamanujanLostNotebook.PartIII


