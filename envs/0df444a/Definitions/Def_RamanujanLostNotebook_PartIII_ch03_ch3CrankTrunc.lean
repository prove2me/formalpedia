-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3CrankTrunc
-- name    : RamanujanLostNotebook_PartIII_ch03_ch3CrankTrunc
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T09:04:43.873776+00:00
-- url     : https://prove2.me/theorems/4e08f5e4-94b7-4178-9aba-0ba7cdf7ede9
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 3: ch3CrankTrunc
-- statement:
--   Exact degree-N representative of F_a(q)=(q;q)_∞/((aq;q)_∞(q/a;q)_∞),
--   (3.1.1), p.45, over Z[a,a⁻¹]. Each reciprocal factor is represented by its
--   finite geometric series. For every N, coefficient N equals the infinite formal
--   product coefficient: omitted factors and geometric terms start above N.
--   The size-one coefficient is a+a⁻¹-1, so no combinatorial crank convention
--   is silently substituted. No formal equality is assumed in this definition.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 3.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3EulerTrunc
import Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3MonomialA

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Exact degree-N representative of F_a(q)=(q;q)_∞/((aq;q)_∞(q/a;q)_∞),
(3.1.1), p.45, over Z[a,a⁻¹]. Each reciprocal factor is represented by its
finite geometric series. For every N, coefficient N equals the infinite formal
product coefficient: omitted factors and geometric terms start above N.
The size-one coefficient is a+a⁻¹-1, so no combinatorial crank convention
is silently substituted. No formal equality is assumed in this definition. -/
noncomputable def ch3CrankTrunc (N : ℕ) : Polynomial (AddMonoidAlgebra ℤ ℤ) :=
  ch3EulerTrunc N 1 *
    ∏ j ∈ Finset.Icc 1 N,
      ((∑ k ∈ Finset.range (N + 1),
        Polynomial.C (ch3MonomialA (k : ℤ)) * Polynomial.X ^ (j * k)) *
       (∑ k ∈ Finset.range (N + 1),
        Polynomial.C (ch3MonomialA (-(k : ℤ))) * Polynomial.X ^ (j * k)))

end RamanujanLostNotebook.PartIII

end


