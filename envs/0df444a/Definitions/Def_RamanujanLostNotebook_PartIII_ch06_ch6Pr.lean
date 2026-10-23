-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch06_ch6Pr
-- name    : RamanujanLostNotebook_PartIII_ch06_ch6Pr
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T06:35:57.413518+00:00
-- url     : https://prove2.me/theorems/596fa342-d483-45c7-a53f-25a6f3418c94
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 6: ch6Pr
-- statement:
--   Generalized partition coefficient p_r(n) of (q;q)_∞^(-r), pp.183,195.
--   For r>0 these count r-colored partitions; r<0 gives signed Euler-product
--   coefficients, including q_m(n)=p_{-m}(n) in (6.1.3). The empty coefficient is 1.
--   Negative indices are assigned 0, so Entry 6.5.1 retains its printed n=0 case.
--   The zero extension is a disclosed interpretation in Entry 6.5.1; all other
--   uses evaluate nonnegative indices.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 6.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartIII_ch06_ch6EulerPower

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Generalized partition coefficient p_r(n) of (q;q)_∞^(-r), pp.183,195.
For r>0 these count r-colored partitions; r<0 gives signed Euler-product
coefficients, including q_m(n)=p_{-m}(n) in (6.1.3). The empty coefficient is 1.
Negative indices are assigned 0, so Entry 6.5.1 retains its printed n=0 case.
The zero extension is a disclosed interpretation in Entry 6.5.1; all other
uses evaluate nonnegative indices. -/
noncomputable def ch6Pr (r n : ℤ) : ℤ :=
  if n < 0 then 0 else (ch6EulerPower (-r) n.toNat).coeff n.toNat

end RamanujanLostNotebook.PartIII

end


