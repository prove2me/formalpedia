-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch17_ch17EtaQuotient
-- name    : RamanujanLostNotebook_PartI_ch17_ch17EtaQuotient
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-11T12:05:51.491732+00:00
-- url     : https://prove2.me/theorems/76c5491e-2dbb-45ca-af2c-dcb7a6d81b06
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 17: ch17EtaQuotient
-- statement:
--   Euler-product quotient with its exponential prefactor exposed.
--   For Re(w)<0 and a,b>0 this is f(-exp(a*w))/(exp(c*w)*f(-exp(b*w))).
--   The variable w=2*pi*i*z fixes every fractional power in (17.2.1),
--   (17.2.25), and (17.2.34); it is not replaced by an arbitrary root of q.
--   The Euler products converge and never vanish on this domain.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 17.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_eulerF

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Euler-product quotient with its exponential prefactor exposed.
For Re(w)<0 and a,b>0 this is f(-exp(a*w))/(exp(c*w)*f(-exp(b*w))).
The variable w=2*pi*i*z fixes every fractional power in (17.2.1),
(17.2.25), and (17.2.34); it is not replaced by an arbitrary root of q.
The Euler products converge and never vanish on this domain. -/
noncomputable def ch17EtaQuotient (w : ℂ) (a b c : ℝ) : ℂ :=
  eulerF (Complex.exp ((a : ℂ) * w)) /
    (Complex.exp ((c : ℂ) * w) * eulerF (Complex.exp ((b : ℂ) * w)))

end RamanujanLostNotebook.PartI

end


