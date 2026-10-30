-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch15_ch15F
-- name    : RamanujanLostNotebook_PartI_ch15_ch15F
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:10:11.662336+00:00
-- url     : https://prove2.me/theorems/41d6230d-1d68-4481-b624-a93433cbed78
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 15: ch15F
-- statement:
--   F(q)=f(-q)=(q;q)_∞ on the real line, via the approved complex Euler product. For |q|<1 the product has its classical convergent value; it is positive for 0≤q<1. Endpoint q=1 is zero and is used only at a measure-zero integration endpoint. Source (15.2.4), p.329.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 15.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_shared_eulerF

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- F(q)=f(-q)=(q;q)_∞ on the real line, via the approved complex Euler product. For |q|<1 the product has its classical convergent value; it is positive for 0≤q<1. Endpoint q=1 is zero and is used only at a measure-zero integration endpoint. Source (15.2.4), p.329. -/
def ch15F (q : ℝ) : ℝ := (eulerF (q : ℂ)).re

end RamanujanLostNotebook.PartI

end


