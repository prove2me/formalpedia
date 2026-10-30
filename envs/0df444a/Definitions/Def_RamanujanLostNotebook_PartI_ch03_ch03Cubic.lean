-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Cubic
-- name    : RamanujanLostNotebook_PartI_ch03_ch03Cubic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:13:54.758273+00:00
-- url     : https://prove2.me/theorems/5f18618a-6186-4ec0-a94d-8d7e9d74c8fa
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 3: ch03Cubic
-- statement:
--   Cubic continued fraction in a coherent root coordinate r: q=r³,
--   G(q)=r/(1+(q+q²)/(1+(q²+q⁴)/(1+…))), (3.1.6), p. 86.
--   The cube root is an explicit argument rather than a principal complex power;
--   the accompanying convergence conclusion keeps this independent of products.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 3.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03Convergent
import Definitions.Def_RamanujanLostNotebook_PartI_ch03_ch03SequenceValue

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Cubic continued fraction in a coherent root coordinate r: q=r³,
G(q)=r/(1+(q+q²)/(1+(q²+q⁴)/(1+…))), (3.1.6), p. 86.
The cube root is an explicit argument rather than a principal complex power;
the accompanying convergence conclusion keeps this independent of products. -/
noncomputable def ch03Cubic (r : ℂ) : ℂ :=
  r * ch03SequenceValue (ch03Convergent (fun k : ℕ => (r ^ 3) ^ k + (r ^ 3) ^ (2 * k)))

end RamanujanLostNotebook.PartI

end


