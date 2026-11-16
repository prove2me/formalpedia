-- Prove2me | Definitions.Def_WeightedEdgeColor_Supplement_hInf
-- name    : WeightedEdgeColor_Supplement_hInf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:37:04.088195+00:00
-- url     : https://prove2.me/theorems/665f287f-a2e7-413a-8170-71340d6bf59f
-- title:
--   Harmonic constant $h_\infty=\sum_{j\ge1}1/r_j$, $r_1=1$, $r_{j+1}=r_j(r_j+1)$
-- statement:
--   Define the integer sequence $r_1=1$, $r_{j+1}=r_j(r_j+1)$, so $r=1,2,6,42,1806,\dots$, and the **harmonic constant**
--   $$
--   h_\infty=\sum_{j\ge1}\frac1{r_j}=1.691030206757\ldots
--   $$
--   It is the supremum of the harmonic charge $a(w)=1/\lfloor 1/w\rfloor$ that fits in one unit bin (Lee and Lee). It is the coefficient of Theorem E.4 and, multiplied by $5/4$, of Theorem F.1.
--
--   **Formalization Note** The sequence is indexed from $0$ in Lean ($r_{j+1}$ is the $j$-th term), and $h_\infty$ is the sum of the series, which converges since $r_{j+1}\ge2^j$. The decimal expansion is not used.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Appendix E.4, p.64

import Mathlib

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- The sequence `r_1 = 1`, `r_{j+1} = r_j (r_j + 1)` (Sylvester-type sequence `1, 2, 6, 42, …`),
indexed from `0`: `hInfSeq j = r_{j+1}`. -/
def hInfSeq : ℕ → ℕ
  | 0 => 1
  | j + 1 => hInfSeq j * (hInfSeq j + 1)

/-- The harmonic constant `h∞ = ∑_{j ≥ 1} 1 / r_j = 1.691030206757…`.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped), Appendix E.4, p.64:
"Let r_1 = 1, r_{j+1} = r_j(r_j + 1), h∞ = ∑_{j≥1} 1/r_j = 1.691030206757 . . . ."

**Formalization Note.** The sequence is indexed from `0` (`hInfSeq j = r_{j+1}`), so the sum is
over `j : ℕ`. The series converges (`r_{j+1} ≥ 2^j`), so `tsum` is the actual sum, not a junk
value; the decimal expansion is not used. -/
noncomputable def hInf : ℝ := ∑' j : ℕ, 1 / (hInfSeq j : ℝ)

end Supplement

end WeightedEdgeColor


