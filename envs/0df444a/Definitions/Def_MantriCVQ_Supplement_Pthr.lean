-- Prove2me | Definitions.Def_MantriCVQ_Supplement_Pthr
-- name    : MantriCVQ_Supplement_Pthr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:05:53.308488+00:00
-- url     : https://prove2.me/theorems/c148ac16-350e-496a-9ca4-e94a87231204
-- title:
--   Width threshold $P(n,h)$ (Appendix B)
-- statement:
--   For the degree $d$ of the code family and an instance of size $n$ and height $h$, put
--   $$t_i=\Big\lfloor\frac{m_i}{16d}\Big\rfloor\ (0\le i<h),\qquad P(n,h)=\prod_{i<h}(t_i+1),$$
--   with $P(n,0)=1$, where $m_i=8\lfloor n/(8\cdot16^i)\rfloor$ are the dimensions of Eq. (4.1). Theorem B.1 shows that a DNF of width less than $P(n,h)$ on the leaves cannot distinguish the two root values, which drives the message lower bound of Theorem B.4.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Appendix B, p. 47 (PDF p. 49)

import Mathlib
import Definitions.Def_MantriCVQ_dimsRange

namespace MantriCVQ.Supplement

/-- The width threshold `P(n, h) = ∏_{i<h} (t_i + 1)` with `t_i = ⌊m_i / (16d)⌋` (Mantri,
arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Appendix B, p. 47 (PDF p. 49): "We put
`t_i = ⌊m_i/(16d)⌋ (0 ≤ i < h)`, `P(n, h) = ∏_{i<h} (t_i + 1)`, with `P(n, 0) = 1`"). The dimensions
`m_i` are those of Eq. (4.1) (`MantriCVQ.dim`). -/
def Pthr (d n h : ℕ) : ℕ :=
  ∏ i ∈ Finset.range h, (dim n i / (16 * d) + 1)

end MantriCVQ.Supplement


