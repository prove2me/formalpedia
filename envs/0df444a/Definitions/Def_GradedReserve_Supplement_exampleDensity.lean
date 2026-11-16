-- Prove2me | Definitions.Def_GradedReserve_Supplement_exampleDensity
-- name    : GradedReserve_Supplement_exampleDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:47:05.469581+00:00
-- url     : https://prove2.me/theorems/b765f168-49d6-4bf5-83d0-c7fbfe6cccfd
-- title:
--   The discontinuous density $\tfrac12$ on $[0,0.3)$, $\tfrac{17}{14}$ on $(0.3,1]$
-- statement:
--   The density of the counterexample in Theorem 3.6:
--   $$f(v)=\begin{cases}1/2,& 0\le v<0.3,\\ 17/14,& 0.3\le v\le1,\end{cases}$$
--   and $0$ outside $[0,1]$.
--
--   **Formalization Note** The paper leaves $f(0.3)$ open; it is set to $17/14$. One point changes no distribution function and no revenue, and with this value $\varphi$ is strictly increasing on $(0,1)$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.6, p.8 (PDF 9); proof p.17 (PDF 18)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The discontinuous density of Theorem 3.6 (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.6, p.8, PDF 9; proof p.17, PDF 18):
`1/2` on `[0, 0.3)` and `17/14` on `(0.3, 1]`, and `0` outside `[0, 1]`.

**Formalization Note.** The paper leaves the value at `0.3` open; it is set to `17/14` here. The
value at one point changes neither `F`, nor `Q`, nor any revenue; with this choice
`φ(0.3) = −0.4` and `φ` is strictly increasing on `(0, 1)`, as the paper asserts. -/
noncomputable def exampleDensity (v : ℝ) : ℝ :=
  if v ∈ Icc (0:ℝ) 1 then (if v < 3 / 10 then 1 / 2 else 17 / 14) else 0

end GradedReserve.Supplement


