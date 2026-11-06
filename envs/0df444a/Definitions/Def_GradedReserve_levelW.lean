-- Prove2me | Definitions.Def_GradedReserve_levelW
-- name    : GradedReserve_levelW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:49.426715+00:00
-- url     : https://prove2.me/theorems/6aa15c4e-24a1-4ea8-b075-7e8c5a9b09df
-- title:
--   Acceptance levels $w(t)=\inf\{v:s(v)\ge t\}$
-- statement:
--   For $t\in(0,1)$, the type at which the probability of sale reaches level $t$,
--   $$w(t)=\inf\{v:s(v)\ge t\},$$
--   with $w(t)=1$ if the level is never reached.
--
--   **Formalization Note** As in the paper's proof ("generalized inverses are understood up to null sets"), $w(t)$ is the essential infimum: the infimum of the $v\in[0,1]$ for which $\{u\le v: s(u)\ge t\}$ has positive probability, and $1$ if there is none.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 3.2, p.5 (PDF 6); proof of Lemma 3.2, p.14 (PDF 15)

import Mathlib
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_saleProb
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The acceptance levels `w(t) = inf{v : s(v) ≥ t}`, with `w(t) = 1` if the level is never reached
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 3.2, p.5, PDF 6).

**Formalization Note.** "Generalized inverses are understood up to null sets" (proof of Lemma 3.2,
p.14, PDF 15): `w(t)` is the essential infimum, the infimum of the `v ∈ [0, 1]` for which
`{u ≤ v : s(u) ≥ t}` has positive probability, and `1` when there is none. For a non-decreasing
`s` this is the paper's `inf{v : s(v) ≥ t}`; it is insensitive to the values of `s` on a null
set of types, where `σ` need not be a best response. -/
noncomputable def levelW (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) (σ : Kernel ℝ ℝ) (t : ℝ) : ℝ :=
  sInf (insert 1 {v ∈ Icc (0:ℝ) 1 |
    0 < typeMeasure f ({u | t ≤ saleProb f n π σ u} ∩ Iic v)})

end GradedReserve


