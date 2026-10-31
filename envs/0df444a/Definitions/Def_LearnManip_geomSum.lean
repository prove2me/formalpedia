-- Prove2me | Definitions.Def_LearnManip_geomSum
-- name    : LearnManip_geomSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:05.59982+00:00
-- url     : https://prove2.me/theorems/540e91a5-b8c2-4079-b650-a13fa0a319dd
-- title:
--   Partial geometric sum $\sum_{j<k}\alpha^j$
-- statement:
--   The partial geometric sum
--   $$A_k=\sum_{j=0}^{k-1}\alpha^j,$$
--   the coefficient of $\mu$ in the $k$-stage value.
--
--   **Formalization Note.** The printed (EC.16) has upper index $k$, which the proof's own base case $v_1=\mu+\hat G_1$ contradicts; the upper index is $k-1$.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), (EC.16), p.ec9 (PDF 48), corrected

import Mathlib
import Definitions.Def_LearnManip_Params

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The partial geometric sum `∑_{j<k} α^j`, the coefficient of `μ` in (EC.16), p.ec9 (PDF 48), of
Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), with the upper index corrected from `k` to `k − 1`
(the proof's own base case is `v₁ = μ + Ĝ₁`). -/
noncomputable def geomSum (P : Params) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, (P.α : ℝ) ^ j

end LearnManip


