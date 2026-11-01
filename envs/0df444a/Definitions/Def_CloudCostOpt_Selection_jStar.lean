-- Prove2me | Definitions.Def_CloudCostOpt_Selection_jStar
-- name    : CloudCostOpt_Selection_jStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:06:07.720492+00:00
-- url     : https://prove2.me/theorems/6abdf00a-25ba-4cf7-b4ac-76bd98027357
-- title:
--   The optimal resource $j^*(i,s,l)$ of a selection
-- statement:
--   For a selection, $j^*(i,s,l)=j^{Early}(i,s,l)$ before the deadline ($s<\delta_i$) and $j^*(i,s,l)=j_i^{Late,*}$ from the deadline on ($s\ge\delta_i$), as in Lemma 1.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Lemma 1, p.12; §3, p.13

import Mathlib
import Definitions.Def_CloudCostOpt_Selection

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`j*(i, s, l)`**: the selected early minimizer before the deadline (`s < δᵢ`), and
`j^{Late,*}_i` from the deadline on (Lemma 1).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Lemma 1, p.12; §3, p.13. -/
def Selection.jStar {S : System} (sel : Selection S) (i : Fin S.I) (s l : ℕ) : Fin (S.J + 1) :=
  if s < S.δ i then sel.jEarly i s l else sel.jLate i

end CloudCostOpt


