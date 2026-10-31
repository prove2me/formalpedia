-- Prove2me | Definitions.Def_TSPSDPGap_sdp2Opt
-- name    : TSPSDPGap_sdp2Opt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:47.862316+00:00
-- url     : https://prove2.me/theorems/91beb564-8492-421f-9fc8-dc9883408276
-- title:
--   Optimal value $\mathrm{OPT}_{\mathrm{SDP}}(D)$ of SDP (2)
-- statement:
--   For an $(n+1)\times(n+1)$ cost matrix $D$ and $r,s\in[n+1]$, the **optimal value of SDP (2)** is
--   $$
--   \mathrm{OPT}_{\mathrm{SDP}}(D)=\inf\Bigl\{\operatorname{trace}\bigl((D[\beta]\otimes\tfrac12 C^{(n+1)}_1[\alpha]+\operatorname{Diag}(\bar c))Y\bigr)\ :\ Y \text{ feasible for SDP (2)}\Bigr\}.
--   $$
--
--   **Formalization Note** The value lies in $[0,\infty]$: the objective enters through $x\mapsto\max(x,0)$ and an empty feasible set would give $+\infty$. For metric $D$ the objective is nonnegative on the feasible set (all of $D$, $C_1$, $\bar c$, $Y$ are entrywise nonnegative), and the feasible set is nonempty, so this is the paper's optimal value.
-- source:
--   Gutekunst & Williamson, SDP Relaxations of the TSP and Their Integrality Gaps, arXiv:1907.09054v1, §2.1, p.5 (OPT_SDP); SDP (2), p.7

import Mathlib
import Definitions.Def_TSPSDPGap_IsSDP1Feasible
import Definitions.Def_TSPSDPGap_sdp2Objective

open scoped ENNReal

namespace TSPSDPGap

/-- **The optimal value `OPT_SDP(D)` of SDP (2) on `n + 1` vertices.**
Gutekunst & Williamson, *SDP Relaxations of the TSP and Their Integrality Gaps*,
arXiv:1907.09054v1, §2.1, p.5: "Let OPT_SDP(D) … denote the optimal value to an SDP
relaxation", applied to SDP (2) on `n + 1` vertices (p.7).

It is the infimum of the SDP (2) objective over every `Y` feasible for SDP (1)/(2).

**Formalization Note.** The value is in `ℝ≥0∞`: an empty feasible set gives `⊤` (not a junk
`0`), and the objective enters through `ENNReal.ofReal`. For metric `D` the objective is
`≥ 0` on the feasible set (all of `D`, `C_1`, `c̄` and `Y` are entrywise nonnegative), so
`ENNReal.ofReal` loses nothing there. -/
noncomputable def sdp2Opt (n : ℕ) (D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (r s : Fin (n + 1)) : ℝ≥0∞ :=
  ⨅ (Y : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (_ : IsSDP1Feasible n Y),
    ENNReal.ofReal (sdp2Objective n D r s Y)

end TSPSDPGap


