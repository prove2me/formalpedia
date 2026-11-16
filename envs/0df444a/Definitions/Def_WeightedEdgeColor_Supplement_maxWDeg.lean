-- Prove2me | Definitions.Def_WeightedEdgeColor_Supplement_maxWDeg
-- name    : WeightedEdgeColor_Supplement_maxWDeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:36:29.288027+00:00
-- url     : https://prove2.me/theorems/a33f97c9-68b2-4020-aa14-259e021aee0d
-- title:
--   Maximum weighted degree $\Delta_w(G)=\max_{v\in V} W_G(v)$
-- statement:
--   Let $G=(V,E)$ be a finite loopless edge-weighted multigraph with weights $w:E\to(0,1]$, and let $W_G(v)=\sum_{e\ni v}w_e$ be the weighted degree of a vertex $v$. The **maximum weighted degree** is
--   $$
--   \Delta_w(G)=\max_{v\in V}W_G(v).
--   $$
--   It is the natural volume lower bound for weighted edge coloring: $\lceil\Delta_w(G)\rceil\le\mathrm{bp}(G)\le\chi'_w(G)$. The total-weight results of the paper (Theorems B.2 and D.3) bound $\chi'_w(G)$ in terms of $\Delta_w(G)$.
--
--   **Formalization Note** The maximum is a finite maximum over the vertex set. A graph with no vertices has no edges, and its value is set to $0$; in every case $\Delta_w(G)\ge0$. The ceiling $\lceil\Delta_w(G)\rceil$ is the integer ceiling.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), §1, p.1; Appendix A (standing conventions), p.24

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

open WGraph

/-- The maximum weighted degree `∆_w(G) = max_{v ∈ V} W_G(v)`, where `W_G(v) = ∑_{e ∋ v} w_e`.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped), §1, p.1; Appendix A
(standing conventions), p.24.

**Formalization Note.** The maximum is taken over the finite vertex set with `Finset.sup'`. For a
graph with no vertices (hence no edges) the value is `0`, the empty maximum of nonnegative
weighted degrees; this is the only case without a vertex. Since every `W_G(v) ≥ 0`, the value is
always `≥ 0`, and `⌈∆_w(G)⌉` is the integer ceiling `Int.ceil`. -/
noncomputable def maxWDeg {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : WGraph V E) : ℝ :=
  if h : (Finset.univ : Finset V).Nonempty then Finset.univ.sup' h G.W else 0

end Supplement

end WeightedEdgeColor


