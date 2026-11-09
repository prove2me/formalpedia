-- Prove2me | Definitions.Def_InflMaxAdapt_edgeProb
-- name    : InflMaxAdapt_edgeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:21.675623+00:00
-- url     : https://prove2.me/theorems/227282ef-0a34-43bd-a41d-84bd3535679b
-- title:
--   Probability of an event of the live edge set
-- statement:
--   For an event $\mathcal E$ of the live edge set,
--   $$
--   \mathbb P(\mathcal E) \;=\; \sum_{E \,:\, E \in \mathcal E} \prod_{e \in E} q_e \prod_{e \notin E} (1 - q_e),
--   $$
--   the probability of $\mathcal E$ under independent bond percolation with edge probabilities $q$. Connection probabilities such as $\mathbb P(u \leftrightarrow v)$ and $\mathbb P(u \leftrightarrow v,\ u \not\leftrightarrow S)$ are of this form.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6)

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeWeight

namespace InflMaxAdapt

/-- The probability `P(ev)` of an event of the live edge set in the undirected-edge
representation (Section 2, printed p.5 = PDF p.6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): the total weight of the live edge sets
`E` satisfying `ev`. -/
noncomputable def edgeProb {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ)
    (ev : Finset (Sym2 V) → Prop) : ℝ := by
  classical
  exact ∑ E : Finset (Sym2 V), if ev E then edgeWeight q E else 0

end InflMaxAdapt


