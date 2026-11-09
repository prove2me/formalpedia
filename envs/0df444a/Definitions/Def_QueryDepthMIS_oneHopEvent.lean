-- Prove2me | Definitions.Def_QueryDepthMIS_oneHopEvent
-- name    : QueryDepthMIS_oneHopEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:33.350988+00:00
-- url     : https://prove2.me/theorems/7ec4cb1f-9418-457b-a000-315fa076907f
-- title:
--   The one-hop event $F$
-- statement:
--   For a nonempty set of positions $P_1$ and positions $p_1, p_2$, $F$ is the event that the vertices $\pi(p_1)$ and $\pi(p_2)$ are adjacent and both are alive at time $\max P_1 + 1$:
--   $$
--   (\pi(p_1), \pi(p_2)) \in E,\qquad \operatorname{rank}(\operatorname{inhib}(\pi(p_j))) \ge \max P_1 + 1\ \ (j = 1, 2).
--   $$
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.2, p.12

import Mathlib
import Definitions.Def_RGMISFast_tau
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- The event `F` of the one-hop lemma (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.2, p.12): "Let F be the event that
(π(p₁), π(p₂)) ∈ E and both vertices are alive at time max P₁ + 1."

`oneHopEvent G P₁ p₁ p₂ ω` holds if the vertices `u, v` at positions `p₁, p₂` are adjacent and
both alive at time `max P₁ + 1`, i.e. `max P₁ + 1 ≤ τ(u)` and `max P₁ + 1 ≤ τ(v)` with `τ` the
rank of the inhibitor (Definition 2.2).

**Formalization Note** `max P₁` is `P₁.sup id` (the maximum of a nonempty set of naturals; the
lemma assumes `P₁` nonempty). Positions outside `[1, n]` carry no vertex, and the event is then
false. -/
def oneHopEvent {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P₁ : Finset ℕ) (p₁ p₂ : ℕ) (ω : Perm V) : Prop :=
  ∃ u v : V, rank ω u = p₁ ∧ rank ω v = p₂ ∧ G.Adj u v ∧
    P₁.sup id + 1 ≤ RGMISFast.tau G (rank ω) u ∧ P₁.sup id + 1 ≤ RGMISFast.tau G (rank ω) v

end QueryDepthMIS


