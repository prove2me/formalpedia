-- Prove2me | Definitions.Def_QueryDepthMIS_twoHopEvent
-- name    : QueryDepthMIS_twoHopEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:32:54.940006+00:00
-- url     : https://prove2.me/theorems/2e1df344-e281-4c51-83fa-5a63f6b6ad6e
-- title:
--   The two-hop event $\mathcal G$
-- statement:
--   For sets of positions $P_1, P_2$ and positions $p_1, p_2, p_3$, $\mathcal G$ is the intersection of
--
--   1. $(\pi(p_1), \pi(p_2), \pi(p_3))$ forms an induced path,
--   2. $\pi(p_1)$ is alive at time $\max P_1 + 1$, and
--   3. $\pi(p_2)$ and $\pi(p_3)$ are alive at time $\max P_2 + 1$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.3, p.13

import Mathlib
import Definitions.Def_RGMISFast_tau
import Definitions.Def_QueryDepthMIS_rank
import Definitions.Def_QueryDepthMIS_IsInducedPath

set_option autoImplicit false

namespace QueryDepthMIS

/-- The event `G` of the two-hop lemma (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.3, p.13): "Define the event G as the
intersection of the following: • (p₁, p₂, p₃) forms an induced path, • p₁ is alive at time
max P₁ + 1, and • p₂ and p₃ are alive at time max P₂ + 1."

The vertices `u, v, w` at positions `p₁, p₂, p₃` form an induced path `[u, v, w]`
(Definition 2.8), `max P₁ + 1 ≤ τ(u)`, `max P₂ + 1 ≤ τ(v)` and `max P₂ + 1 ≤ τ(w)`, with `τ` the
rank of the inhibitor.

**Formalization Note** `max P` is `P.sup id`. -/
def twoHopEvent {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (P₁ P₂ : Finset ℕ) (p₁ p₂ p₃ : ℕ) (ω : Perm V) : Prop :=
  ∃ u v w : V, rank ω u = p₁ ∧ rank ω v = p₂ ∧ rank ω w = p₃ ∧ IsInducedPath G [u, v, w] ∧
    P₁.sup id + 1 ≤ RGMISFast.tau G (rank ω) u ∧ P₂.sup id + 1 ≤ RGMISFast.tau G (rank ω) v ∧
    P₂.sup id + 1 ≤ RGMISFast.tau G (rank ω) w

end QueryDepthMIS


