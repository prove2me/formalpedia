-- Prove2me | Definitions.Def_FeedbackSwitching_StronglyRevealing
-- name    : FeedbackSwitching_StronglyRevealing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:08.218748+00:00
-- url     : https://prove2.me/theorems/3be14e93-627a-4c67-a297-7bbf2a5cbfa1
-- title:
--   Strongly revealing graph (Definition 1, Eq. (13))
-- statement:
--   A feedback graph $G=([K],E)$ is **strongly revealing** if every pair of distinct actions has an endpoint that observes the losses of both: for every $i\neq j$,
--   $$
--   \big[(i,i)\in E\ \text{and}\ (i,j)\in E\big]\quad\text{or}\quad\big[(j,j)\in E\ \text{and}\ (j,i)\in E\big].
--   $$
--   Full information, apple tasting (one action observes both losses, the other nothing) and every tournament with all self-loops are strongly revealing; a bandit pair (two self-loops, no edge between them) and a loopless pair (each observes only the other) violate the condition.
--
--   This is the condition that separates the $\sqrt T$ regime from the $T^{2/3}$ regime of the characterization.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Definition 1, Eq. (13), p.14 (PDF p.16)

import Mathlib
import Definitions.Def_FeedbackSwitching_FeedbackGraph

namespace FeedbackSwitching

/-- **Strongly revealing graph** (Definition 1, Eq. (13), p.14 = PDF p.16). Cesa-Bianchi et al.,
arXiv:2606.03851 (held version, sha256 ded8f8bc…). `G` is strongly revealing if every pair of
distinct actions has an endpoint that observes the losses of both:
for every `i ≠ j`, `[(i, i) ∈ E and (i, j) ∈ E]` or `[(j, j) ∈ E and (j, i) ∈ E]`. -/
def StronglyRevealing {K : ℕ} (G : FeedbackGraph K) : Prop :=
  ∀ i j : Fin K, i ≠ j → (G i i ∧ G i j) ∨ (G j j ∧ G j i)

end FeedbackSwitching


