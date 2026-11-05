-- Prove2me | Definitions.Def_ReusableMatching_window
-- name    : ReusableMatching_window
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:30.989125+00:00
-- url     : https://prove2.me/theorems/90506d23-f8bd-452d-a776-05f0d6f48c6c
-- title:
--   The dual window $\{t : \max\{j-d+1,1\}\le t\le j\}$ of an arrival
-- statement:
--   For an arrival $j$ the **dual window** is the set of arrivals $t$ with
--
--   $$
--   \max\{j-d+1,1\}\le t\le j,
--   $$
--
--   that is, the arrivals in the last $d$ steps up to and including $j$. The dual constraint of an edge $(i,j)$ in the LP of §2 is $\beta_j+\sum_{t\in\text{window}(j)}\alpha_{i,t}\ge r_i$.
--
--   **Formalization Note** With arrivals numbered from $0$, the window of $j$ is $\{t: t\le j,\ j<t+d\}$.
-- source:
--   Delong, Farhadi, Niazadeh, Sivan & Udwani, Online Bipartite Matching with Reusable Resources, arXiv:2110.07084v2, LP (D) and Lemma 1, p.6

import Mathlib
import Definitions.Def_ReusableMatching_OBMRRInstance

namespace ReusableMatching

/-- **The dual window of an arrival** (arXiv:2110.07084v2, LP (D), p.6, and Lemma 1, p.6): the
arrivals `t` with `max{j − d + 1, 1} ≤ t ≤ j`, over which the dual constraint
`β_j + ∑_{t = max{j−d+1,1}}^{j} α_{i,t} ≥ r_i` of the edge `(i, j)` sums.

**Formalization Note.** With `0`-based arrivals the window of `j` is
`{t : t ≤ j and j < t + d}`; the lower end `max{j − d + 1, 1}` of the paper becomes the condition
`j < t + d` (and the bound `t ≥ 0` of `Fin n`). -/
def window {V : Type*} {n : ℕ} (I : OBMRRInstance V n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun t : Fin n => t ≤ j ∧ (j : ℕ) < (t : ℕ) + I.d)

end ReusableMatching


