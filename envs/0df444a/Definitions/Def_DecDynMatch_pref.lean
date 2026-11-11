-- Prove2me | Definitions.Def_DecDynMatch_pref
-- name    : DecDynMatch_pref
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:57.368054+00:00
-- url     : https://prove2.me/theorems/7f6c5b8a-6cce-4ff2-87ab-66e718f2a5bf
-- title:
--   Player ranking $p_i(r)$
-- statement:
--   For a player $i$ with strict utilities $\mu_{i,\cdot}$, let $\operatorname{rank}_i(k)$ be the number of arms that $i$ strictly prefers to arm $k$. The **ranking** $p_i(r)$, $r=1,\dots,K$, is player $i$'s $r$-th most preferred arm, i.e. the unique arm $k$ with $\operatorname{rank}_i(k)=r-1$.
--
--   The protocol uses $p_i(1)$ in the Top stage of Work and $p_i(k)$ in its deferred-acceptance stage.
--
--   **Formalization Note** `pref I i r` is 0-based: `pref I i r` $=p_i(r+1)$. It is found by searching the arms $0,\dots,K-1$ for the one of rank $r$; for $r\ge K$ (never used) it defaults to arm $0$.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.1, p.4

import Mathlib
import Definitions.Def_DecDynMatch_Instance

namespace DecDynMatch

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- `rank I i k` is the number of arms that player `i` strictly prefers to arm `k`
(arms `k'` with `μᵢ,ₖ < μᵢ,ₖ'`). With strict rankings it is a bijection `Fin K → {0, …, K − 1}`. -/
noncomputable def rank (I : Instance K ι) (i : ι) (k : Fin K) : ℕ :=
  (Finset.univ.filter (fun k' => I.μ i k < I.μ i k')).card

/-- **Player ranking `pᵢ(r)`.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable
Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.1, p.4: "Let pᵢ(r) denote player
i's r-th most preferred arm (r = 1, 2, …, K)."

`pref I i r` is the arm with exactly `r` strictly better arms, i.e. `pref I i r = pᵢ(r + 1)`.

**Formalization Note.** The index is 0-based: `pref I i 0 = pᵢ(1)` and `pref I i (k - 1) = pᵢ(k)`.
It is computed by searching the arms `0, …, K − 1` for the one of rank `r`; strict rankings
make that arm unique and existent for `r < K`. For `r ≥ K` (never used) the search fails and the
value defaults to arm `0`. -/
noncomputable def pref (I : Instance K ι) (i : ι) (r : ℕ) : Fin K :=
  ((List.finRange K).find? (fun k => decide (rank I i k = r))).getD (bus I)

end DecDynMatch


