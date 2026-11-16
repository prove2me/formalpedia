-- Prove2me | Definitions.Def_CompDesignBFM_Supplement_lbValue
-- name    : CompDesignBFM_Supplement_lbValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:05:03.658029+00:00
-- url     : https://prove2.me/theorems/ade12a68-20c0-4846-b251-248056ec2438
-- title:
--   The XOS value function (34) of the PoA lower bound
-- statement:
--   Fix an integer $k\ge1$ and let $m=k^4$. The $n=mk=k^5$ agents are partitioned into $m$ groups $N_1,\dots,N_m$ of $k$ agents each, and
--
--   $$v(S)=\max\Bigl\{\tfrac2m|S|,\ \max_{j\in[m]}|S\cap N_j|\Bigr\}\qquad(S\subseteq N).$$
--
--   This normalized monotone XOS function (Lemma B.1) is the value function of the instance on which every randomized compensation rule has price of anarchy $\Omega(n^{1/5})$.
--
--   **Formalization Note** Agents are $\{0,\dots,k^5-1\}$ and agent $i$ belongs to group $\lfloor i/k\rfloor\in\{0,\dots,k^4-1\}$.
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, App. B, eq. (34), p.41 (PDF 43), with m = k⁴, n = k⁵

import Mathlib

namespace CompDesignBFM

namespace Supplement

/-- The XOS value function (34) of the price-of-anarchy lower bound (Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, App. B, eq. (34), p.41,
PDF 43), on the instance `m = k⁴`, `n = mk = k⁵`:
`v(S) = max { (2/m) |S|, max_(j ∈ [m]) |S ∩ N_j| }`, where the agents are split into `m` groups
`N_1, …, N_m` of `k` agents each.
**Formalization Note.** Agents are `Fin (k ^ 5)` and groups are indexed by `Fin (k ^ 4)`; agent `i`
belongs to group `i / k` (natural-number division), so group `j` is `{jk, …, jk + k − 1}`, of size `k`
for `k ≥ 1`. The inner maximum is a `Finset.sup` of natural numbers (all values are `≥ 0`, so the
default `0` of an empty supremum changes nothing). -/
noncomputable def lbValue (k : ℕ) (S : Finset (Fin (k ^ 5))) : ℝ :=
  max (2 / (k ^ 4 : ℝ) * S.card)
    (((Finset.univ : Finset (Fin (k ^ 4))).sup fun j => (S.filter fun i => i.val / k = j.val).card : ℕ) : ℝ)

end Supplement

end CompDesignBFM


