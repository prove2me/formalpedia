-- Prove2me | Definitions.Def_PacingComplexity_highBid
-- name    : PacingComplexity_highBid
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:19.996411+00:00
-- url     : https://prove2.me/theorems/dbc7016c-d851-42b4-9d32-e0b1334e3b89
-- title:
--   Highest bid $h_j(\alpha)$
-- statement:
--   Given values $v_{ij}$ and pacing multipliers $\alpha=(\alpha_i)$, buyer $i$ bids $\alpha_i v_{ij}$ on good $j$, and the **highest bid** on good $j$ is
--   $$
--   h_j(\alpha)=\max_{i\in[n]}\alpha_i v_{ij}.
--   $$
--   Only buyers whose bid is (close to) $h_j(\alpha)$ may win good $j$ in an (approximate) pacing equilibrium.
--
--   **Formalization Note** Written as the real supremum over the finite set of buyers, which is the maximum when there is at least one buyer (the supremum over an empty set is $0$ in Lean; instances of the search problem have at least two buyers).
-- source:
--   Chen, Kroer, Kumar, The Complexity of Pacing for Second-Price Auctions, arXiv:2103.13969v2, §2, p.7

import Mathlib

namespace PacingComplexity

/-- **Highest bid** `h_j(α)` on good `j` (Chen, Kroer, Kumar, *The Complexity of Pacing for
Second-Price Auctions*, arXiv:2103.13969v2, §2, p.7): "we let hj(α) = max_{i∈[n]} αi vij denote
the highest bid on good j", where buyer `i` bids `αi vij` on good `j`.

**Formalization Note** Written as the real supremum `⨆ i, α i * v i j` over the finite type of
buyers, which is the maximum when there is at least one buyer (Lean's `⨆` over an empty type is
`0`; instances of `ApproxPacing` have at least two buyers). -/
noncomputable def highBid {N G : Type} (v : N → G → ℝ) (α : N → ℝ) (j : G) : ℝ :=
  ⨆ i : N, α i * v i j

end PacingComplexity


