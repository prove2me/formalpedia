-- Prove2me | Definitions.Def_FASTournament_mu
-- name    : FASTournament_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:28.149232+00:00
-- url     : https://prove2.me/theorems/29f5d64a-80c3-4872-8bc6-8f994e204e55
-- title:
--   $\mu_w(G)$: minimum weight of a directed cycle
-- statement:
--   For a digraph $G$ with nonnegative integral arc weights $w$,
--   $$
--   \mu_w(G)=\min\Big\{\sum_{e\in C}w(e) : C \text{ a directed cycle of } G\Big\}.
--   $$
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$ (`ℕ∞`); if $G$ has no directed cycle the minimum over the empty family is $\infty$.
-- source:
--   Chen, Ding, Zang & Zhao, Packing Feedback Arc Sets in Tournaments Exactly, Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3

import Mathlib
import Definitions.Def_FASTournament_Arc
import Definitions.Def_FASTournament_IsDirCycle

namespace FASTournament

/-- **`µ_w(G)`, the minimum weight of a directed cycle.**
Chen, Ding, Zang & Zhao, *Packing Feedback Arc Sets in Tournaments Exactly*,
Math. Oper. Res. (2024), doi:10.1287/moor.2023.1352, p.3: "let µw(G) be the minimum total weight of a cycle (directed)".

**Formalization Note.** The value is in `ℕ∞`; the infimum over the empty family is `⊤`, so
`µ_w(G) = ⊤` when `G` has no directed cycle. -/
noncomputable def mu {V : Type*} (G : Digraph V) (w : Arc G → ℕ) : ℕ∞ :=
  ⨅ (C : Finset (Arc G)) (_ : IsDirCycle G C), ((∑ e ∈ C, w e : ℕ) : ℕ∞)

end FASTournament


