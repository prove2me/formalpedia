-- Prove2me | Definitions.Def_MWCSherali_MWCInst_IsTerminalLabeling
-- name    : MWCSherali_MWCInst_IsTerminalLabeling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:10.853215+00:00
-- url     : https://prove2.me/theorems/6ceb4dca-3438-4eb0-b828-d2a678815f33
-- title:
--   Multiway cuts as terminal labelings
-- statement:
--   A **multiway cut** of an instance $G$ with terminals $\tau_0,\dots,\tau_{k-1}$ is a partition of $V$ into $k$ parts, each containing exactly one terminal. It is described by a labeling $g:V\to\{0,\dots,k-1\}$ with
--
--   $$g(\tau_i)=i\qquad\text{for every terminal }i,$$
--
--   part $i$ being $g^{-1}(i)$. Every such partition, with its parts named after their terminals, arises this way. Its weight is $\operatorname{cut}_G(g)=\sum_{\{u,v\}\in E}w_{uv}\mathbf 1[g(u)\neq g(v)]$ (the published `Max3CutHard.cutK`), and Multiway Cut asks to minimize it.
--
--   **Formalization Note** Parts other than the terminals' parts may be empty, as in the paper's partition into $k$ parts.
-- source:
--   Brakensiek–Huang–Potechin–Zwick, Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations, arXiv:2611.05511 (version of Nov. 3, 2026), §1, p.2

import Mathlib
import Definitions.Def_MWCSherali_MWCInst

namespace MWCSherali

/-- **Multiway cuts as terminal labelings.** Brakensiek–Huang–Potechin–Zwick, *Improved lower bounds on the approximability of Multiway Cut using Sherali–Adams relaxations*,
arXiv:2611.05511 (version of Nov. 3, 2026), §1, p.2: "a partition of `V` into `k`
parts, each containing exactly one terminal".

A map `g : V → [k]` with `g(term i) = i` for every terminal `i` describes such a partition: part
`i` is `g⁻¹(i)`, which contains terminal `i` and no other terminal. Conversely every such
partition, with its parts named after their terminals, is of this form.

**Formalization Note.** Parts are indexed by `Fin k` (0-based); parts other than the terminals'
may be empty, as in the paper's partition into `k` parts each containing one terminal. The
weight of the cut is `Max3CutHard.cutK G.k G.graph g`. -/
def MWCInst.IsTerminalLabeling (G : MWCInst) (g : Fin G.graph.n → Fin G.k) : Prop :=
  ∀ i, g (G.term i) = i

end MWCSherali


