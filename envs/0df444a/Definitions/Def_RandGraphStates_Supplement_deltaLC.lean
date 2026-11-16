-- Prove2me | Definitions.Def_RandGraphStates_Supplement_deltaLC
-- name    : RandGraphStates_Supplement_deltaLC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:20:49.049935+00:00
-- url     : https://prove2.me/theorems/87ebc9a6-03a6-4a63-9cee-c80a82f91072
-- title:
--   The minimum degree up to local complementation $\delta_{\mathrm{LC}}(G)$
-- statement:
--   Let $G$ be a finite simple graph and write $\delta(H)$ for the minimum degree of a graph $H$. The **minimum degree up to local complementation** of $G$ is the smallest minimum degree among all graphs LC-equivalent to $G$,
--   $$
--   \delta_{\mathrm{LC}}(G):=\min\{\delta(H): H\equiv_{\mathrm{LC}}G\},
--   $$
--   where $H\equiv_{\mathrm{LC}}G$ means that $H=G\star v_1\star\cdots\star v_t$ for some sequence of vertices $v_1,\dots,v_t$ (possibly empty), and $G\star v$ is the local complementation of $G$ at $v$.
--
--   For a graph state $|G\rangle$, $\delta_{\mathrm{LC}}(G)+1$ is the distance of the state (the smallest support of a non-identity stabilizer), so $\delta_{\mathrm{LC}}$ measures how many parties must be measured before outcomes stop being completely random.
--
--   **Formalization Note** Local complementation and LC-equivalence are the published base definitions of `RandGraphStates_alphaLC`. The minimum is an infimum in $\mathbb N$ over a family that contains $\delta(G)$, so it is attained; $\delta(H)$ is Mathlib's `SimpleGraph.minDegree`, which is $0$ on the empty vertex set.
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), §2.1, p.4

import Mathlib
import Definitions.Def_RandGraphStates_alphaLC

set_option autoImplicit false

namespace RandGraphStates.Supplement

open RandGraphStates

/-- `δLC(G) := min{δ(H) : H is LC-equivalent to G}`, the minimum degree up to local complementation.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript
(November 2026), §2.1, p.4.

**Formalization Note.** `LCEquiv` (and `localComplement`) are the published base definitions of
`RandGraphStates_alphaLC`. The minimum is an infimum in `ℕ`; the family is nonempty (it contains
`δ(G)`, via the empty sequence), so the infimum is attained and is the printed minimum
(`Solutions/verification/RandGraphStates_Supplement_Sanity.lean`). `δ(H)` is Mathlib's
`SimpleGraph.minDegree`, which is `0` on the empty vertex type; decidability of adjacency is
classical. -/
noncomputable def deltaLC {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ H : SimpleGraph V, LCEquiv G H ∧
    k = (by classical exact H.minDegree)}

end RandGraphStates.Supplement


