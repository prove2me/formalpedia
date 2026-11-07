-- Prove2me | Definitions.Def_GyoriLovasz_PT
-- name    : GyoriLovasz_PT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:11.703593+00:00
-- url     : https://prove2.me/theorems/39441984-d601-4038-a0e0-c9a00ae03140
-- title:
--   Pre-terminals $\mathrm{PT}(G,S)$
-- statement:
--   A vertex $p\in V\setminus T$ is a **pre-terminal** if it has an outgoing edge $(p,t)$ to some terminal $t\in T$. For $S\subseteq T$, $\mathrm{PT}(G,S)$ is the set of pre-terminals with an outgoing edge to a terminal of $S$:
--   $$\mathrm{PT}(G,S)=\{p\in V\setminus T:\exists\,t\in S,\ (p,t)\in E\}.$$
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Definition 2.1, p.14

import Mathlib
import Definitions.Def_GyoriLovasz_DG

namespace GyoriLovasz

/-- **Pre-terminals `PT(G, S)`.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, *Breaking the Exponential Barrier*,
arXiv:2608.30945 (held file sha256 3f80f82d…780e), Definition 2.1, p.14: "A vertex p ∈ V \ T is a pre-terminal if it
has an outgoing edge (p, t) to some terminal t ∈ T. For a subset S ⊆ T, we let PT(G, S) denote the set
of pre-terminals with an outgoing edge to a terminal in S."

**Formalization Note.** The terminal set `T` is an explicit argument, because a pre-terminal must be a
non-terminal even when `S ⊂ T`. -/
def PT {V : Type*} [DecidableEq V] (G : DG V) (T S : Finset V) : Finset V :=
  (G.verts \ T).filter fun p => ∃ t ∈ S, (p, t) ∈ G.arcs

end GyoriLovasz


