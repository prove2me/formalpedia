-- Prove2me | Definitions.Def_PertComp_subdiffPre
-- name    : PertComp_subdiffPre
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:28.508008+00:00
-- url     : https://prove2.me/theorems/ebe2660f-7b66-4661-8975-3107f0892323
-- title:
--   Subdifferential of a function on a dual space, read in $V$
-- statement:
--   Let $V$ be a real normed space and $k\colon V^*\to[-\infty,+\infty]$. The subdifferential (2.6) of $k$ at $v^*$ is a subset of $V^{**}$: the functionals $\nu$ with $k(v^*)+\nu(w^*-v^*)\le k(w^*)$ for every $w^*\in V^*$. When $V$ is reflexive the paper identifies $V^{**}$ with $V$, so that
--   $$\partial k(v^*)=\{v\in V : k(v^*)+\langle v,w^*-v^*\rangle\le k(w^*)\ \text{for all } w^*\in V^*\}.$$
--   This is how $\partial g^*$, $\partial\ell^*$, $\partial f^*$ and the second factor of the Kuhn–Tucker operator (2.26) are read.
--
--   **Formalization Note** The set of $v\in V$ whose canonical image $Jv\in V^{**}$ lies in `RockafellarMaxMono.Shared.subdiff k v'`. Every statement using it assumes $V$ reflexive.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, (2.6), p.5, and (2.26), p.9

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, (2.6), p.5, applied to a function `k` on a dual
space `V*`: its subdifferential `∂k(v*)` is a subset of `V** = V` (reflexive spaces). This is the
set of `v ∈ V` whose canonical image `Jv ∈ V**` is a subgradient of `k` at `v*`, i.e.
`k(v*) + ⟨v, w* − v*⟩ ≤ k(w*)` for every `w* ∈ V*`.

**Formalization Note.** The published `RockafellarMaxMono.Shared.subdiff` puts subgradients of
`k : V* → EReal` in `V**`; this pulls them back to `V` through
`NormedSpace.inclusionInDoubleDual`. Under reflexivity (every statement of the mission assumes
it) this is the paper's identification `V** = V`. -/
def subdiffPre {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : StrongDual ℝ V → EReal) (v' : StrongDual ℝ V) : Set V :=
  {v | NormedSpace.inclusionInDoubleDual ℝ V v ∈ RockafellarMaxMono.Shared.subdiff k v'}

end PertComp


