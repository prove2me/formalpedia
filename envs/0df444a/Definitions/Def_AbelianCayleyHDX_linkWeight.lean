-- Prove2me | Definitions.Def_AbelianCayleyHDX_linkWeight
-- name    : AbelianCayleyHDX_linkWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:48.671302+00:00
-- url     : https://prove2.me/theorems/9cb0c547-aa83-4d29-9205-99d3ece1e345
-- title:
--   Edge weights of the link of a vertex
-- statement:
--   For a triangle set $T$ with the uniform distribution and a vertex $v$, the link of $v$ carries the top-face distribution obtained by conditioning on $v \in \tau$: its top faces are the edges $\{u, w\}$ with $\{v, u, w\} \in T$, all of equal weight. The (unnormalized) link weight is
--   $$w_v(u, w) = \begin{cases} 1 & \{v, u, w\} \in T,\\ 0 & \text{otherwise.}\end{cases}$$
--
--   **Formalization Note** The normalizing factor (the number of triangles through $v$) is omitted: the random-walk operator and the spectral condition of Section 2.2 are invariant under scaling of all weights. For $u = w$ the set $\{v,u,u\}$ is not a triangle, so the weight is $0$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **The edge weights of the link of a vertex** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8): the link of `v`
carries the top-face distribution obtained by conditioning the uniform distribution on `T` on
`v ∈ τ`; its top faces are the edges `{u, w}` with `{v, u, w} ∈ T`, all of equal weight.

**Formalization Note** The weight is unnormalized: `1` on a link edge, `0` otherwise. The
conditioned distribution is this function divided by the number of triangles through `v`; the
random-walk operator and the spectral condition of Section 2.2 do not change under scaling. For
`u = w` the set `{v, u, u}` has at most two elements, is not a triangle, and gets weight `0`. -/
noncomputable def linkWeight {n : ℕ} (T : Finset (Finset (Vec n))) (v u w : Vec n) : ℝ :=
  if ({v, u, w} : Finset (Vec n)) ∈ T then 1 else 0

end AbelianCayleyHDX


