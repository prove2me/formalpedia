-- Prove2me | Definitions.Def_KnodelPrimeCordial_vtx
-- name    : KnodelPrimeCordial_vtx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T05:59:12.961206+00:00
-- url     : https://prove2.me/theorems/b0b48f43-bf21-44ed-b686-f663f4c299a6
-- title:
--   The vertex names $v_i$ of $W_{\Delta,n}$
-- statement:
--   The paper names the vertices of $W_{\Delta,n}$ by a single index read modulo $n$: $v_{2j}$ is the vertex $(1,j)$ and $v_{2j-1}$ is the vertex $(2,j)$. Equivalently, for $0\le i\le n-1$,
--
--   $$
--   v_i=\begin{cases}(1,\ i/2), & i\text{ even},\\ (2,\ (i+1)/2 \bmod n/2), & i\text{ odd},\end{cases}
--   $$
--
--   so that, for instance, $v_{n-1}=v_{-1}=(2,0)$. For even $n$ this is a bijection from $\{0,\dots,n-1\}$ onto the vertex set.
--
--   **Formalization Note** The sides $1,2$ are the `Fin 2` values $0,1$, as in the definition of $W_{\Delta,n}$. The map takes a proof of $0<n/2$, which only makes the target type nonempty; for even $n$ the reduction of $i/2$ modulo $n/2$ in the even case is the identity.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), §1, p.3 (PDF p.3), "let v2j represent vertex (1,j) and v2j−1 represent vertex (2,j)"

import Mathlib

namespace KnodelPrimeCordial

/-- **The paper's vertex names `v_i` of `W_{Δ,n}`** (Haque, Khanam, Shahriar, *Prime cordial
labeling of Knödel graph*, manuscript (2026), §1, p.3): "For W∆,n, let v2j represent vertex
(1,j) and v2j−1 represent vertex (2,j). In this paper, the vertex labels are read modulo n".

`vtx n h i` is the vertex of `W_{Δ,n}` named `v_i`: for even `i`, `v_i = (1, i/2)`; for odd
`i`, `v_i = (2, (i+1)/2 mod n/2)` (from `v_{2j−1} = (2, j)` with `j = (i+1)/2`; so
`v_{n−1} = v_{−1} = (2, 0)`).

**Formalization Note** The sides `1, 2` are the `Fin 2` values `0, 1`, as in `knodel`. The
hypothesis `h : 0 < n / 2` only makes `Fin (n / 2)` nonempty; for even `n` the reduction
`i / 2 mod n/2` of an even index is the identity. -/
def vtx (n : ℕ) (h : 0 < n / 2) (i : Fin n) : Fin 2 × Fin (n / 2) :=
  if i.val % 2 = 0 then (0, ⟨(i.val / 2) % (n / 2), Nat.mod_lt _ h⟩)
  else (1, ⟨((i.val + 1) / 2) % (n / 2), Nat.mod_lt _ h⟩)

end KnodelPrimeCordial


