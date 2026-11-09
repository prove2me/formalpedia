-- Prove2me | Definitions.Def_NondetConn_Auv
-- name    : NondetConn_Auv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:21:25.051007+00:00
-- url     : https://prove2.me/theorems/bc88aaef-fb98-4c82-9ad0-92f6afa75499
-- title:
--   Restricted family $\mathcal A_{(u,v)}$
-- statement:
--   For a set $\mathcal A$ of permutations of $[n]$ and $u, v \in [n]$,
--   $$
--   \mathcal A_{(u,v)} = \{a_{(u,v)} \mid a \in \mathcal A,\ a(u) = v\},
--   $$
--   the set of restrictions to $[n]\setminus\{u\}$ of the members of $\mathcal A$ that send $u$ to $v$.
--
--   **Formalization Note** Each $a_{(u,v)}$ is recorded as the map $x \mapsto a(x)$ on $[n]\setminus\{u\}$ with values in $[n]$; distinct restrictions give distinct maps, so $|\mathcal A_{(u,v)}|$ is the paper's cardinality.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.10 (PDF p.12)

import Mathlib

namespace NondetConn

/-- **The restricted family `𝒜_(u,v)`** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac),
§4.1, p.10): for a set `𝒜` of permutations of `[n]` and `u, v ∈ [n]`,
`𝒜_(u,v) = {a_(u,v) | a ∈ 𝒜, a(u) = v}`, the set of restrictions to `[n] \ {u}` of the members
of `𝒜` that send `u` to `v`.

**Formalization Note** Each `a_(u,v)` is recorded as the map `x ↦ a x` on `{x // x ≠ u}` with
values in `Fin n` (its values avoid `v`); distinct restrictions give distinct maps, so the
cardinality is that of the paper's set. -/
def Auv {n : ℕ} (𝒜 : Finset (Equiv.Perm (Fin n))) (u v : Fin n) :
    Finset ({x : Fin n // x ≠ u} → Fin n) :=
  (𝒜.filter (fun a => a u = v)).image (fun a x => a x.1)

end NondetConn


