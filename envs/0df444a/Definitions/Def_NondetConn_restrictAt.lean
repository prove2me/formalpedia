-- Prove2me | Definitions.Def_NondetConn_restrictAt
-- name    : NondetConn_restrictAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:20:11.583262+00:00
-- url     : https://prove2.me/theorems/a217e125-bcc4-4938-8ac2-dd10716e84b6
-- title:
--   Restriction $a_{(u,v)}$ of a permutation to $[n]\setminus\{u\}$
-- statement:
--   For a permutation $a$ of $[n]$ and $u \in [n]$, put $v = a(u)$. The **restriction** $a_{(u,v)} : [n]\setminus\{u\} \to [n]\setminus\{v\}$ is $a$ restricted to $[n]\setminus\{u\}$; it is a bijection.
--
--   It is the Alice side of the reduction from $n$ to $n-1$ in Section 4.1.
--
--   **Formalization Note** The point $v$ is taken to be $a(u)$, so the codomain is $[n]\setminus\{a(u)\}$.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.10 (PDF p.12)

import Mathlib

namespace NondetConn

/-- **Restriction `a_(u,v)`** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1,
p.10): for a permutation `a` of `[n]` and `u ∈ [n]` with `v = a(u)`, the restriction of `a` to
`[n] \ {u}`, a bijection `[n] \ {u} → [n] \ {v}`.

**Formalization Note** The point `v` is `a u` itself, so the codomain is `{y // y ≠ a u}`;
`[n] \ {u}` is the subtype `{x // x ≠ u}`. -/
def restrictAt {n : ℕ} (a : Equiv.Perm (Fin n)) (u : Fin n) :
    {x : Fin n // x ≠ u} ≃ {y : Fin n // y ≠ a u} :=
  a.subtypeEquiv (fun _ => a.injective.ne_iff.symm)

end NondetConn


