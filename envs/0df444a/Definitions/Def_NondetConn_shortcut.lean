-- Prove2me | Definitions.Def_NondetConn_shortcut
-- name    : NondetConn_shortcut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:20:19.243167+00:00
-- url     : https://prove2.me/theorems/ea8cac17-7d09-4589-afeb-52f3c8364fe1
-- title:
--   Shortcut map $b_{(u,v)}$
-- statement:
--   For a permutation $b$ of $[n]$ and $u, v \in [n]$, the **shortcut** $b_{(u,v)} : [n]\setminus\{u\} \to [n]\setminus\{v\}$ is the same as $b$ except that $b_{(u,v)}(b^{-1}(v)) = b(u)$: it redirects the preimage of $v$ to the image of $u$. For $x \ne u$,
--   $$
--   b_{(u,v)}(x) = \begin{cases} b(u) & \text{if } x = b^{-1}(v),\\ b(x) & \text{otherwise.}\end{cases}
--   $$
--
--   It is the Bob side of the reduction from $n$ to $n-1$ in Section 4.1.
--
--   **Formalization Note** Built as the restriction to $[n]\setminus\{u\}$ of the permutation $\tau\circ b$, where $\tau$ swaps $b(u)$ and $v$; this permutation sends $u$ to $v$, so the restriction is a bijection onto $[n]\setminus\{v\}$, and on $x \ne u$ it is the displayed formula. When $b(u) = v$ (a case the paper never uses) it is the plain restriction of $b$.
-- source:
--   Zhang, Settling Nondeterministic Communication Complexity of Graph Connectivity, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1, p.10 (PDF p.12)

import Mathlib

namespace NondetConn

/-- **Shortcut `b_(u,v)`** (Zhang, *Settling Nondeterministic Communication Complexity of Graph Connectivity*, arXiv:2610.32346 (held version, sha256 1d4f00d1…4e7ac), §4.1,
p.10): for a permutation `b` of `[n]` and `u, v ∈ [n]`, the map `[n] \ {u} → [n] \ {v}` that
agrees with `b` except that `b_(u,v)(b⁻¹(v)) = b(u)`: it redirects the preimage of `v` to the
image of `u`. Explicitly, for `x ≠ u`,
`b_(u,v)(x) = b(u)` if `x = b⁻¹(v)` and `b_(u,v)(x) = b(x)` otherwise.

**Formalization Note** Built as the restriction to `{x // x ≠ u}` of the permutation
`swap (b u) v * b`, which sends `u ↦ v`; on `x ≠ u` it takes the value `b u` at `x = b⁻¹ v` and
`b x` elsewhere (the paper's formula, proved in the mission's sanity file). This makes it a
bijection `{x // x ≠ u} ≃ {y // y ≠ v}` for all `u, v`; when `b u = v` it is the plain restriction
of `b` (the paper only uses `b u ≠ v`). -/
def shortcut {n : ℕ} (b : Equiv.Perm (Fin n)) (u v : Fin n) :
    {x : Fin n // x ≠ u} ≃ {y : Fin n // y ≠ v} :=
  (Equiv.swap (b u) v * b).subtypeEquiv (fun x => by
    simp only [Equiv.Perm.mul_apply, ne_eq]
    constructor
    · intro hx h
      have h' : b x = b u := by
        have h2 : (Equiv.swap (b u) v) (b x) = (Equiv.swap (b u) v) (b u) := by
          rw [h, Equiv.swap_apply_left]
        exact (Equiv.swap (b u) v).injective h2
      exact hx (b.injective h')
    · intro h hx
      exact h (by rw [hx, Equiv.swap_apply_left]))

end NondetConn


