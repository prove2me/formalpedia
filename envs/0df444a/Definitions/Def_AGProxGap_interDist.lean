-- Prove2me | Definitions.Def_AGProxGap_interDist
-- name    : AGProxGap_interDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:36.623824+00:00
-- url     : https://prove2.me/theorems/181b059b-7cdc-4fa1-b576-674fa2f66527
-- title:
--   Interleaved distance $d([u_0,\dots,u_\ell],[c_0,\dots,c_\ell])$
-- statement:
--   For $u_0,\dots,u_\ell,c_0,\dots,c_\ell\in\mathbb F_q^n$, view the interleavings $[u_0,\dots,u_\ell]$ and $[c_0,\dots,c_\ell]$ as words of length $n$ over the alphabet $\mathbb F_q^{\ell+1}$. The **interleaved distance** is
--   $$
--   d([u_0,\dots,u_\ell],[c_0,\dots,c_\ell])=\bigl|\{\,i\in[n] : (u_{0,i},\dots,u_{\ell,i})\ne(c_{0,i},\dots,c_{\ell,i})\,\}\bigr| .
--   $$
--   A coordinate counts once if any of the $\ell+1$ entries differ. Thus $d([u],[c])\le t$ means that $u_0,\dots,u_\ell$ agree with $c_0,\dots,c_\ell$ on one common set of at least $n-t$ coordinates.
--
--   **Formalization Note** Mathlib's `hammingDist` of the transposed words `fun i j => u j i`, with classical decidability.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.1, p.13

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical

namespace AGProxGap

/-- **Interleaved distance** `d([u_0, …, u_ℓ], [c_0, …, c_ℓ])`, the number of coordinates
`i ∈ [n]` with `(u_{0,i}, …, u_{ℓ,i}) ≠ (c_{0,i}, …, c_{ℓ,i})` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.1, p.13: "We view
[u_0, . . . , u_ℓ] and [c_0, . . . , c_ℓ] as words in (F_q^{ℓ+1})^n").

**Formalization Note** The interleaved word is `fun i j => u j i : Fin n → (Fin (ℓ+1) → K)`,
and the distance is Mathlib's `hammingDist` over the alphabet `K^{ℓ+1}`: a coordinate counts
once if any of the `ℓ + 1` entries differs (not a sum over `j`). Decidability is classical. -/
noncomputable def interDist {K : Type*} {n ℓ : ℕ} (u c : Fin (ℓ + 1) → Fin n → K) : ℕ :=
  hammingDist (fun i j => u j i) (fun i j => c j i)

end AGProxGap


