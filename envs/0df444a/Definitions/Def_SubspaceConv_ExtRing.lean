-- Prove2me | Definitions.Def_SubspaceConv_ExtRing
-- name    : SubspaceConv_ExtRing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:16.810383+00:00
-- url     : https://prove2.me/theorems/0d3e44c1-2393-45c8-a01e-ecf04fed45ce
-- title:
--   The coefficient ring $R[t]/(1+t+\dots+t^{p-1})$ and block decoding
-- statement:
--   For a commutative ring $R$ and the characteristic $p$ of $\mathbb F_q$, §3.4 works in
--   $$R[t]/(1+t+\dots+t^{p-1}),\qquad \zeta=t\bmod(1+t+\dots+t^{p-1}),$$
--   whose elements have unique expansions $\sum_{i=0}^{p-2}c_i\zeta^i$ with $c_i\in R$. **Block decoding** sends a block $(c_0,\dots,c_{p-2})$ of $p-1$ elements of $R$ to $\sum_i c_i\zeta^i$; programs over $R$ act on such blocks to carry out arithmetic in the extension.
--
--   **Formalization Note** `AdjoinRoot` of the polynomial $\sum_{i<p}X^i$; $\zeta$ is `AdjoinRoot.root`. $p$ is a natural-number parameter.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.4, p.13

import Mathlib

namespace SubspaceConv

open Polynomial

/-- The coefficient ring of §3.4, `R[t]/(1 + t + ⋯ + t^{p−1})` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.4, p.13). Its
class of `t` is `ζ = AdjoinRoot.root _`.

**Formalization Note** `AdjoinRoot` of the polynomial `∑_{i<p} X^i` over the commutative ring
`A`; `p` is a natural-number parameter (the theorems take `p` prime, or `p = ringChar F`). -/
noncomputable abbrev ExtRing (A : Type*) [CommRing A] (p : ℕ) : Type _ :=
  AdjoinRoot (∑ i ∈ Finset.range p, (X : A[X]) ^ i)

/-- Block decoding: a block of `p − 1` elements `c_0, …, c_{p−2}` of `A` represents the element
`∑_i c_i ζ^i` of `ExtRing A p` ("a unique expansion in `1, t, …, t^{p−2}`", Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §3.4,
p.13). Programs over `A` act on such blocks to implement arithmetic in the extension. -/
noncomputable def dec {A : Type*} [CommRing A] {p : ℕ} (c : Fin (p - 1) → A) : ExtRing A p :=
  ∑ i : Fin (p - 1), AdjoinRoot.of _ (c i) * AdjoinRoot.root _ ^ (i : ℕ)

end SubspaceConv


