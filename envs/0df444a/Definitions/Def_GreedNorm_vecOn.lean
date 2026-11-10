-- Prove2me | Definitions.Def_GreedNorm_vecOn
-- name    : GreedNorm_vecOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:49.965902+00:00
-- url     : https://prove2.me/theorems/cff1a1ef-e897-4c88-890f-a0e962897572
-- title:
--   Restriction $v[S]$ of a value vector
-- statement:
--   For values $v:U\to\mathbb R$ and $S\subseteq U$, the vector
--
--   $$
--   v[S]=\bigl(v(e)\cdot\mathbf 1\{e\in S\}\bigr)_{e\in U}.
--   $$
--
--   With $v=p_i$ (the row of machine $i$) this gives the GLB load function $\mathrm{load}_i(S)=f_i(p_i[S])$.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 3.13, p.9 (PDF 11); §1, pp.1–2 (PDF 3–4)

import Mathlib

namespace GreedNorm

/-- **The restriction `v[S]` of a value vector to a set `S`**: the vector `(v(e)·1{e ∈ S})_{e ∈ U}`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 3.13, p.9 (PDF 11): "v[S] is the n-dimensional vector (v(e) · 1{e∈S})e∈U"; also
§1, p.1 (PDF 3) and the GLB instance of NestedCostAlloc, p.2 (PDF 4), `loadi(S) = fi(pi[S])`.

**Formalization Note** The vector is a function `U → ℝ`, equal to `v e` on `S` and `0` off `S`. -/
def vecOn {U : Type} [DecidableEq U] (v : U → ℝ) (S : Finset U) : U → ℝ :=
  fun e => if e ∈ S then v e else 0

end GreedNorm


