-- Prove2me | Definitions.Def_IntADSat_Supplement_caterpillarGraph
-- name    : IntADSat_Supplement_caterpillarGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:51:49.282161+00:00
-- url     : https://prove2.me/theorems/5ae1370f-2b16-45d2-b8c0-d4a8064181cf
-- title:
--   Ordinary caterpillar $C(a_0,\dots,a_k)$
-- statement:
--   For $k\ge0$ and nonnegative integers $a_0,\dots,a_k$, the **ordinary caterpillar** $C(a_0,\dots,a_k)$ is the tree obtained from a $k$-edge path $v_0v_1\cdots v_k$ by attaching $a_i$ leaves at $v_i$ for each $i$. It has $k+1+\sum_ia_i$ vertices; $C(0)=K_1$. By (C.1), $\hom(C(a_0,\dots,a_k),G)=e^{\mathsf T}D^{a_0}AD^{a_1}\cdots AD^{a_k}e$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Appendix C, p.20 (PDF 21)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The ordinary caterpillar `C(a_0, …, a_k)` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix C, p.20 (PDF 21)): the tree obtained by
attaching `a_i` leaves at vertex `i` of a `k`-edge path `v_0 v_1 ⋯ v_k` (`k ≥ 0`, `a_i ≥ 0`).
`C(0) = K_1`.

**Formalization Note** Vertices are the spine `Fin (k + 1)` and, for each spine vertex `i`, `a_i` leaves
`⟨i, ·⟩ : Σ i, Fin (a i)`. Spine vertices `i`, `i + 1` are adjacent, and each leaf `⟨i, _⟩` is adjacent to
spine vertex `i`; `SimpleGraph.fromRel` symmetrizes. -/
def caterpillarGraph (k : ℕ) (a : Fin (k + 1) → ℕ) :
    SimpleGraph (Fin (k + 1) ⊕ (Σ i : Fin (k + 1), Fin (a i))) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl i, Sum.inl j => i.val + 1 = j.val
    | Sum.inr p, Sum.inl j => p.1 = j
    | _, _ => False

end IntADSat.Supplement


