-- Prove2me | Definitions.Def_RandTreeUniv_IsLinkingSystemIn
-- name    : RandTreeUniv_IsLinkingSystemIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:11.095415+00:00
-- url     : https://prove2.me/theorems/5f3fa1f9-c604-48bc-82b7-97aa8273863e
-- title:
--   $G[S]$ contains an $(\mathbf a,\mathbf b;k)$-linking system (Definition 1.1)
-- statement:
--   Let $\mathbf a=(a_1,\dots,a_m)$ and $\mathbf b=(b_1,\dots,b_m)$ be two $m$-tuples of vertices of a graph $G$, and $k\ge1$. An **$(\mathbf a,\mathbf b;k)$-linking system** is a union of forests $F_\sigma$, one for each permutation $\sigma\in S_m$, where $F_\sigma$ consists of vertex-disjoint paths of length $k$ connecting $a_i$ with $b_{\sigma(i)}$ for every $i$. The number $k$ is the depth. $G[S]$ **contains** an $(\mathbf a,\mathbf b;k)$-linking system when, for every $\sigma\in S_m$, $G[S]$ contains an $(\mathbf a,\sigma(\mathbf b);k)$-path system, where $\sigma(\mathbf b)=(b_{\sigma(1)},\dots,b_{\sigma(m)})$.
--
--   In words: for every way of matching the vertices of $\mathbf a$ to those of $\mathbf b$, there is a family of disjoint $k$-paths realising that matching. On a vertex set of exactly $(k+1)m$ vertices each $F_\sigma$ covers every vertex, so the linking system is spanning; the paper calls a graph containing a spanning linking system "a linking system".
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §1.3, Definition 1.1, pp.3–4 (PDF 4–5)

import Mathlib
import Definitions.Def_RandTreeUniv_IsPathSystemIn

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `G[S]` contains an `(a, b; k)`-linking system (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), Definition 1.1, pp.3–4 (PDF 4–5)): for
every permutation `σ ∈ S_m` there is a forest `F_σ` of vertex-disjoint paths of length `k`
connecting `a_i` with `b_{σ(i)}` for every `i`, i.e. an `(a, b ∘ σ; k)`-path system.

**Formalization Note** The paper's phrase "`G` is an `(a, b; k)`-linking system" is used, "with
some abuse of terminology", for "`G` contains a spanning linking system" (p.4); this predicate is
the containment. When the vertex set has exactly `(k + 1)m` vertices (as in every use in this
mission) each forest `F_σ` covers all vertices, so the contained linking system is spanning. -/
def IsLinkingSystemIn {V : Type*} (G : SimpleGraph V) (S : Set V) {m : ℕ} (a b : Fin m → V)
    (k : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin m), IsPathSystemIn G S a (b ∘ σ) k

end RandTreeUniv


