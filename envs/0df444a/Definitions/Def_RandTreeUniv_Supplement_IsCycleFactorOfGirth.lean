-- Prove2me | Definitions.Def_RandTreeUniv_Supplement_IsCycleFactorOfGirth
-- name    : RandTreeUniv_Supplement_IsCycleFactorOfGirth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:37:46.22457+00:00
-- url     : https://prove2.me/theorems/3f9dff61-4967-4a05-85c9-dc58c0a518ae
-- title:
--   Cycle factors on $[n]$ of girth at least $\ell$ (the family $\mathcal C_{n,\ell}$)
-- statement:
--   A **cycle factor** in a graph $G$ is a spanning subgraph of $G$ that is isomorphic to a union of vertex-disjoint cycles. A cycle factor *on* $[n]=\{1,\dots,n\}$ is a cycle factor of the complete graph on $[n]$: a graph $T$ with vertex set $[n]$ whose components are cycles covering every vertex, equivalently a graph in which every vertex has degree exactly $2$.
--
--   For an integer $\ell$, the family $\mathcal C_{n,\ell}$ consists of all cycle factors $T$ on $[n]$ of **girth at least $\ell$**, i.e. with every cycle of length at least $\ell$:
--
--   $$
--   \mathcal C_{n,\ell}=\{\,T \text{ on } [n]:\ \deg_T(v)=2\ \text{for all } v\in[n],\ \ \operatorname{girth}(T)\ge\ell\,\}.
--   $$
--
--   This is the family whose universality Theorem 4 asserts for $G(n,C(\ln n)^\psi/n)$. It contains every $C_{\ell'}$-factor with $\ell'\ge\ell$ (when $\ell'\mid n$), and also every mixture of cycle lengths that are all at least $\ell$.
--
--   **Formalization Note** The vertex set is any finite type (the theorems use `Fin n`). Spanning 2-regularity is the published `SnarkGen.EdgeInsertion.IsTwoFactor ⊤ T` (a 2-factor of the complete graph); a finite 2-regular simple graph is exactly a vertex-disjoint union of cycles covering all vertices. Girth at least $\ell$ is $(\ell:\mathbb N_\infty)\le$ `T.egirth`.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §1.2, p.2 (PDF 3) (cycle factor) and p.5 (PDF 6) (the family C_{n,ℓ})

import Mathlib
import Definitions.Def_SnarkGen_EdgeInsertion_EvenTwoFactor

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv.Supplement

/-- `T` belongs to the family `C_{n,ℓ}` of cycle factors of girth at least `ℓ` (Cohen Antonir,
Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*,
arXiv:2608.06358 (held revision, sha256 33e85b21…), §1.2, p.2 (PDF 3) and p.5 (PDF 6)): "A cycle
factor in a graph `G` is a spanning subgraph of `G` that is isomorphic to a union of vertex-disjoint
cycles", and `C_{n,ℓ}` is "the family of all cycle factors on `[n]` of girth at least `ℓ`".

**Formalization Note** A cycle factor on the vertex set `V` (the paper's `[n]`, i.e. `Fin n`) is a
2-factor of the complete graph on `V`: a graph on all of `V` in which every vertex has degree
exactly `2` (the published `SnarkGen.EdgeInsertion.IsTwoFactor ⊤ T`); a finite 2-regular simple
graph is exactly a vertex-disjoint union of cycles covering every vertex. Girth at least `ℓ` is
`(ℓ : ℕ∞) ≤ T.egirth`: every cycle of `T` has length at least `ℓ`. -/
def IsCycleFactorOfGirth {V : Type*} [Fintype V] (ℓ : ℕ) (T : SimpleGraph V) : Prop :=
  SnarkGen.EdgeInsertion.IsTwoFactor (⊤ : SimpleGraph V) T ∧ (ℓ : ℕ∞) ≤ T.egirth

end RandTreeUniv.Supplement


