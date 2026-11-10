-- Prove2me | Definitions.Def_RandTreeUniv_IsBarePathFamily
-- name    : RandTreeUniv_IsBarePathFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:17.142888+00:00
-- url     : https://prove2.me/theorems/88bd294b-1025-4bd4-bab0-321517e1d6c4
-- title:
--   Vertex-disjoint bare paths of a given length
-- statement:
--   A path in a graph $T$ is **bare** if every internal vertex has degree $2$ in $T$; the internal vertices of a $uw$-path are its vertices other than $u$ and $w$. A family $P_1,\dots,P_r$ is a family of **$r$ vertex-disjoint bare paths of length $L$** when each $P_i$ is a path of $T$ with exactly $L$ edges, each is bare, and no two share a vertex.
--
--   Long bare paths are the structure that separates the family $\mathcal T_1$ (embedded with linking systems, §5) from $\mathcal T_2\cup\mathcal T_3$ (embedded with rollback and absorption, §6).
--
--   **Formalization Note** The module defines `IsBare` and `IsBarePathFamily`; path $i$ runs from $u_i$ to $w_i$ and degrees are taken in the whole graph $T$.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §4, p.21 (PDF 22) and §5, p.25 (PDF 26)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- A path `P` of `T` is bare (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §4, p.21 (PDF 22)): "A path in a graph `G` is called bare if
every internal vertex has degree 2 in `G`."

**Formalization Note** The internal vertices of a `uw`-path are its vertices other than `u` and
`w`; the degree is taken in the whole graph `T`. -/
def IsBare {V : Type*} [Fintype V] (T : SimpleGraph V) {u w : V} (P : T.Walk u w) : Prop :=
  ∀ v ∈ P.support, v ≠ u → v ≠ w → T.degree v = 2

/-- `P_1, …, P_r` are `r` pairwise vertex-disjoint bare paths of `T`, each of length exactly `L`
(Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §4, p.21 (PDF 22) and §5, p.25 (PDF 26)). Path `i` runs from `u i` to `w i`. -/
def IsBarePathFamily {V : Type*} [Fintype V] (T : SimpleGraph V) {r : ℕ} (u w : Fin r → V)
    (P : ∀ i, T.Walk (u i) (w i)) (L : ℕ) : Prop :=
  (∀ i, (P i).IsPath ∧ (P i).length = L ∧ IsBare T (P i)) ∧
    ∀ i j, i ≠ j → ∀ v ∈ (P i).support, v ∉ (P j).support

end RandTreeUniv


