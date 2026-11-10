-- Prove2me | Definitions.Def_RandTreeUniv_InT1Star
-- name    : RandTreeUniv_InT1Star
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:07.23625+00:00
-- url     : https://prove2.me/theorems/3e2ebafc-fc5f-4e3a-810c-9a8a8557054b
-- title:
--   The family $\mathcal T_1^*$ (graphs with $\alpha$ long bare paths and a bounded-degree forest remainder)
-- statement:
--   Let $K$ be the large constant of §4, $\psi\ge1$ and $\alpha=n\psi\ln\ln n/(K^3\ln n)$. The family $\mathcal T_1^*$ consists of all graphs $T$ on $n$ vertices having $\alpha$ vertex-disjoint bare paths $P_1,\dots,P_\alpha$ of length $n/(K^2\alpha)$ such that
--
--   $$
--   T\setminus E(P_1\cup\dots\cup P_\alpha)
--   $$
--
--   (delete the path edges, keep all $n$ vertices) is a forest with maximum degree at most $\Delta$.
--
--   Graphs in $\mathcal T_1^*$ may contain cycles; trees of $\mathcal T_{n,\Delta}$ with many long bare paths and cycle factors of large girth both belong to it. Theorem 5.1 shows that $G(n,C(\ln n)^\psi/n)$ is whp $\mathcal T_1^*$-universal.
--
--   **Formalization Note** The real quantities are rounded up: $\lceil\alpha\rceil$ paths, each of length $\lceil n/(K^2\alpha)\rceil$. With this reading the paper's remark that $\mathcal T_1\subseteq\mathcal T_1^*$ holds.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §5, p.25 (PDF 26)

import Mathlib
import Definitions.Def_RandTreeUniv_IsBarePathFamily
import Definitions.Def_RandTreeUniv_alpha

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `T ∈ T∗₁` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §5, p.25 (PDF 26)): "the family of all graphs `T` on `n` vertices with `α`
vertex-disjoint bare paths `P_1, …, P_α` of length `n/(K²α)` such that `T \ E(P_1 ∪ … ∪ P_α)` is a
forest with maximum degree at most `∆`", with `α = n ψ ln ln n/(K³ ln n)`. Graphs in `T∗₁` may
contain cycles.

**Formalization Note** `T` is any simple graph on `Fin n` (not necessarily a tree). The real
quantities are rounded up: `⌈α⌉` paths of length `⌈n/(K²α)⌉` (the paper ignores rounding, §2.1;
with this reading the paper's remark "`T₁` is a subfamily of `T∗₁`" holds). Removing the path
edges keeps all `n` vertices (`deleteEdges`); the forest is acyclic and its degrees are at most
`∆`. -/
def InT1Star (n : ℕ) (K ψ : ℝ) (Δ : ℕ) (T : SimpleGraph (Fin n)) : Prop :=
  ∃ (u w : Fin ⌈alpha K ψ n⌉₊ → Fin n) (P : ∀ i, T.Walk (u i) (w i)),
    IsBarePathFamily T u w P ⌈(n : ℝ) / (K ^ 2 * alpha K ψ n)⌉₊ ∧
    (T.deleteEdges (⋃ i, {e | e ∈ (P i).edges})).IsAcyclic ∧
    ∀ v, (T.deleteEdges (⋃ i, {e | e ∈ (P i).edges})).degree v ≤ Δ

end RandTreeUniv


