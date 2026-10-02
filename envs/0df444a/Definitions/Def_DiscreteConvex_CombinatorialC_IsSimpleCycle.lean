-- Prove2me | Definitions.Def_DiscreteConvex_CombinatorialC_IsSimpleCycle
-- name    : DiscreteConvex_CombinatorialC_IsSimpleCycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:40:02.810834+00:00
-- url     : https://prove2.me/theorems/5a3b39d2-aac2-44e5-8670-65b366290d05
-- title:
--   Simple cycle in a directed graph
-- statement:
--   An injective cyclic vertex sequence $v:\mathrm{Fin}(k{+}1)\to V$ and arcs with $\{\partial^+(\mathrm{arcs}_i),\partial^-(\mathrm{arcs}_i)\}=\{v_i,v_{i+1}\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, footnote 33.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.83, footnote 33

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, footnote 33: a simple cycle, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- A **simple cycle** (footnote 33): an alternating sequence of `k+1` vertices
`v : Fin (k+1) → V` (cyclically indexed, `v` injective — the `v_i` are pairwise distinct) and
arcs `arcs : Fin (k+1) → A` such that `{∂⁺(arcs i), ∂⁻(arcs i)} = {v i, v (i+1)}` for every `i`
(`i + 1` wraps cyclically since it is computed in `Fin (k+1)`). Cycle length is `k+1 > 0`. -/
def IsSimpleCycle {V A : Type*} [DecidableEq V] (src dst : A → V) (k : ℕ) (v : Fin (k + 1) → V)
    (arcs : Fin (k + 1) → A) : Prop :=
  Function.Injective v ∧
    ∀ i : Fin (k + 1), ({src (arcs i), dst (arcs i)} : Finset V) = {v i, v (i + 1)}

end DiscreteConvex.CombinatorialC


