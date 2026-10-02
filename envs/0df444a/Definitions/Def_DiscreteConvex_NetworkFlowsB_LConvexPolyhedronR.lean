-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_LConvexPolyhedronR
-- name    : DiscreteConvex_NetworkFlowsB_LConvexPolyhedronR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:11.501033+00:00
-- url     : https://prove2.me/theorems/11be2a73-c6d5-4cca-8ada-c7a74fdc8b96
-- title:
--   Real L-convex polyhedron
-- statement:
--   The class $L^0[\mathbb{R}]$ of **real** L-convex polyhedra: a nonempty polyhedron closed under $\vee$, $\wedge$ and translation by any multiple of the all-ones vector — the indicator form of (SBF[R]) and (TRF[R]).
--
--   It is strictly larger than the integral class $L^0[\mathbb{Z}|\mathbb{R}]$ of convex hulls of integer L-convex sets: one arc of cost $1/2$ gives optimal potentials $\{p : p(v)-p(u)\le 1/2\}$, the convex hull of no integer set.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.2, Theorem 9.6 (2).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §9.2, Theorem 9.6

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_IsPolyhedron

namespace DiscreteConvex.NetworkFlowsB

open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The class `L⁰[R]` of **real** L-convex polyhedra: a nonempty polyhedron closed under `⊔`, `⊓`
and translation by any multiple of the all-ones vector — the indicator form of (SBF[R]) and
(TRF[R]). `LConvexPolyhedron` is the convex hull of an integer L-convex set, i.e. the *integral*
class `L⁰[Z|R]`. Theorem 9.6 (2) and Theorem 9.15 (1) hold in the real class: one arc of cost
`1/2` gives optimal potentials `{p : p(v) - p(u) ≤ 1/2}`, the convex hull of no integer set. -/
def LConvexPolyhedronR (P : Set (V → ℝ)) : Prop :=
  IsPolyhedron P ∧ P.Nonempty ∧
    (∀ p ∈ P, ∀ q ∈ P, p ⊔ q ∈ P ∧ p ⊓ q ∈ P) ∧
    (∀ p ∈ P, ∀ α : ℝ, (fun v => p v + α) ∈ P)

end DiscreteConvex.NetworkFlowsB


