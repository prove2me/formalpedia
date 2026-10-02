-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_Boundary
-- name    : DiscreteConvex_NetworkFlows_Boundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:13:33.389026+00:00
-- url     : https://prove2.me/theorems/eed10eab-bbf6-4231-b0d0-3af890f2fbbe
-- title:
--   Boundary of a flow (Eq. 9.1)
-- statement:
--   The **boundary** $\partial\xi(v) = \sum\{\xi(a) : a \in \delta^+v\} - \sum\{\xi(a) : a \in \delta^-v\}$ of a flow $\xi : A \to \mathbb R$ on a digraph with vertex set $V$, arc set $A$, and tail/head maps $\mathrm{tail} = \partial^+$, $\mathrm{head} = \partial^-$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.245, Eq. (9.1)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.245, Eq. (9.1): the boundary of a flow, in
`DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- The **boundary** `∂ξ(v) = Σ{ξ(a) : a ∈ δ⁺v} - Σ{ξ(a) : a ∈ δ⁻v}` (Eq. (9.1)) of a flow
`ξ : A → ℝ` on a digraph with vertex set `V`, arc set `A`, and tail/head maps `tail = ∂⁺`,
`head = ∂⁻ : A → V`. -/
noncomputable def Boundary {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (ξ : A → ℝ) (v : V) : ℝ :=
  (∑ a ∈ Finset.univ.filter (fun a => tail a = v), ξ a) -
    (∑ a ∈ Finset.univ.filter (fun a => head a = v), ξ a)

end DiscreteConvex.NetworkFlows


