-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_DeltaMinus
-- name    : DiscreteConvex_NetworkFlows_DeltaMinus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:13:45.014216+00:00
-- url     : https://prove2.me/theorems/1fe5bf3f-de2a-4b87-9c8a-04c66f499eb4
-- title:
--   Arcs entering a vertex subset (Eq. 9.15)
-- statement:
--   $\Delta^-X = \{a \in A : \partial^-a \in X,\ \partial^+a \in V\setminus X\}$, the set of arcs entering $X$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.15).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.15)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.247, Eq. (9.15): arcs entering a vertex
subset, in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- `Δ⁻X = {a ∈ A : ∂⁻a ∈ X, ∂⁺a ∈ V∖X}` (Eq. (9.15)), the set of arcs entering `X`, where
`tail = ∂⁺` and `head = ∂⁻`. -/
def DeltaMinus {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (X : Finset V) : Finset A :=
  Finset.univ.filter (fun a => head a ∈ X ∧ tail a ∉ X)

end DiscreteConvex.NetworkFlows


