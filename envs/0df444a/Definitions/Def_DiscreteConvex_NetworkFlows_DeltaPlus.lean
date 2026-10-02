-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlows_DeltaPlus
-- name    : DiscreteConvex_NetworkFlows_DeltaPlus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:13:39.731634+00:00
-- url     : https://prove2.me/theorems/00679561-2b9e-4a5b-bf6e-8a68c4eaae0f
-- title:
--   Arcs leaving a vertex subset (Eq. 9.14)
-- statement:
--   $\Delta^+X = \{a \in A : \partial^+a \in X,\ \partial^-a \in V\setminus X\}$, the set of arcs leaving $X$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.14).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.247, Eq. (9.14)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.247, Eq. (9.14): arcs leaving a vertex subset,
in `DiscreteConvex.NetworkFlows`.
-/

namespace DiscreteConvex.NetworkFlows

/-- `Δ⁺X = {a ∈ A : ∂⁺a ∈ X, ∂⁻a ∈ V∖X}` (Eq. (9.14)), the set of arcs leaving `X`, where
`tail = ∂⁺` and `head = ∂⁻`. -/
def DeltaPlus {V A : Type*} [Fintype A] [DecidableEq V]
    (tail head : A → V) (X : Finset V) : Finset A :=
  Finset.univ.filter (fun a => tail a ∈ X ∧ head a ∉ X)

end DiscreteConvex.NetworkFlows


