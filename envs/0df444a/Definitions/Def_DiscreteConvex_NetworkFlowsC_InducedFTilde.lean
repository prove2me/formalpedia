-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTilde
-- name    : DiscreteConvex_NetworkFlowsC_InducedFTilde
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:38.001213+00:00
-- url     : https://prove2.me/theorems/978ff335-54aa-49e5-b26c-ce1c0f29d308
-- title:
--   InducedFTilde
-- statement:
--   The flow-type induced function $\tilde f:\mathbb Z^T\to\mathbb Z\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.81).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.81)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_BoundaryZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOn

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The flow-type induced function `f̃ : Zᵀ → Z∪{±∞}` of Eq. (9.81). -/
noncomputable def InducedFTilde (tail head : A → V) (S T : Finset V) (fa : A → ℤ → WithTop ℝ)
    (f : (V → ℤ) → WithTop ℝ) (y : V → ℤ) : EReal :=
  sInf {L : EReal | ∃ xi : A → ℤ, ∃ x : V → ℤ, SupportedOn S x ∧
    (∀ v ∈ S, BoundaryZ tail head xi v = x v) ∧
    (∀ v ∈ T, BoundaryZ tail head xi v = -(y v)) ∧
    (∀ v, v ∉ S → v ∉ T → BoundaryZ tail head xi v = 0) ∧
    L = ToEReal (f x + ∑ a : A, fa a (xi a))}

end DiscreteConvex.NetworkFlowsC


