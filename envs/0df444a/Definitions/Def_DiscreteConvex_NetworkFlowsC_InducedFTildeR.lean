-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeR
-- name    : DiscreteConvex_NetworkFlowsC_InducedFTildeR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:38.329726+00:00
-- url     : https://prove2.me/theorems/c8952132-da76-4831-956b-6c07b6ce06fe
-- title:
--   InducedFTildeR
-- statement:
--   The flow-type induced function, real domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, real version of Eq. (9.81).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, real version of Eq. (9.81)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_Boundary
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOnR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedFTildeR (tail head : A → V) (S T : Finset V) (fa : A → ℝ → WithTop ℝ)
    (f : (V → ℝ) → WithTop ℝ) (y : V → ℝ) : EReal :=
  sInf {L : EReal | ∃ xi : A → ℝ, ∃ x : V → ℝ, SupportedOnR S x ∧
    (∀ v ∈ S, Boundary tail head xi v = x v) ∧
    (∀ v ∈ T, Boundary tail head xi v = -(y v)) ∧
    (∀ v, v ∉ S → v ∉ T → Boundary tail head xi v = 0) ∧
    L = ToEReal (f x + ∑ a : A, fa a (xi a))}

end DiscreteConvex.NetworkFlowsC


