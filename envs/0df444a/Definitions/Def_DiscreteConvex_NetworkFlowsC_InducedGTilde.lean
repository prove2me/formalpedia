-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTilde
-- name    : DiscreteConvex_NetworkFlowsC_InducedGTilde
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:53:50.790165+00:00
-- url     : https://prove2.me/theorems/75d64421-470d-4514-a84a-187e6036d8dc
-- title:
--   InducedGTilde
-- statement:
--   The potential-type induced function $\tilde g:\mathbb Z^T\to\mathbb Z\cup\{\pm\infty\}$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.82).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.82)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOn

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- The potential-type induced function `g̃ : Zᵀ → Z∪{±∞}` of Eq. (9.82). -/
noncomputable def InducedGTilde (tail head : A → V) (S T : Finset V) (ga : A → ℤ → WithTop ℝ)
    (g : (V → ℤ) → WithTop ℝ) (q : V → ℤ) : EReal :=
  sInf {L : EReal | ∃ eta : A → ℤ, ∃ P : V → ℤ, ∃ p : V → ℤ, SupportedOn S p ∧
    (∀ v ∈ S, P v = p v) ∧ (∀ v ∈ T, P v = q v) ∧
    (∀ a : A, eta a = -(P (tail a) - P (head a))) ∧
    L = ToEReal (g p + ∑ a : A, ga a (eta a))}

end DiscreteConvex.NetworkFlowsC


