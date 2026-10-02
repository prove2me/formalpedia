-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeR
-- name    : DiscreteConvex_NetworkFlowsC_InducedGTildeR
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:54:06.315173+00:00
-- url     : https://prove2.me/theorems/ab3856f9-1ee3-4e06-8611-be80ab1e6dba
-- title:
--   InducedGTildeR
-- statement:
--   The potential-type induced function, real domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, real version of Eq. (9.82).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, real version of Eq. (9.82)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ToEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SupportedOnR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedGTildeR (tail head : A → V) (S T : Finset V) (ga : A → ℝ → WithTop ℝ)
    (g : (V → ℝ) → WithTop ℝ) (q : V → ℝ) : EReal :=
  sInf {L : EReal | ∃ eta : A → ℝ, ∃ P : V → ℝ, ∃ p : V → ℝ, SupportedOnR S p ∧
    (∀ v ∈ S, P v = p v) ∧ (∀ v ∈ T, P v = q v) ∧
    (∀ a : A, eta a = -(P (tail a) - P (head a))) ∧
    L = ToEReal (g p + ∑ a : A, ga a (eta a))}

end DiscreteConvex.NetworkFlowsC


