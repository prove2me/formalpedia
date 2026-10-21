-- Prove2me | Definitions.Def_HeteroBass_HetP_finiteJumpGenerator
-- name    : HeteroBass_HetP_finiteJumpGenerator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:49.492846+00:00
-- url     : https://prove2.me/theorems/21b9d865-13ab-4813-81d2-8d50e307aae5
-- title:
--   Finite-state pure-jump generator
-- statement:
--   A finite-state continuous-time jump process with off-diagonal rates $r(S,T)$ has generator $G$ given by
--
--   $$G(S,T)=r(S,T)\quad(S\ne T),\qquad G(S,S)=-\sum_{U\ne S}r(S,U).$$
--
--   This general generator is the reusable finite-chain interface used by the consumer adoption model. Nonnegative rates are imposed by the theorems that use it.
-- source:
--   Fibich & Golan, Diffusion of new products with heterogeneous consumers, arXiv:2102.05926v3, §2, eq. (5), p. 5 (general finite-state generator of the model)

import Mathlib

namespace HeteroBass.HetP

/-- Generator of a finite pure-jump chain with off-diagonal jump rates `r`. -/
noncomputable def finiteJumpGenerator {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → ℝ) : Matrix α α ℝ :=
  fun S T => if S = T then -∑ U : α, if U = S then 0 else r S U else r S T

end HeteroBass.HetP


