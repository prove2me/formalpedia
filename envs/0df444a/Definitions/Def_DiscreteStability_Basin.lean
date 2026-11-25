-- Prove2me | Definitions.Def_DiscreteStability_Basin
-- name    : DiscreteStability_Basin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:43:41.653915+00:00
-- url     : https://prove2.me/theorems/f661750a-074d-4221-bfa7-89db066c9e7a
-- title:
--   Basin
-- statement:
--   Definitions and structural lemmas for Basin, from B. J. Ridenhour (magbenji/discrete-modified-gradient-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Stability of equilibria in discrete-time modified-gradient systems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Basin.lean

import Definitions.Def_DiscreteStability_Stability
set_option autoImplicit true
open scoped RealInnerProductSpace Topology
open Set Metric Filter
namespace DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {f : E → ℝ} {g : E → E} {xbar : E} {L Λ c η : ℝ}
  {P : ℕ → E →L[ℝ] E} {lo hi : ℕ → ℝ}
end DiscreteStability


