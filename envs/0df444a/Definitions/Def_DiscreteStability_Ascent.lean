-- Prove2me | Definitions.Def_DiscreteStability_Ascent
-- name    : DiscreteStability_Ascent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T08:32:32.520853+00:00
-- url     : https://prove2.me/theorems/f4c379b3-0d75-4ebe-8f05-5cff83d9c464
-- title:
--   Ascent
-- statement:
--   Definitions and structural lemmas for Ascent, from B. J. Ridenhour (magbenji/discrete-modified-gradient-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Stability of equilibria in discrete-time modified-gradient systems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/magbenji/discrete-modified-gradient-lean/blob/c3e4688e6f32de6904ce696890a372ae4cba6ad3/DiscreteStability/Ascent.lean

import Definitions.Def_DiscreteStability_Basic
set_option autoImplicit true
open scoped RealInnerProductSpace
open Set
namespace DiscreteStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Consequences
variable {f : E → ℝ} {g : E → E} {S : Set E} {L lo hi : ℝ} {P : E →L[ℝ] E}
end Consequences
end DiscreteStability


