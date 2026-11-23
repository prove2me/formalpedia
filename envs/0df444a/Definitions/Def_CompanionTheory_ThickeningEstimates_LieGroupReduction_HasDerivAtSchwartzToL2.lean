-- Prove2me | Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
-- name    : CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:26.92923+00:00
-- url     : https://prove2.me/theorems/5fd75523-8546-4e4a-9023-5924b7d7a0d5
-- title:
--   Has Deriv At Schwartz To L2
-- statement:
--   Definitions and structural lemmas for Has Deriv At Schwartz To L2, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/HasDerivAtSchwartzToL2.lean

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real
namespace CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
def LD (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l → Sch l) (t₀ : ℝ) : Prop :=
  ∀ f, HasDerivAt (fun t => schwartzToL2 l (U t f)) (schwartzToL2 l (Q f)) t₀
variable [DecidableEq l]
end CompanionTheory.ThKR.LL


