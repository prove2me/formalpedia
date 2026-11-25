-- Prove2me | Definitions.Def_StableMSR_SeparatorLevel
-- name    : StableMSR_SeparatorLevel
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-25T05:46:57.277096+00:00
-- url     : https://prove2.me/theorems/a8b77d67-9266-57df-a4c1-fa5d1c059d4d
-- title:
--   Output and table invariants between separator levels
-- statement:
--   The state between consecutive component sizes retains the utility registers and permanent regional tables, advances its scratch cursor monotonically, and keeps an open output tape with an exact length counter. The level tape lists the mathematical outputs for that one component size in cut and component order.
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_RegionalMenuImage

namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorLevels
open StableMSR.Recovery StableMSR.Recovery.SingleCircuit
set_option autoImplicit false

/-- State shared between consecutive component-size levels of the separator writer. -/
structure Between (original current : State) : Prop where
  control : ∀ j,j=6 ∨ j=7 ∨ (64≤j ∧ j≤81) → current.reg j=original.reg j
  cursor : original.reg 8 ≤ current.reg 8
  tables : ∀ i < (original.reg 8).toNat,current.heap i=original.heap i
  count : current.reg 82=(current.output.length:ℤ)
  available : current.closed=false

/-- The instructions for components of size k+1, starting with the first separator. -/
def levelTape (d : Instance) (w k : ℕ) :=
  let vs := TightLanguage.vertices d
  (TightLanguage.cuts vs (min w d.n)).flatMap fun cut =>
    (TightLanguage.keysFor d vs cut).flatMap (visitTape Naming.name d k cut)

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.SeparatorLevels


