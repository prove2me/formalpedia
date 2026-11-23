-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SupSec
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SupSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:02.477995+00:00
-- url     : https://prove2.me/theorems/c3d7f53d-3bd4-47c5-a8f9-7d024e6cd352
-- title:
--   Sup Sec
-- statement:
--   Definitions and structural lemmas for Sup Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SupSec.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_SupGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExtProof
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfRsmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec
open NumberField ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def toGT (X : PT E) : GT (Idx X.dim) where
  b := X.b
  integral := X.integral
  perfect := X.perfect
  ka := fun x => (X.eps x : ℂ)
  ka_abs := by
    intro x hx
    rcases X.eps_pm x hx with h | h <;> simp [h]
end ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupSec


