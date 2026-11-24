-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:06.964272+00:00
-- url     : https://prove2.me/theorems/1c407dcd-8858-4d5d-aa5c-97e0540ab265
-- title:
--   Two Le Krull Dim Of Relevant Prime
-- statement:
--   Definitions and structural lemmas for Two Le Krull Dim Of Relevant Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/TwoLeKrullDimOfRelevantPrime.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
section Dim
variable {R : Type*} [CommRing R]
end Dim
section Kill
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
def i2kill (k : K) : MRing ι →ₐ[ℤ] MRing ι := aeval fun v => if v.1 = k then 0 else X v
end Kill
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


