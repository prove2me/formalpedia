-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:30.274636+00:00
-- url     : https://prove2.me/theorems/ae5d5888-151c-4ff6-87fd-a7a6738fcf5f
-- title:
--   Inter Div Supp
-- statement:
--   Definitions and structural lemmas for Inter Div Supp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSupp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
section Dim
variable {σ : Type*} [Finite σ]
end Dim
section Blocks
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def blockWeight [DecidableEq K] (k : K) : (Σ k, ι k) → ℕ := fun p => if p.1 = k then 1 else 0
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end Blocks
end ReciprocityTheory.ChartRestriction.G.Geo


