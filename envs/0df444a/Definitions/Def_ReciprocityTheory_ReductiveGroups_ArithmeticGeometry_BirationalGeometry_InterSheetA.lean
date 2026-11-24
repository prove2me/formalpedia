-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:10.983794+00:00
-- url     : https://prove2.me/theorems/f5f7bcf2-d597-4078-97a3-193c18f1c310
-- title:
--   Inter Sheet A
-- statement:
--   Definitions and structural lemmas for Inter Sheet A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
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
open MvPolynomial Filter Topology
section Alg
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def bsmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => c p.1 * z p
end Alg
section Hess
variable {e : ℕ}
end Hess
end ReciprocityTheory.ChartRestriction.G.Geo


