-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLowerBounds_NewtonIdentitiesLowDegree
-- name    : Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLowerBounds_NewtonIdentitiesLowDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:34.903611+00:00
-- url     : https://prove2.me/theorems/6ee248a8-0587-4e5b-b2b7-44e28ffa1512
-- title:
--   Newton Identities Low Degree
-- statement:
--   Definitions and structural lemmas for Newton Identities Low Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NewtonLowerBounds/NewtonIdentitiesLowDegree.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace PositivityTheory.RgJS.NewtonIdentitiesAlt
variable {A : Type} [Fintype A]
def ev (a : A → ℂ) (j : ℕ) : ℂ := ∑ t ∈ powersetCard j (univ : Finset A), ∏ i ∈ t, a i
end PositivityTheory.RgJS.NewtonIdentitiesAlt
namespace PositivityTheory.RgJS
end PositivityTheory.RgJS


