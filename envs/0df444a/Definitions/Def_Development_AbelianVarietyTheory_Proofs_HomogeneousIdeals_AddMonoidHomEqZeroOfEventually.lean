-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:45.818972+00:00
-- url     : https://prove2.me/theorems/a4612318-e100-49cc-b898-777a0e09e99e
-- title:
--   Add Monoid Hom Eq Zero Of Eventually
-- statement:
--   Definitions and structural lemmas for Add Monoid Hom Eq Zero Of Eventually, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/AddMonoidHomEqZeroOfEventually.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology
noncomputable section
namespace GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}
def latticeIsogeny (α : ℂ) (hα : ∀ l ∈ L.lattice, α * l ∈ L'.lattice) :
    (latticeCurve L).toAffine.Point →+ (latticeCurve L').toAffine.Point :=
  (QuotientAddGroup.lift L.lattice.toAddSubgroup
    ((latticePointHom L').comp (AddMonoidHom.mulLeft α))
    fun l hl ↦ latticePoint_of_mem L' (hα l hl)).comp (latticePointEquiv L).symm.toAddMonoidHom
end GlobalTheory


