-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_KappaStatementHolds
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_KappaStatementHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:15.619836+00:00
-- url     : https://prove2.me/theorems/eb31caad-4fa5-4ff6-ae5b-a2b76f1211d1
-- title:
--   Kappa Statement Holds
-- statement:
--   Definitions and structural lemmas for Kappa Statement Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/KappaStatementHolds.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_HasFDerivAtNmat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def ninvF (w : V (nd X)) : Frame X.Ψ r := fun τ a c => Ring.inverse (mat (nmat X w) τ) a c
def vecL : V (nd X) ≃ₗ[ℂ] (Ent X → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin (Ent X)))
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf


