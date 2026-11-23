-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:44:25.97906+00:00
-- url     : https://prove2.me/theorems/ef4cbd64-944b-4db9-b43c-d949f1adad12
-- title:
--   Transport
-- statement:
--   Definitions and structural lemmas for Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace ReciprocityTheory.ChartRestriction.G.Semi.Transport
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
variable {X : Scheme.{0}}
section Transport
variable {A B : LB X}
abbrev pq (p : B.ι) (q : A.ι) : (LB.div B A).ι := (p, q)
lemma le_divU (p : B.ι) (q : A.ι) : A.U q ⊓ B.U p ≤ (LB.div B A).U (pq p q) :=
  le_inf inf_le_right inf_le_left
def cand (w : LB.Iso A B) (b : LB.Gen B) (q : A.ι) (p : B.ι) : Γ(X, A.U q ⊓ B.U p)ˣ :=
  (res (le_divU p q) (w.s (pq p q)))⁻¹ * res inf_le_right (b.s p)
end Transport
section InvComp
variable {A B C : LB X}
lemma swapLe (qp : (LB.div A B).ι) : (LB.div A B).U qp ≤ (LB.div B A).U (pq qp.2 qp.1) :=
  le_inf inf_le_right inf_le_left
def invIso (w : LB.Iso A B) : LB.Iso B A := ⟨fun qp => (res (swapLe qp) (w.s (pq qp.2 qp.1)))⁻¹⟩
end InvComp
end ReciprocityTheory.ChartRestriction.G.Semi.Transport


