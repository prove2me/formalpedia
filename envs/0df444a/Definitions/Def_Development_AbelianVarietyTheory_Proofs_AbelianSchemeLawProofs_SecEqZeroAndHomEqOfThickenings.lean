-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:03.179549+00:00
-- url     : https://prove2.me/theorems/60177635-e1e1-4e70-9181-264fbeb66953
-- title:
--   Sec Eq Zero And Hom Eq Of Thickenings
-- statement:
--   Definitions and structural lemmas for Sec Eq Zero And Hom Eq Of Thickenings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SecEqZeroAndHomEqOfThickenings.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace ThickeningDetermines
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData TopologicalSpace
variable {X Y : Scheme.{0}} {N : LB X}
theorem exists_mem_chart (hN : N.IsLB) (x : X) : ∃ i, x ∈ N.U i :=
  Opens.mem_iSup.1 (hN.cover.ge (Set.mem_univ x))
theorem associated_germ_sec (s : N.Sec) (i j : N.ι) (x : X) (hi : x ∈ N.U i) (hj : x ∈ N.U j) :
    Associated ((X.presheaf.germ _ x hi).hom (s.f i)) ((X.presheaf.germ _ x hj).hom (s.f j)) := by
  have hm : x ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  have h0 : Associated (resG X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (s.f i))
      (resG X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (s.f j)) :=
    (congrArg (Associated · _) (s.compat i j)).mpr
      (associated_unit_mul_left _ _ (N.g i j).isUnit)
  have := h0.map (X.presheaf.germ _ x hm).hom
  rwa [germ_resG, germ_resG] at this
noncomputable def secIdeal (hN : N.IsLB) (s : N.Sec) : X.IdealSheafData :=
  locIdeal N.U s.f (exists_mem_chart hN) (associated_germ_sec s)
end ThickeningDetermines
end GlobalTheory


