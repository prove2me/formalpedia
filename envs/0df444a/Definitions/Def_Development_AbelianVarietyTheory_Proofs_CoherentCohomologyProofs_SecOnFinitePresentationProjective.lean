-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnFinitePresentationProjective
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnFinitePresentationProjective
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:15:56.849807+00:00
-- url     : https://prove2.me/theorems/ee2a05bc-ba19-4893-a889-2a68a51d202b
-- title:
--   Sec On Finite Presentation Projective
-- statement:
--   Definitions and structural lemmas for Sec On Finite Presentation Projective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SecOnFinitePresentationProjective.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
namespace GlobalTheory.AbLaw
variable {Y : Scheme.{0}} {M : LB Y} {V : Y.Opens}
noncomputable def SecOn.chartBasicOpen (hM : M.IsLB) (i : M.ι) (a : Γ(Y, V))
    (h : Y.basicOpen a ≤ M.U i) : SecOn M V →ₗ[Γ(Y, V)] Γ(Y, Y.basicOpen a) where
  toFun s := SecOn.chart hM i h (SecOn.restrict M (Y.basicOpen_le a) s)
  map_add' s t := by rw [map_add, map_add]
  map_smul' r s := by
    rw [map_smulₛₗ, map_smul, RingHom.id_apply, Algebra.smul_def r]
    rfl
end GlobalTheory.AbLaw


