-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AcyclicSliceSecCubeOfIsAffineOpen
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:07:47.491595+00:00
-- url     : https://prove2.me/theorems/9162b6c6-1a8e-4ea4-a516-d0a9e08ed1c7
-- title:
--   Acyclic Slice Sec Cube Of Is Affine Open
-- statement:
--   Definitions and structural lemmas for Acyclic Slice Sec Cube Of Is Affine Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/AcyclicSliceSecCubeOfIsAffineOpen.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SecOnBasicOpenLocalization
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_rs

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
noncomputable section
namespace GlobalTheory.AbLaw
variable {Y : Scheme.{0}} (M : LB Y)
def SecOnLE {V W : Y.Opens} (_h : W ≤ V) : Type := SecOn M W
namespace SecOnLE
variable {V W W' : Y.Opens}
instance (h : W ≤ V) : AddCommGroup (SecOnLE M h) := inferInstanceAs (AddCommGroup (SecOn M W))
instance (h : W ≤ V) : Module Γ(Y, V) (SecOnLE M h) := Module.compHom (SecOn M W) (rs Y h)
def restrict (h : W ≤ V) (h' : W' ≤ V) (e : W' ≤ W) : SecOnLE M h →ₗ[Γ(Y, V)] SecOnLE M h' where
  toFun s := SecOn.restrict M e s
  map_add' s t := (SecOn.restrict M e).map_add s t
  map_smul' a s := ((SecOn.restrict M e).map_smulₛₗ (rs Y h a) s).trans
    (congrArg (· • SecOn.restrict M e s) (rs_rs _ _ a))
end SecOnLE
def secCubeLE {κ : Type} (V : Finset κ → Y.Opens) (hV : Antitone V) : Cube.{0} κ Γ(Y, V ∅) :=
  Cube.mk (fun s => ModuleCat.of _ (SecOnLE M (hV (Finset.empty_subset s))))
    (fun h => SecOnLE.restrict M _ _ (hV h))
    (fun _ x => SecOn.restrict_self le_rfl x) (fun h h' x => SecOn.restrict_restrict (hV h) (hV h') x)
variable {M}
end GlobalTheory.AbLaw


