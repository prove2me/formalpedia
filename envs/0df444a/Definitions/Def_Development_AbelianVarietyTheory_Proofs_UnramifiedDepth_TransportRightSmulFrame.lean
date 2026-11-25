-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TransportRightSmulFrame
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TransportRightSmulFrame
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T16:36:25.73819+00:00
-- url     : https://prove2.me/theorems/b6aaa29a-7a6d-417d-8237-e9cee166c79e
-- title:
--   Transport Right Smul Frame
-- statement:
--   Definitions and structural lemmas for Transport Right Smul Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TransportRightSmulFrame.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
section
variable {R₀ : Type} [CommRing R₀] (B : BX R₀) {R : LAlg R₀}
lemma smul_inj {x y : B.G R} (w : B.P R x y) {l l' : (R : Type)ˣ}
    (h : B.smul l w = B.smul l' w) : l = l' :=
  (B.trans w (B.smul l' w)).unique h rfl
noncomputable def frameEquiv {x y : B.G R} (w : B.P R x y) : (R : Type)ˣ ≃ B.P R x y :=
  Equiv.ofBijective (fun l => B.smul l w)
    ⟨fun _ _ h => smul_inj B w h, fun v => (B.trans w v).exists⟩
end
end GlobalTheory


