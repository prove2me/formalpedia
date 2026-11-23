-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:12:11.22411+00:00
-- url     : https://prove2.me/theorems/32bee2c0-5084-4b26-8f74-03db4e1735e1
-- title:
--   Exists Sec Of Local
-- statement:
--   Definitions and structural lemmas for Exists Sec Of Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSecOfLocal.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {Y Y' X₁ X₂ Z₁ Z₂ Z : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
def isoVal (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (r : Z ⟶ Y) (z : Z) (i₂ : L₂.ι) (i₁ : L₁.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((L₂.pull f₂).U (fun _ => i₂) ⊓ (L₁.pull f₁).U (fun _ => i₁)) (w.s (fun _ => i₂, fun _ => i₁))
def powVal {L : LB X₁} {g : Z₁ ⟶ X₁} {k : ℤ} (a : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => k)))
    (r : Z ⟶ Z₁) (z : Z) (i : L.ι) : Z.presheaf.stalk z :=
  gs r z (LB.wchart L (fun _ : Fin 1 => g) (fun _ => i)) (a.f (fun _ => i))
end GlobalTheory.FieldBaseChange


