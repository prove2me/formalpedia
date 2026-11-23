-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:51.25716+00:00
-- url     : https://prove2.me/theorems/6a33178a-e736-4615-842a-7b1f6a326ba8
-- title:
--   Is Unit Ev
-- statement:
--   Definitions and structural lemmas for Is Unit Ev, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsUnitEv.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.WtRat
variable {R R' : Type} [CommRing R] [CommRing R'] {Y Y' : Scheme.{0}}
def ev (g : Sp R ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ V) : Γ(Y, V) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (g.appLE V ⊤ h).hom
end GlobalTheory.SS.WtRat
end


