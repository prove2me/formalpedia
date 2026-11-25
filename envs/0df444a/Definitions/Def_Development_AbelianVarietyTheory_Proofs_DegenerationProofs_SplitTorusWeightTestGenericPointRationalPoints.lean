-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:32:23.212065+00:00
-- url     : https://prove2.me/theorems/748efd0c-51dc-4c01-b4b1-50c608bb611d
-- title:
--   Split Torus Weight Test Generic Point Rational Points
-- statement:
--   Definitions and structural lemmas for Split Torus Weight Test Generic Point Rational Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusWeightTestGenericPointRationalPoints.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
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
def wtDefect {P G T : Scheme.{0}} (a b : P ⟶ G) (c : P ⟶ T) (V : G.Opens) (u : Γ(G, V))
    (e : Γ(T, ⊤)) : Γ(P, a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V) :=
  (a.appLE V _ inf_le_left).hom u - (c.appLE ⊤ _ le_top).hom e * (b.appLE V _ inf_le_right).hom u
end GlobalTheory.SS.WtRat
end


