-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:42:38.335373+00:00
-- url     : https://prove2.me/theorems/ac98549a-c90d-44fb-9e7d-5260a837fd90
-- title:
--   Exists Hom Of Locally Rel
-- statement:
--   Definitions and structural lemmas for Exists Hom Of Locally Rel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsHomOfLocallyRel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
namespace GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
def IsSumAt {k : Type} [Field k] (a b c : Spec (.of k) ⟶ scheme W) : Prop :=
  ∀ (ρ : R →+* k) (P Q : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P)
    (hQ : IsUnimodularSol (W.map ρ) Q), a = ptHom W ρ P hP → b = ptHom W ρ Q hQ →
    ∃ h : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), c = ptHom W ρ _ h
def IsNonsingularAt {k : Type} [Field k] (a : Spec (.of k) ⟶ scheme W) : Prop :=
  ∀ (ρ : R →+* k) (P : Fin 3 → k) (hP : IsUnimodularSol (W.map ρ) P),
    a = ptHom W ρ P hP → (W.map ρ).toProjective.Nonsingular P
end GlobalTheory.SmoothLocusAdd
namespace GlobalTheory
open MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
end GlobalTheory


