-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:53:49.504824+00:00
-- url     : https://prove2.me/theorems/19d62934-af70-4fd6-bb63-774f8ce5ab68
-- title:
--   Exists Line Bundle Generator Extending Dense Part
-- statement:
--   Definitions and structural lemmas for Exists Line Bundle Generator Extending Dense Part, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GenericExtend
def ExtAt {Q Y : Scheme.{0}} (J : Q ⟶ Y) (W : Y.Opens) (f : Γ(Q, J ⁻¹ᵁ W)) (y : Y) : Prop :=
  ∃ (V : Y.Opens) (h : V ≤ W) (s : Γ(Y, V)), y ∈ V ∧
    (J.appLE V (J ⁻¹ᵁ V) le_rfl).hom s = resG Q (J.preimage_mono h) f
def Compat {Q Y : Scheme.{0}} (N : LB Y) (J : Q ⟶ Y) (τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Q) (z : Z) (a b : N.ι), J (r z) ∈ N.U a → J (r z) ∈ N.U b →
    gm r z (J ⁻¹ᵁ N.U a) (τ a) =
      gm (r ≫ J) z (N.U a ⊓ N.U b) (N.g a b) * gm r z (J ⁻¹ᵁ N.U b) (τ b)
end GlobalTheory.GenericExtend


