-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:23.650274+00:00
-- url     : https://prove2.me/theorems/44dfaca8-28ca-4ab4-b5a5-fefe204e2eed
-- title:
--   Exists Stalk Derivation Of Is Pullback
-- statement:
--   Definitions and structural lemmas for Exists Stalk Derivation Of Is Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsStalkDerivationOfIsPullback.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
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
namespace GlobalTheory.SS.StalkDer
variable {K : Type} [Field K] {P : Scheme.{0}} {X : Over (Sp K)}
def gm (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) :
    Γ(X.left, V) →+* P.presheaf.stalk z :=
  (P.presheaf.germ (f ⁻¹ᵁ V) z hz).hom.comp (f.app V).hom
def gmDual (D : VF X) (f : P ⟶ X.left) (z : P) (V : X.left.Opens) (hz : z ∈ f ⁻¹ᵁ V) :
    Γ(X.left, V) →+* DualNumber (P.presheaf.stalk z) where
  toFun b := (gm f z V hz b, gm f z V hz (D.D V b))
  map_one' := TrivSqZeroExt.ext (map_one _) (by
    show gm f z V hz (D.D V 1) = 0
    have := D.const V 1
    rw [map_one] at this
    rw [this, map_zero])
  map_mul' a b := TrivSqZeroExt.ext (map_mul _ a b) (by
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    show gm f z V hz (D.D V (a * b)) = gm f z V hz a * gm f z V hz (D.D V b) +
      gm f z V hz (D.D V a) * gm f z V hz b
    rw [D.leibniz, map_add, map_mul, map_mul]; ring)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (by
    show gm f z V hz (D.D V 0) = 0
    rw [map_zero, map_zero])
  map_add' a b := TrivSqZeroExt.ext (map_add _ a b) (by
    show gm f z V hz (D.D V (a + b)) = gm f z V hz (D.D V a) + gm f z V hz (D.D V b)
    rw [map_add, map_add])
end GlobalTheory.SS.StalkDer
namespace GlobalTheory.SS
end GlobalTheory.SS
end


