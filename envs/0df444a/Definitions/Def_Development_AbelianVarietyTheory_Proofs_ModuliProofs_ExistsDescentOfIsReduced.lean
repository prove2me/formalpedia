-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:55.156107+00:00
-- url     : https://prove2.me/theorems/6520d7e9-2a68-4322-8f75-ebb126b855af
-- title:
--   Exists Descent Of Is Reduced
-- statement:
--   Definitions and structural lemmas for Exists Descent Of Is Reduced, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDescentOfIsReduced.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
def gsHom (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom
abbrev rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom
abbrev gg (L : LB X) (r : Z ⟶ X) (z : Z) (i j : L.ι) : (Z.presheaf.stalk z)ˣ :=
  gm r z (L.U i ⊓ L.U j) (L.g i j)
def IsLocSec (L : LB X) (W : X.Opens) (m : ∀ i, Γ(X, W ⊓ L.U i)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i j, r z ∈ W → r z ∈ L.U i → r z ∈ L.U j →
    gs r z _ (m i) = (gg L r z i j).val * gs r z _ (m j)
section Lin
variable {L : LB X}
abbrev twist (L : LB X) (t : X ⟶ X) : LB X := LB.LinComb L (K := Fin 2) ![𝟙 X, t] ![1, -1]
def uv {t : X ⟶ X} (u : LB.Gen (twist L t)) (r : Z ⟶ X) (z : Z) (i j : L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z (LB.wchart L (K := Fin 2) ![𝟙 X, t] ![i, j]) (u.s ![i, j])
variable {C : Type} {t : C → (X ⟶ X)}
def IsInv (u : ∀ c, LB.Gen (twist L (t c))) (W : X.Opens) (s : ∀ i, Γ(X, W ⊓ L.U i)) : Prop :=
  ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ W → r z ∈ L.U i → (r ≫ t c) z ∈ L.U k →
    gs r z _ (s i) = (uv (u c) r z i k).val * gs (r ≫ t c) z _ (s k)
variable [Group C] [Finite C]
end Lin
section Desc
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}
def LocTransitive (t : C → (X ⟶ X)) (π : X ⟶ Y) : Prop :=
  ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X), g₁ ≫ π = g₂ ≫ π → ∀ z : Z,
    ∃ (c : C) (Z' : Scheme.{0}) (a : Z' ⟶ Z) (_ : IsOpenImmersion a) (z' : Z'),
      a z' = z ∧ a ≫ g₁ = (a ≫ g₂) ≫ t c
def IsInvGen (u : ∀ c, LB.Gen (twist L (t c))) (W : X.Opens) (e : ∀ i, Γ(X, W ⊓ L.U i)ˣ) : Prop :=
  (∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i j, r z ∈ W → r z ∈ L.U i → r z ∈ L.U j →
    gm r z _ (e i) = gg L r z i j * gm r z _ (e j)) ∧
  ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i k, r z ∈ W → r z ∈ L.U i →
    (r ≫ t c) z ∈ L.U k → gm r z _ (e i) = uv (u c) r z i k * gm (r ≫ t c) z _ (e k)
end Desc
section Grp
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
end Grp
end GlobalTheory.LinDescent
namespace GlobalTheory.LinDescent
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
end GlobalTheory.LinDescent


