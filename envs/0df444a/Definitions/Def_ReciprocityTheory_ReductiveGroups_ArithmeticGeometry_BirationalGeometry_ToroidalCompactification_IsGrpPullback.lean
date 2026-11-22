-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:12.687251+00:00
-- url     : https://prove2.me/theorems/9c28c133-e20b-4722-b7d8-c31c21479ef1
-- title:
--   Is Grp Pullback
-- statement:
--   Definitions and structural lemmas for Is Grp Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsGrpPullback.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S X : Scheme.{0}}
def abLocus (G : Over S) : Set S :=
  {s | ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S), s ∈ Set.range t → IsProper (pullback.snd G.hom t)}
structure OAct (O : Type) [CommRing O] (G : Over S) [GrpObj G] where

  act : O → (G ⟶ G)
  hom : ∀ a, IsMonHom (act a)
  one : act 1 = 𝟙 G
  mul : ∀ a b, act (a * b) = act a ≫ act b
  add : ∀ a b, act (a + b) = act a * act b
def IsGrpPullback {S' : Scheme.{0}} (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : G'.left ⟶ G.left) : Prop :=
  IsPullback φ G'.hom G.hom f ∧
    ∀ (T : Over S') (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G),
      x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (x₀ * y₀).left = (x * y).left ≫ φ
abbrev resG (X : Scheme.{0}) {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom
def secOn (L : LB X) (V : X.Opens) : Set (∀ i, Γ(X, V ⊓ L.U i)) :=
  {s | ∀ i j,
    resG X (inf_le_left : V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i) (s i) =
      resG X (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          V ⊓ L.U i ⊓ L.U j ≤ L.U i ⊓ L.U j) (L.g i j : Γ(X, L.U i ⊓ L.U j)) *
        resG X (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          V ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U j) (s j)}
def LBIso (L M : LB X) : Prop := ∃ w : LB.Iso L M, w.IsGen
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


