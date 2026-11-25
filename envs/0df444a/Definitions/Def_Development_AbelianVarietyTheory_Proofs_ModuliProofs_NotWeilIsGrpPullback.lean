-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:57:06.787524+00:00
-- url     : https://prove2.me/theorems/a6a78f9c-9c3f-4ce0-8ed6-dbce5baae271
-- title:
--   Not Weil Is Grp Pullback
-- statement:
--   Definitions and structural lemmas for Not Weil Is Grp Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/NotWeilIsGrpPullback.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
abbrev oneChart (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
abbrev manyChart {X : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) : LB X :=
  ⟨κ, fun _ => ⊤, fun i j => res inf_le_left (v i * (v j)⁻¹)⟩
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]
@[ext] structure Heis (R : Type) where

  a : R

  b : R

  c : R
instance (R : Type) [CommRing R] : Group (Heis R) where
  mul g h := ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩
  one := ⟨0, 0, 0⟩
  inv g := ⟨-g.a, -g.b, g.a * g.b - g.c⟩
  mul_assoc g h k := Heis.ext (add_assoc _ _ _) (add_assoc _ _ _) (by
    show g.c + h.c + g.a * h.b + k.c + (g.a + h.a) * k.b = g.c + (h.c + k.c + h.a * k.b) + g.a * (h.b + k.b)
    ring)
  one_mul g := Heis.ext (zero_add _) (zero_add _) (by show 0 + g.c + 0 * g.b = g.c; ring)
  mul_one g := Heis.ext (add_zero _) (add_zero _) (by show g.c + 0 + g.a * 0 = g.c; ring)
  inv_mul_cancel g := Heis.ext (neg_add_cancel _) (neg_add_cancel _) (by
    show g.a * g.b - g.c + g.c + -g.a * g.b = 0; ring)
def Heis.map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Heis R →* Heis R' :=
  MonoidHom.mk' (fun g => ⟨f g.a, f g.b, f g.c⟩) fun g h => Heis.ext (map_add f _ _) (map_add f _ _) (by
    show f (g.c + h.c + g.a * h.b) = f g.c + f h.c + f g.a * f h.b
    rw [map_add, map_add, map_mul])
def heisFunctor (S : Scheme.{0}) : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Heis Γ(T.unop.left, ⊤))
  map g := GrpCat.ofHom (Heis.map g.unop.left.appTop.hom)
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => by
    have e : ∀ a, (𝟙 T : T ⟶ T).unop.left.appTop.hom a = a := fun a =>
      congrArg (fun q => q.hom a) (Scheme.Hom.id_appTop (X := T.unop.left))
    exact Heis.ext (e _) (e _) (e _))
  map_comp g g' := GrpCat.hom_ext (MonoidHom.ext fun x => rfl)
abbrev heisObj (S : Scheme.{0}) : Over S := Over.mk (𝔸(Fin 3; S) ↘ S)
def heisEquiv {S : Scheme.{0}} (T : Over S) : (T ⟶ heisObj S) ≃ Heis Γ(T.left, ⊤) where
  toFun x := ⟨x.left.appTop (AffineSpace.coord S 0), x.left.appTop (AffineSpace.coord S 1),
    x.left.appTop (AffineSpace.coord S 2)⟩
  invFun g := Over.homMk (AffineSpace.homOfVector T.hom ![g.a, g.b, g.c]) (AffineSpace.homOfVector_over _ _)
  left_inv x := Over.OverMorphism.ext (AffineSpace.hom_ext
    ((AffineSpace.homOfVector_over _ _).trans (Over.w x).symm) fun i => by
      refine (AffineSpace.homOfVector_appTop_coord _ _ i).trans ?_
      fin_cases i <;> rfl)
  right_inv g := Heis.ext (AffineSpace.homOfVector_appTop_coord _ _ _) (AffineSpace.homOfVector_appTop_coord _ _ _)
    (AffineSpace.homOfVector_appTop_coord _ _ _)
def heisRep (S : Scheme.{0}) : (heisFunctor S ⋙ forget _).RepresentableBy (heisObj S) where
  homEquiv {T} := heisEquiv T
  homEquiv_comp _ _ := rfl
instance (S : Scheme.{0}) : GrpObj (heisObj S) := GrpObj.ofRepresentableBy _ _ (heisRep S)
end GlobalTheory.WeilPullNoncomm
namespace GlobalTheory
open WeilPullNoncomm
end GlobalTheory


