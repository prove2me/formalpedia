-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:59.531577+00:00
-- url     : https://prove2.me/theorems/69eeee38-f6ef-4485-9da5-40bc69d19cae
-- title:
--   Exists Segre Coordinates
-- statement:
--   Definitions and structural lemmas for Exists Segre Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSegreCoordinates.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.SegreCoord
variable {X : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {T T' : Type} [CommRing T] [CommRing T']
def ev (y : Sp T) : T →+* (Sp T).presheaf.stalk y :=
  ((Sp T).presheaf.germ ⊤ y trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
theorem gs_sec (s : M.Sec) {Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) {j j' : M.ι} (h : r z ∈ M.U j) (h' : r z ∈ M.U j') :
    gs r z _ (s.f j) = (gm r z _ (M.g j j')).val * gs r z _ (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨h, h'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))
variable (M th) in

def Loc (x : Sp T ⟶ X) (v : σ → T) : Prop :=
  ∀ (y : Sp T) (j : M.ι), x y ∈ M.U j → ∃ u : ((Sp T).presheaf.stalk y)ˣ, ∀ i, gs x y _ ((th i).f j) = ev y (v i) * u
section Rep
variable {R : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {s : X ⟶ Sp R} (H : ProjRep I s M th)
include H
end Rep
section Box
variable {Y : Scheme.{0}} (p q : Y ⟶ X)
theorem gs_appLE' {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {U : X.Opens} {V : Y.Opens} (h : V ≤ p ⁻¹ᵁ U) (hz : r z ∈ V)
    (a : Γ(X, U)) : gs r z V ((p.appLE U V h).hom a) = gs (r ≫ p) z U a :=
  (gs_res r z h hz _).trans (gs_pull r p z U (h hz) a)
variable (M) in

abbrev boxLB : LB Y := LB.LinComb M (K := Fin 2) ![p, q] (fun _ => 1)
def boxF (a b : M.Sec) (j : Fin 2 → M.ι) : Γ(Y, LB.wchart M ![p, q] j) :=
  (p.appLE _ _ (LB.wchart_le M ![p, q] j 0)).hom (a.f (j 0)) * (q.appLE _ _ (LB.wchart_le M ![p, q] j 1)).hom (b.f (j 1))
theorem gs_boxF (a b : M.Sec) (j : Fin 2 → M.ι) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart M ![p, q] j) :
    gs r z _ (boxF p q a b j) = gs (r ≫ p) z _ (a.f (j 0)) * gs (r ≫ q) z _ (b.f (j 1)) :=
  (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) (gs_appLE' p r z _ hz _) (gs_appLE' q r z _ hz _))
def boxSec (a b : M.Sec) : (boxLB M p q).Sec where
  f := boxF p q a b
  compat j j' := fn_ext fun y hy => by
    refine ((gs_res (𝟙 Y) y _ hy _).trans (gs_boxF p q a b j _ y hy.1)).trans (Eq.trans ?_
      ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb M _ _ (𝟙 Y) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (gs_boxF p q a b j' _ y hy.2)))).symm)
    rw [gs_sec a (𝟙 Y ≫ p) y (LB.wchart_le M ![p, q] j 0 hy.1) (LB.wchart_le M ![p, q] j' 0 hy.2),
      gs_sec b (𝟙 Y ≫ q) y (LB.wchart_le M ![p, q] j 1 hy.1) (LB.wchart_le M ![p, q] j' 1 hy.2),
      Fin.prod_univ_two, zpow_one, zpow_one, Units.val_mul, mul_mul_mul_comm]
    rfl
variable (th) in

def boxTh (i : σ × σ) : (boxLB M p q).Sec := boxSec p q (th i.1) (th i.2)
end Box
section Segre
variable {R : Type} [CommRing R] (I : Ideal (MvPolynomial σ R))
open MvPolynomial in

def segreIdeal : Ideal (MvPolynomial (σ × σ) R) :=
  Ideal.span ({G | ∃ a b c d, G = MvPolynomial.X (a, b) * MvPolynomial.X (c, d) -
      MvPolynomial.X (a, d) * MvPolynomial.X (c, b)} ∪
    {G | ∃ b, ∃ F ∈ I, G = rename (fun i => (i, b)) F} ∪ {G | ∃ a, ∃ F ∈ I, G = rename (fun i => (a, i)) F})
def RankOne (β : R →+* T) (w : σ × σ → T) : Prop :=
  (∀ a b c d, w (a, b) * w (c, d) = w (a, d) * w (c, b)) ∧
    (∀ b, ∀ F ∈ I, MvPolynomial.eval₂ β (fun i => w (i, b)) F = 0) ∧
    (∀ a, ∀ F ∈ I, MvPolynomial.eval₂ β (fun i => w (a, i)) F = 0)
variable {I} {s : X ⟶ Sp R} (H : ProjRep I s M th) {Y : Scheme.{0}} {p q : Y ⟶ X} (hP : IsPullback p q s s)
include H hP
end Segre
end GlobalTheory.SegreCoord
end


