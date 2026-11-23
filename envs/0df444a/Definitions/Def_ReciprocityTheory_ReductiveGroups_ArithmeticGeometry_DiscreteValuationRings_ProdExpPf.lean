-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:40.890859+00:00
-- url     : https://prove2.me/theorems/c01eb7de-a1f1-4d5d-8e9d-301f53db1fc2
-- title:
--   Prod Exp Pf
-- statement:
--   Definitions and structural lemmas for Prod Exp Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdExpPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
section One
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
abbrev pGl : (thickObj R I e G).left ⟶ D.toPre.P.A.left := (U.gt e).pG.left
variable (I G) in
omit [IsDomain R] [GrpObj G] [IsCommMonObj G] in

abbrev fGl : (thickObj R I e G).left ⟶ G.left := (fstG I e G).left
abbrev Oφl (α : D.toPre.X) : Fin 4 → ((thickObj R I e G).left ⟶ D.toPre.P.A.left) := D.toPre.Oφ (U.gt e).pG α
abbrev tG (α : D.toPre.X) : LB.Gen (LB.LinComb D.toPre.P.L (Oφl U e α) Oinvε) := (U.gt e).t α
def wv {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  gm r z ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓ (U.LG.L.pull (fGl I G e)).U (fun _ => jL))
    ((U.w e).s (fun _ => jM, fun _ => jL))
def sv (σ : H0 U.LG.L k) {Z : Scheme.{0}} (q : Z ⟶ G.left) (z : Z) (jL : U.LG.L.ι) : Z.presheaf.stalk z :=
  gs q z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL))
variable (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
end One
section Box
variable {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
def bw (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (ψ : Z ⟶ X') (z : Z) (jN : Fin j → M.ι) (k : M'.ι) :
    (Z.presheaf.stalk z)ˣ := gm ψ z (LB.wchart M pr jN ⊓ M'.U k) (w.s (jN, k))
end Box
section Exp
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {j : ℕ} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {pD : IsPowDeg D'.toPre D.toPre j} {pA : IsPowPolAV A' A j} {pG : IsPowGrp G' G j}
  {U' : Unif I D' A' G'} {U : Unif I D A G}
variable (I pG) in

abbrev rhoE (e : ℕ) (i : Fin j) : (thickObj R I e G').left ⟶ (thickObj R I e G).left :=
  ((Over.pullback (thick R I e)).map (pG.pr i)).left
variable (pD) in

def omB {Z : Scheme.{0}} (y : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι)
    (ψ : Z ⟶ D'.toPre.P.A.left) : (Z.presheaf.stalk y)ˣ := bw pD.w ψ y (fun i => J (ψ ≫ (pD.pw.pr i).left)) (J' ψ)
end Exp
end ReciprocityTheory.ChartRestriction.G.DVR


