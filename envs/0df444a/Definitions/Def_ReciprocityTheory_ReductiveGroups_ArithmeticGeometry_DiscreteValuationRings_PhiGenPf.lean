-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:52.826805+00:00
-- url     : https://prove2.me/theorems/1f7513df-7d57-41d4-8e9e-0041b9d1859b
-- title:
--   Phi Gen Pf
-- statement:
--   Definitions and structural lemmas for Phi Gen Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/PhiGenPf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.DVR
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
def cP (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ
abbrev th {T : Over (Spec (CommRingCat.of R))} (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) := cubV D.cub z J
def uVal (k : ℕ) (α : D.X) (m : TF (R := R) F ⟶ D.P.A) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ DegPre.BF D F)
    (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) : (T.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) k (cP D T α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ DegPre.prB D F) *
    (th D z J (cP D T α) (ρ ≫ DegPre.prB D F) (ρ ≫ fst _ _ ≫ m))⁻¹
section Values
variable {D F} {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
  {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ
end Values
variable {D F}
def PhiVal {k : ℕ} (p : QkPt D F k) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (s t : ∀ α : D.X, LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))) : Prop :=
  ∀ (α β : D.X), α + p.y = β → ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ DegPre.BF D F) (z : T.left) (J),
    Good D.P.L z J → sval (t β) ρ.left z J = sval (s α) (ρ ≫ DegPre.trPt D F p.g.b).left z J *
      (uVal D F k α p.g.b ρ z J * val (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) (ρ ≫ fst _ _).left z J).val
variable (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k)
  (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
include hG hw
end ReciprocityTheory.ChartRestriction.G.DVR


