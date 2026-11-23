-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:30:37.144678+00:00
-- url     : https://prove2.me/theorems/2cc6f950-6146-4d6f-bcfd-c5ecd85486c0
-- title:
--   Phi Specialises
-- statement:
--   Definitions and structural lemmas for Phi Specialises, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory
namespace PhiSpec
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
section Base
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
def trT (m : T ⟶ D.P.A) : T ⊗ D.P.A ⟶ T ⊗ D.P.A :=
  lift (fst _ _) (padd D.P.A (snd _ _) (fst _ _ ≫ m))
def lineT (m : T ⟶ D.P.A) : Fin 2 → (T.left ⟶ D.P.A.left) := ![(1 : T ⟶ D.P.A).left, m.left]
def uT (k : ℕ) (α : D.X) (m : T ⟶ D.P.A) {T₁ : Over (Spec (CommRingCat.of R))} (ρ : T₁ ⟶ T ⊗ D.P.A)
    (z : T₁.left) (J : (T₁.left ⟶ D.P.A.left) → D.P.L.ι) : (T₁.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) k (cP D T₁ α) (ρ ≫ fst _ _ ≫ m) (ρ ≫ snd _ _) *
    (th D z J (cP D T₁ α) (ρ ≫ snd _ _) (ρ ≫ fst _ _ ≫ m))⁻¹
abbrev SecT (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (α : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (fun i => (snd T D.P.A).left ≫ D.famφB α i) (DegPre.famε k))
variable {D}
def PhiT {k : ℕ} (y : D.X) (gp : GtPt D T) (w : LB.Gen (LB.LinComb D.P.L (lineT D gp.b) (DegPre.lineε k)))
    (g g₂ : ∀ α, SecT D T k α) : Prop :=
  ∀ (α β : D.X), α + y = β → ∀ (T₁ : Over (Spec (CommRingCat.of R))) (ρ : T₁ ⟶ T ⊗ D.P.A) (z : T₁.left) (J),
    Good D.P.L z J → sval (g₂ β) ρ.left z J = sval (g α) (ρ ≫ trT D gp.b).left z J *
      (uT D k α gp.b ρ z J * (val (gp.s α) (ρ ≫ fst _ _).left z J * val w (ρ ≫ fst _ _).left z J)).val
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
end Base
section Charts
variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {G : X' ⟶ X} {K : Type} [Fintype K]
end Charts
section Special
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {T : Over (Spec (CommRingCat.of R))} {F : Type} [Field F] [Algebra (FractionRing R') F]
  (hD : IsPullDeg φ D D') {h : (TF (R := R') F).left ⟶ T.left} (hT : (TF (R := R') F).hom ≫ spMap φ = h ≫ T.hom)
  {Θ : (DegPre.BF D' F).left ⟶ (T ⊗ D.P.A).left}
  (hΘ₁ : Θ ≫ (fst T D.P.A).left = (fst (TF (R := R') F) D'.P.A).left ≫ h)
  (hΘ₂ : Θ ≫ (snd T D.P.A).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
def liftB (ρ : T' ⟶ DegPre.BF D' F) : Over.mk (T'.hom ≫ spMap φ) ⟶ T ⊗ D.P.A :=
  Over.homMk (ρ.left ≫ Θ) (by
    show (ρ.left ≫ Θ) ≫ (T ⊗ D.P.A).hom = T'.hom ≫ spMap φ
    rw [← Over.w (fst T D.P.A), Category.assoc, ← Category.assoc Θ, hΘ₁, Category.assoc, ← hT, ← Over.w ρ,
      ← Over.w (fst (TF (R := R') F) D'.P.A)]
    simp only [Category.assoc])
variable (Θ) in

def SecMaps {k : ℕ} (x : D'.X) (s : SecT D T k (hD.xe x))
    (s' : LB.Sec (LB.LinComb D'.P.L (DegPre.famφ D' F x) (DegPre.famε k))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι) (q : Fin 4 → D'.P.L.ι),
    (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
    (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
    gs (r ≫ Θ) z (LB.wchart D.P.L (fun i => (snd T D.P.A).left ≫ D.famφB (hD.xe x) i) p) (s.f p) =
      (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
        gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) (s'.f q)
end Special
end PhiSpec
end GlobalTheory


