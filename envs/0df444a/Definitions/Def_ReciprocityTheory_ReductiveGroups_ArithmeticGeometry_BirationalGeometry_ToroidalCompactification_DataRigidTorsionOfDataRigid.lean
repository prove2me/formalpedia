-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:04:24.251258+00:00
-- url     : https://prove2.me/theorems/0e77962a-5141-47b2-be4a-53a9b3040126
-- title:
--   Data Rigid Torsion Of Data Rigid
-- statement:
--   Definitions and structural lemmas for Data Rigid Torsion Of Data Rigid, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DataRigidTorsionOfDataRigid.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
def LatFinOrdSt : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (b : LinearMap.BilinForm ℤ Y),
    (∀ y z, b y z = b z y) → (∀ y, y ≠ 0 → 0 < b y y) →
    ∀ σ : Y ≃ₗ[ℤ] Y, (∀ y z, b (σ y) (σ z) = b y z) → ∃ n : ℕ, 0 < n ∧ σ ^ n = 1
def LatMinkowskiSt : Prop :=
  ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (σ : Y ≃ₗ[ℤ] Y) (n M : ℕ), 0 < n →
    σ ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, σ y = y + M • z) → σ = 1
def PairThetaSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    letI := H.starRing
    ∃ (θ : P.toPre.P.A ≅ P.toPre.P.A) (wθ : LB.Iso P.toPre.P.L (P.toPre.P.L.pull θ.hom.left))
      (w₁' : LB.Iso P.toPre.P.L (a.D₀.P.L.pull (θ.hom.left ≫ φ₂))),
      IsMonHom θ.hom ∧ θ.hom.left ≫ φ₂ = φ₁ ∧ (∀ x, oP.onB.act x ≫ θ.hom = θ.hom ≫ oP.onB.act x) ∧
      (∀ y, (P.toPre.c (e₁ y)).left ≫ θ.hom.left = (P.toPre.c (e₂ y)).left) ∧ wθ.IsGen ∧
      HEq w₁' w₁ ∧ Tri w₂ wθ w₁'
def DataRigidTorsion : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (t : SAB H (Sp (PowerSeries k)))
    (P : PELUnif (Ideal.span {PowerSeries.X}) t), P.TorsionIso →
    ∀ (φ₁ φ₂ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.D.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.D.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X),
    WitData a P.D P.oD φ₁ he₁ w₁ e₁ → WitData a P.D P.oD φ₂ he₂ w₂ e₂ →
    (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ (n : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing k) n),
        ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
          (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
        ∀ (q₀ : Out.QkPt a.D₀ F n) (q₁ q₂ : Out.QkPt P.D.toPre F n),
          QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
          (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          Out.QkPt.Equiv P.D.toPre F q₁ q₂) →
    φ₁ = φ₂ ∧ e₁ = e₂ ∧ HEq w₁ w₂
section Gt
open ReciprocityTheory.ChartRestriction.G.Out
def GtCoordToGtSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], Nonempty (GtCoord I D e G) →
    ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : E.B ≅ thickObj R I e D.P.A) (xe : D.X ≃+ E.X), IsMonHom β.hom ∧
      (∀ χ : D.X, ∃ w : LB.Iso (E.O (xe χ)).L (LB.LinComb D.P.L
          (fun k => ((Over.map (thick R I e)).map β.hom ≫ D.prBe I e).left ≫
            D.Oφ (𝟙 _) χ k) Oε), w.IsGen) ∧
      E.IsGt (thickObj R I e G)
end Gt
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


