-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:33.280225+00:00
-- url     : https://prove2.me/theorems/3deaa8ba-712b-41a0-8bce-328a83f9f76c
-- title:
--   Data Rigid St
-- statement:
--   Definitions and structural lemmas for Data Rigid St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DataRigidSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabMapCubical
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def WitData {k : Type} [Field k] {b : O →+* k} (a : ArcIn D l β k b)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) : Prop :=
  letI := H.starRing
  IsGrpPullback P.toPre.P.A a.D₀.P.A (spMap (PowerSeries.C (R := k))) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.toPre.P.A) (fun _ => 1)) P.toPre.rig
      (rigPullOf φ (spMap (PowerSeries.C (R := k))) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (oP.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ y, (P.toPre.c (e y)).left ≫ φ = spMap (PowerSeries.C (R := k)) ≫ (a.D₀.c y).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ y, GenRel w (LB.pullGen _ _ _ (P.toPre.psi (e y)) (Out.jFK (R := PowerSeries k) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := k) F)) (uF ^ (a.be y y / 2))
def DataRigidSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : Out.DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ →
    (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
      (uF : F),
      (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
        algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
      uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
      ∀ (n : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing k) n),
        ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
          (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
        ∀ (q₀ : Out.QkPt a.D₀ F n) (q₁ q₂ : Out.QkPt P.toPre F n),
          QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
          (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
          Out.QkPt.Equiv P.toPre F q₁ q₂) →
    φ₁ = φ₂ ∧ e₁ = e₂ ∧ HEq w₁ w₂
def QkToAkInjSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), Out.AdmBase R I →
  ∀ (Dd : Out.DegData R I) (A : Out.PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Out.Unif I Dd A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
    (n : ℕ), 1 ≤ n → ∀ (p p' : Out.QkPt Dd.toPre F n) (x : Out.TFK (R := R) F ⟶ A.A),
      Out.QkToAkU U.toUnifPre F n p x → Out.QkToAkU U.toUnifPre F n p' x → Out.QkPt.Equiv Dd.toPre F p p'
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


