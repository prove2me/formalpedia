-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T18:12:46.446443+00:00
-- url     : https://prove2.me/theorems/e0b1b760-3141-44b9-8399-c7060dcaa7e9
-- title:
--   Exists Common Field
-- statement:
--   Definitions and structural lemmas for Exists Common Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Theorems.Thm_GlobalTheory_HostModel_arcIn_be_even
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
section General
variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
variable {F : Type} [Field F]
def unitStk (y : Sp F) : Fˣ →* ((Sp F).presheaf.stalk y)ˣ := Units.map (toStk y).toMonoidHom
def unitTop (x : Fˣ) : Γ(Sp F, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom x
end General
section Pull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {f : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {Φ : D'.P.A.left ⟶ D.P.A.left}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
def wVal (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (y : Sp F) (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι) (x : TF (R := R') F ⟶ D'.P.A) : ((Sp F).presheaf.stalk y)ˣ :=
  Geo.Tor.gw w x.left y (J (x.left ≫ Φ)) (J' x.left)
def GtRel (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (e : D.X ≃+ D'.X) (u : D.X → Fˣ) (g₀ : GtPtF D F) (g : GtPtF D' F) :
    Prop :=
  ∀ z, GenRel w (g.s (e z)) (g₀.s z) (u z : F)
variable (gp : IsGrpPullback D'.P.A D.P.A (spMap f) Φ) (hT : (TF (R := R') F).hom ≫ spMap f = (TF (R := R) F).hom)
def pushF (x : TF (R := R') F ⟶ D'.P.A) : TF (R := R) F ⟶ D.P.A :=
  Over.homMk (x.left ≫ Φ) ((Over.w (pushPt gp.1.w x)).trans hT)
variable {e : D.X ≃+ D'.X} (hc : ∀ y, (D'.c (e y)).left ≫ Φ = spMap f ≫ (D.c y).left)
variable {w : LB.Iso D'.P.L (D.P.L.pull Φ)} (hw : PGen w)
variable {he : eSec D'.P.A ≫ Φ = spMap f ≫ eSec D.P.A}
  (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
    (rigPullOf Φ (spMap f) he D.P.L D.rig))
end Pull
section ThetaShiftProofs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left} (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
  {F : Type} [Field F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F] (uF : F)
def IsTransport {n : ℕ} (q₀ : QkPt a.D₀ F n) (q : QkPt P.toPre F n) : Prop :=
  q.y = e q₀.y ∧ ∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))
variable {a w e uF}
theorem u_ne_zero (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X)) :
    uF ≠ 0 := by
  rw [hu]
  exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero)
variable [IsAlgClosed F] {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A} (hW : WitData a P oP φ he w e)
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
    algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
  (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X))
include hW hF hu
end ThetaShiftProofs
section Witness
open GlobalTheory.ToricData GlobalTheory.HostModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  (k : Type) [Field k] (bF : c.F →+* k)
def toricArc : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) :=
  arcData (X := 𝓞 E) k (arcIn c k bF).be (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF)
instance : Module (𝓞 E) (toricArc c k bF).toPre.X := inferInstanceAs (Module (𝓞 E) (𝓞 E))
def toricArcAct : letI := H.starRing; (toricArc c k bF).toPre.OAct (𝓞 E) :=
  letI := H.starRing
  arcOAct (X := 𝓞 E) k _ _ _ _ (𝓞 E) (arcIn c k bF).be_adj
def toricMap : (toricArc c k bF).toPre.P.A.left ⟶ (arcIn c k bF).D₀.P.A.left :=
  baseMap (X := 𝓞 E) (fun _ => 1) (PowerSeries.C (R := k)) (arcExp k (arcIn c k bF).be)
def toricIso : LB.Iso (toricArc c k bF).toPre.P.L ((arcIn c k bF).D₀.P.L.pull (toricMap c k bF)) :=
  baseIso (X := 𝓞 E) (fun _ => 1) (PowerSeries.C (R := k)) (arcExp k (arcIn c k bF).be)
def toricNeg : (arcIn c k bF).D₀.X ≃ₗ[𝓞 E] (toricArc c k bF).toPre.X := LinearEquiv.neg (𝓞 E) (M := 𝓞 E)
end Witness
end GlobalTheory.ArcTransport


