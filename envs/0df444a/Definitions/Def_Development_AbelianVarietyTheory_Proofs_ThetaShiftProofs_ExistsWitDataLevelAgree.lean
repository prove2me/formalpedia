-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T18:11:14.054606+00:00
-- url     : https://prove2.me/theorems/740b9122-5944-423c-8a64-94d424d1ae04
-- title:
--   Exists Wit Data Level Agree
-- statement:
--   Definitions and structural lemmas for Exists Wit Data Level Agree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Theorems.Thm_GlobalTheory_HostModel_arcIn_be_even
import Theorems.Thm_GlobalTheory_ToricData_eSec_baseMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def LevelAgree {D : Datum H} {l : Level H} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k}
    (a : ArcIn D l (RingHom.id c.F) k bF) (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}))
    [Module (𝓞 E) P.toPre.X] {φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
    (uF : F),
    (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
    uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
    ∀ (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n),
      ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
        (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
      ∀ (q₀ : QkPt a.D₀ F n) (q₁ q₂ : QkPt P.toPre F n),
        QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
        (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
        (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
        QkPt.Equiv P.toPre F q₁ q₂
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)
def witP : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) :=
  arcData (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF)
instance instModuleWitP : Module (𝓞 E) (witP c k bF).toPre.X := inferInstanceAs (Module (𝓞 E) (𝓞 E))
def witAct : letI := H.starRing; (witP c k bF).toPre.OAct (𝓞 E) :=
  letI := H.starRing
  arcOAct (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF) (𝓞 E)
    (arcIn c k bF).be_adj
def witMap : (witP c k bF).toPre.P.A.left ⟶ (arcIn c k bF).D₀.P.A.left :=
  baseMap (fun _ : 𝓞 E => 1) (PowerSeries.C (R := k)) (arcExp (X := 𝓞 E) k (arcForm l))
theorem witMap_eSec : eSec (witP c k bF).toPre.P.A ≫ witMap c k bF =
    spMap (PowerSeries.C (R := k)) ≫ eSec (arcIn c k bF).D₀.P.A :=
  eSec_baseMap _ _ _
def witIso : LB.Iso (witP c k bF).toPre.P.L ((arcIn c k bF).D₀.P.L.pull (witMap c k bF)) :=
  baseIso (fun _ : 𝓞 E => 1) (PowerSeries.C (R := k)) (arcExp (X := 𝓞 E) k (arcForm l))
section LevelPts
variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]
variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
    algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
include hF
end LevelPts
end GlobalTheory.HostModel


