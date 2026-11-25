-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T14:15:11.677322+00:00
-- url     : https://prove2.me/theorems/3e39f827-1679-4754-8e92-53cd01edbf23
-- title:
--   Is Theta Pt Over Move
-- statement:
--   Definitions and structural lemmas for Is Theta Pt Over Move, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
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
namespace GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
section Value
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {n : ℤ} {T : Over S}
  {s : LB.Sec (LPow A L n T)} {x : T ⟶ A}
  {ρ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => n))} {c : Γ(T.left, ⊤)}
end Value
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
def psi : (T ⊗ A).left ⟶ (T₀ ⊗ G).left := (psiO hp τ hτ).left
section Points
include hp hτ
end Points
variable {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
def GenThrough (w : LB.Iso L₁ (L₀.pull φ)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (ψ' : K → (Y' ⟶ A.left))
    (ψ : K → (Y ⟶ G.left)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L₁ ψ' ε)) (t : LB.Gen (LB.LinComb L₀ ψ ε))
    (h : Y' ⟶ Y) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    val t (r ≫ h) z J = (∏ k, wVal w z J J' (r ≫ ψ' k) ^ ε k) * val a r z J'
def SecRel (w : LB.Iso L₁ (L₀.pull φ)) {a : ℤ} (s : LB.Sec (LPow A L₁ a T)) (s₀ : LB.Sec (LPow G L₀ a T₀)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    VVRank.sv G s₀ (r ≫ psi hp τ hτ) z J =
      (wVal w z J J' (r ≫ (snd T A).left) ^ a).val * VVRank.sv A s r z J'
end GlobalTheory.ThetaPtMove


