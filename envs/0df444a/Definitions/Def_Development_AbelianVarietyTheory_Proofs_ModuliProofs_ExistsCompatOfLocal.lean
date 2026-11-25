-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:31:01.911156+00:00
-- url     : https://prove2.me/theorems/20bb82d2-34f8-4583-ac54-6e64f2d57ffb
-- title:
--   Exists Compat Of Local
-- statement:
--   Definitions and structural lemmas for Exists Compat Of Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsCompatOfLocal.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
def MapBy (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left
def GeoGood (t t' : TObj g k J b s) (Sg : Set S) : Prop :=
  ∀ (K : Type) [Field K] (x : Sp K ⟶ S), Set.range x ⊆ Sg →
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (su : Sp Ω ⟶ Sp o) (u : TObj g k J b su)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left),
      MapBy u t (spMap i ≫ x) ψ ∧ MapBy u t' (spMap i ≫ x) ψ'
def Compat (t t' : TObj g k J b s) {X : Scheme.{0}} (c₀ : X ⟶ t.A.left) (f : X ⟶ t'.A.left) : Prop :=
  f ≫ t'.A.hom = c₀ ≫ t.A.hom ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ (B : Type) [Field B] (z : Sp B ⟶ u.A.left) (y : Sp B ⟶ X), y ≫ c₀ = z ≫ ψ → y ≫ f = z ≫ ψ'
end GlobalTheory.TUniq


