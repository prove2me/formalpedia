-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_AbelianLocusModels
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_AbelianLocusModels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:41:57.190841+00:00
-- url     : https://prove2.me/theorems/040ddcad-8b81-449b-b2ab-1342b776eefa
-- title:
--   Abelian Locus Models
-- statement:
--   Definitions and structural lemmas for Abelian Locus Models, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/AbelianLocusModels.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
def IsIntegersOf (V C : Type) [CommRing V] [NormedField C] [Algebra V C] : Prop :=
  Function.Injective (algebraMap V C) ∧ ∀ x : C, (∃ a : V, algebraMap V C a = x) ↔ ‖x‖ ≤ 1
example (p : ℕ) [Fact p.Prime] : IsIntegersOf ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val_injective, fun x => ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩⟩
def primeToPart (p n : ℕ) : ℕ := n / p ^ n.factorization p
example : primeToPart 3 45 = 5 := by
  have h : (45 : ℕ).factorization 3 = 2 := by
    rw [show (45 : ℕ) = 3 ^ 2 * 5 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.Prime.factorization_pow (by norm_num), Nat.Prime.factorization (by norm_num)]
    simp
  rw [primeToPart, h]
  norm_num
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def AbelianLocusLevels (p : ℕ) (Y : Model Xo c β) : Prop :=
  ∃ U : Y.X.Opens, (U : Set Y.X) = abLocus Y.t.G ∧
    (∀ a : D.La, primeToPart p l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) → Y.Extends U (Y.oF.eta a)) ∧
    (∀ a : D.La, (∃ b : D.La, primeToPart p l.A • a = l.A • b) → Y.Extends U (Y.oF.etaA a))
def HasGoodReduction (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K]
    (y : Sp K ⟶ Xo.XF c) : Prop :=
  ∃ (B : Over (Sp V)) (_ : GrpObj B) (L : LB B.left),
    IsAbelianScheme B ∧ L.IsLB ∧ ReciprocityTheory.ChartRestriction.G.Out.RelAmple B L ∧
    ∃ (Ay : Over (Sp K)) (_ : GrpObj Ay) (φ : Ay.left ⟶ Y.oF.t.G.left) (ψ : Ay.left ⟶ B.left),
      IsGrpPullback Ay Y.oF.t.G y φ ∧ IsGrpPullback Ay B (spMap (algebraMap V K)) ψ ∧
      LBIso (Y.oF.t.PP.L.pull φ) (L.pull ψ)
def GoodPointsExtend (Y : Model Xo c β) (V K : Type) [CommRing V] [Field K] [Algebra V K] : Prop :=
  ∀ (γ : O →+* V) (y : Sp K ⟶ Xo.XF c),
    y ≫ pullback.snd _ _ ≫ spMap β = spMap (algebraMap V K) ≫ spMap γ →
    HasGoodReduction Y V K y →
    ∃ yt : Sp V ⟶ Y.X, yt ≫ Y.s = spMap γ ∧ spMap (algebraMap V K) ≫ yt = y ≫ Y.j ∧
      Set.range yt ⊆ abLocus Y.t.G
structure OneModel (p : ℕ) (Y : Model Xo c β) : Prop where

  acts : Y.LevelActs

  descends : l.A = 1 → Y.Descends

  push : PushInvertible Y.t.G Y.t.PP.L

  abLevels : AbelianLocusLevels p Y

  extDVR : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [Algebra V K] [IsFractionRing V K],
    GoodPointsExtend Y V K

  extInt : ∀ (V C : Type) [CommRing V] [NormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
    [CharZero C] [Algebra V C], ‖(p : C)‖ < 1 → IsIntegersOf V C → GoodPointsExtend Y V C
end GlobalTheory.IndefiniteRowSideFullHecke.AbelianLocusModels


