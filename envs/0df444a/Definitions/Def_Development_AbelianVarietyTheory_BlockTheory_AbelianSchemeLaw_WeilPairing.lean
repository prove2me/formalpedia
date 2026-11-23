-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_WeilPairing
-- name    : Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_WeilPairing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:25.122924+00:00
-- url     : https://prove2.me/theorems/141264e6-f55e-452b-9997-5cc409b49204
-- title:
--   Weil Pairing
-- statement:
--   Definitions and structural lemmas for Weil Pairing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/WeilPairing.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_Imports
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
def tors {S : Scheme.{0}} (P : PolAV S) (T : Over S) (k : ℕ) : Subgroup (T ⟶ P.A) where
  carrier := {x | x ^ k = 1}
  one_mem' := one_pow k
  mul_mem' := by
    intro x y hx hy
    haveI := P.isAb.comm
    have hc : Commute x y := mul_comm x y
    have hx' : x ^ k = 1 := hx
    have hy' : y ^ k = 1 := hy
    show (x * y) ^ k = 1
    rw [hc.mul_pow, hx', hy', _root_.mul_one]
  inv_mem' := by
    intro x hx
    have hx' : x ^ k = 1 := hx
    show x⁻¹ ^ k = 1
    rw [inv_pow, hx', inv_one]
def unitSpec {K : Type} [CommRing K] (u : Kˣ) : Γ(Spec (CommRingCat.of K), ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom u
def WeilExistsUnique : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) (T : Over S)
    (x y : T ⟶ P.A), x ∈ tors P T k → y ∈ tors P T k →
    ∃! c : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L (k : ℤ) x y c
def WeilMulLeft : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) (T : Over S)
    (x x' y : T ⟶ P.A), x ∈ tors P T k → x' ∈ tors P T k → y ∈ tors P T k →
    ∀ c c' : Γ(T.left, ⊤)ˣ, WeilIs P.A P.L (k : ℤ) x y c → WeilIs P.A P.L (k : ℤ) x' y c' →
      WeilIs P.A P.L (k : ℤ) (x * x') y (c * c')
def WeilAlternating : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ) (T : Over S)
    (x : T ⟶ P.A), x ∈ tors P T k → WeilIs P.A P.L (k : ℤ) x x 1
def WeilLevelChange : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (k l : ℕ) (T : Over S),
    IsUnit ((k * l : ℕ) : Γ(T.left, ⊤)) →
    ∀ (x y : T ⟶ P.A), x ∈ tors P T (k * l) → y ∈ tors P T k →
    ∀ c : Γ(T.left, ⊤)ˣ,
      WeilIs P.A P.L ((k * l : ℕ) : ℤ) x y c ↔ WeilIs P.A P.L (k : ℤ) (x ^ l) y c
def WeilLaws : Prop :=
  WeilExistsUnique ∧ WeilMulLeft ∧ WeilAlternating ∧ WeilLevelChange
def WeilNondegenerate : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (k : ℕ),
    (k : K) ≠ 0 →
    ∀ x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, x ∈ tors P _ k →
      (∀ y : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, y ∈ tors P _ k →
        WeilIs P.A P.L (k : ℤ) x y 1) →
      x = 1
def WeilCharacters : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ),
    (N : K) ≠ 0 →
    ∀ χ : tors P (baseOver (Spec (CommRingCat.of K))) N →* Kˣ,
      ∃! b : tors P (baseOver (Spec (CommRingCat.of K))) N,
        ∀ x : tors P (baseOver (Spec (CommRingCat.of K))) N,
          WeilIs P.A P.L (N : ℤ) x.1 b.1 (unitSpec (χ x))
def WeilAll : Prop := WeilLaws ∧ WeilNondegenerate ∧ WeilCharacters
example {S : Scheme.{0}} (P : PolAV S) (T : Over S) (x : T ⟶ P.A) : x ∈ tors P T 0 := pow_zero x
example {S : Scheme.{0}} (P : PolAV S) (T : Over S) (x y : T ⟶ P.A) :
    x * y = lift x y ≫ μ[P.A] ∧ (1 : T ⟶ P.A) = toUnit T ≫ η[P.A] := ⟨rfl, rfl⟩
example {K : Type} [CommRing K] : Function.Injective (unitSpec (K := K)) :=
  Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.injective
end GlobalTheory.IndefiniteRowSideFullHecke.WeilPairingLaws


