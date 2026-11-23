-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:13.889797+00:00
-- url     : https://prove2.me/theorems/20d0c0bc-8e71-4712-9628-857a28ad42fb
-- title:
--   Unit Lemma Group
-- statement:
--   Definitions and structural lemmas for Unit Lemma Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnitLemmaGroup.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma
open Polynomial
section Orbits
variable (O : Type) [CommRing O] {A : Type} [CommRing A] [Algebra O A]
def mulLat (t : A) (L : Submodule O A) : Submodule O A := L.map (LinearMap.mulLeft O t)
def stabLat (L : Submodule O A) : Subgroup Aˣ where
  carrier := {t | ∀ y, y ∈ L ↔ (t : A) * y ∈ L}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro a b ha hb y
    rw [hb y, ha ((b : A) * y), Units.val_mul, mul_assoc]
  inv_mem' := by
    intro a ha y
    have := ha (((a⁻¹ : Aˣ) : A) * y)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm
def intUnits (A : Type) [CommRing A] [Algebra O A] : Subgroup Aˣ where
  carrier := {t | IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A)}
  one_mem' := by simpa using isIntegral_one
  mul_mem' := by
    intro a b ha hb
    refine ⟨by simpa using ha.1.mul hb.1, ?_⟩
    rw [mul_inv_rev, Units.val_mul]
    exact hb.2.mul ha.2
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, by simpa using ha.1⟩
def Orb (G : Subgroup Aˣ) (X : Set (Submodule O A)) : Type :=
  Quot fun L M : X => ∃ t ∈ G, (M : Submodule O A) = mulLat O (t : A) (L : Submodule O A)
def orbSum (G : Subgroup Aˣ) (X : Set (Submodule O A)) (w : Submodule O A → ℚ) : ℚ :=
  ∑ᶠ o : Orb O G X, w (Quot.out o).1 *
    (((stabLat O (Quot.out o).1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)
def IsLat (E : Type) [Field E] [Algebra E A] (L : Submodule O A) : Prop :=
  L.FG ∧ Submodule.span E (L : Set A) = ⊤
def countGL (E : Type) [Field E] [Algebra E A] (g : A) : ℚ :=
  orbSum O ⊤ {L | IsLat O E L ∧ ∀ y ∈ L, g * y ∈ L} fun _ => 1
end Orbits
def val (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E] (x : E) : ℤ :=
  -WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x)
structure UQ : Type 1 where
  O : Type
  E : Type
  [cO : CommRing O]
  [dO : IsDomain O]
  [dvr : IsDiscreteValuationRing O]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [fin : Finite (IsLocalRing.ResidueField O)]
  [fE : Field E]
  [aOE : Algebra O E]
  [frac : IsFractionRing O E]
  [c0 : CharZero E]
  c : E ≃+* E
  c_c : ∀ x, c (c x) = x
  c_int : ∀ x : O, ∃ y : O, c (algebraMap O E x) = algebraMap O E y
  c_res : ∃ x y : O, c (algebraMap O E x) = algebraMap O E y ∧ x - y ∉ IsLocalRing.maximalIdeal O
  q : ℕ
  card_res : Nat.card (IsLocalRing.ResidueField O) = q ^ 2
attribute [instance] UQ.cO UQ.dO UQ.dvr UQ.cpl UQ.fin UQ.fE UQ.aOE UQ.frac UQ.c0
def UQ.Odd (K : UQ) : Prop := IsUnit (2 : K.O)
def UQ.eta (K : UQ) (x : K.E) : ℚ := (-1 : ℚ) ^ val K.O x
structure InvAlg (K : UQ) : Type 1 where
  A : Type
  [cA : CommRing A]
  [aE : Algebra K.E A]
  [aO : Algebra K.O A]
  [tow : IsScalarTower K.O K.E A]
  [fd : Module.Finite K.E A]
  σ : A ≃+* A
  σ_σ : ∀ y, σ (σ y) = y
  σ_alg : ∀ e : K.E, σ (algebraMap K.E A e) = algebraMap K.E A (K.c e)
  g : A
attribute [instance] InvAlg.cA InvAlg.aE InvAlg.aO InvAlg.tow InvAlg.fd
namespace InvAlg
variable {K : UQ} (B : InvAlg K)
def P : K.E[X] := (LinearMap.mulLeft K.E B.g).charpoly
def prod (B₁ B₂ : InvAlg K) : InvAlg K where
  A := B₁.A × B₂.A
  σ := RingEquiv.prodCongr B₁.σ B₂.σ
  σ_σ := fun y => Prod.ext (B₁.σ_σ y.1) (B₂.σ_σ y.2)
  σ_alg := fun e => Prod.ext (B₁.σ_alg e) (B₂.σ_alg e)
  g := (B₁.g, B₂.g)
def herm (x y z : B.A) : K.E := Algebra.trace K.E B.A (x * y * B.σ z)
def X (x : B.A) : Set (Submodule K.O B.A) :=
  {L | IsLat K.O K.E L ∧ (∀ y ∈ L, B.g * y ∈ L) ∧
    ∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range}
def T : Subgroup B.Aˣ where
  carrier := {t | (t : B.A) * B.σ (t : B.A) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    calc (a : B.A) * b * (B.σ a * B.σ b) = ((a : B.A) * B.σ a) * ((b : B.A) * B.σ b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : B.σ (a : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    calc ((a⁻¹ : B.Aˣ) : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A)
        = ((a⁻¹ : B.Aˣ) : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * B.σ a) := by rw [ha, mul_one]
      _ = (((a⁻¹ : B.Aˣ) : B.A) * a) * (B.σ (a : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A)) := by ring
      _ = 1 := by rw [h1, Units.inv_mul, one_mul]
def N (x : B.A) : ℚ := orbSum K.O B.T (B.X x) fun _ => 1
def gramDet (x : B.A) : K.E :=
  (Matrix.of fun i j => B.herm x (Module.finBasis K.E B.A i) (Module.finBasis K.E B.A j)).det
def Cl : Type :=
  Quot fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} => ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))
def Cl.rep {B : InvAlg K} (k : B.Cl) : B.A := ((Quot.out k).1 : B.Aˣ)
def stSum : ℚ := ∑ᶠ k : B.Cl, B.N k.rep
def kapSum (B₁ B₂ : InvAlg K) : ℚ :=
  ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (Cl.rep k).1) * (B₁.prod B₂).N k.rep
def Identity (B₁ B₂ : InvAlg K) : Prop :=
  (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * kapSum B₁ B₂ = B₁.stSum * B₂.stSum
end InvAlg
def UnitLemmaGroup : Prop :=
  ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂
def UnitLemmaLie : Prop :=
  ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂
end GlobalTheory.UnitLemma


