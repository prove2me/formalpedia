-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:38.283924+00:00
-- url     : https://prove2.me/theorems/59235323-15ed-4189-9ba5-76874c5c4407
-- title:
--   Herm Lat
-- statement:
--   Definitions and structural lemmas for Herm Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/HermLat.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL
def GoodSub {W : Type} [AddCommGroup W] (W0 A : AddSubgroup W) (S : Set W) : Prop :=
  A.relIndex W0 ≠ 0 ∧ W0.relIndex A ≠ 0 ∧ (∀ x ∈ S, ∀ a ∈ A, x + a ∈ S) ∧
    ((QuotientAddGroup.mk : W → W ⧸ A) '' S).Finite
def IsCO {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : Prop := ∃ A, GoodSub W0 A S
def relVol {W : Type} [AddCommGroup W] (W0 A : AddSubgroup W) : ℝ :=
  (W0.relIndex A : ℝ) / (A.relIndex W0 : ℝ)
def cont {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W) : ℝ :=
  if h : IsCO W0 S then
    (((QuotientAddGroup.mk : W → W ⧸ h.choose) '' S).ncard : ℝ) * relVol W0 h.choose else 0
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
def gramT (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) :
    Matrix (Fin m) (Fin m) E := Matrix.of fun a b => hf L Hm (x b) (x a)
def rmul {n m : ℕ} (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) : Fin m → Fin n → E :=
  fun j => ∑ i, A i j • x i
def IsUni {N : ℕ} (s : Matrix (Fin N) (Fin N) E) : Prop := (∀ i j, j < i → s i j = 0) ∧ ∀ i, s i i = 1
def congK (L : LocE F E) (ϖ : 𝒪[F]) (m i : ℕ) : Set (Matrix (Fin m) (Fin m) E) :=
  {A | ∀ a b, ∃ c ∈ L.O, A a b - (1 : Matrix (Fin m) (Fin m) E) a b = algebraMap F E ((ϖ : F) ^ i) * c}
def thick (L : LocE F E) (ϖ : 𝒪[F]) {n m : ℕ} (Ω : Set (Fin m → Fin n → E)) (i : ℕ) :
    Set (Fin m → Fin n → E) := {x | ∃ y ∈ Ω, ∃ A ∈ congK L ϖ m i, x = rmul y A}
def horb (L : LocE F E) (ϖ : 𝒪[F]) {m : ℕ} (Γ : Matrix (Fin m) (Fin m) E) (i : ℕ) :
    Set (Matrix (Fin m) (Fin m) E) := {X | ∃ A ∈ congK L ϖ m i, X = cT L A * Γ * A}
def tupLat (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (m : ℕ) :
    AddSubgroup (Fin m → Fin n → E) := AddSubgroup.pi Set.univ fun _ => Λ.toAddSubgroup
def hermLat (L : LocE F E) (m : ℕ) : AddSubgroup (Matrix (Fin m) (Fin m) E) :=
  AddSubgroup.closure {X | IsHerm L X ∧ IsIntM L X}
def IsPrimT (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Λ : Submodule L.O (Fin n → E))
    (x : Fin m → Fin n → E) : Prop :=
  (∀ a, x a ∈ Λ) ∧ ∃ y : Fin m → Fin n → E, (∀ a, y a ∈ Λ) ∧
    ∀ a b, hf L Hm (x a) (y b) = if a = b then 1 else 0
def fixG (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E)) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) := isomG L Hm ⊓ unipOn Y ⊥
abbrev stabL (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) := MulAction.stabilizer ((Fin n → E) ≃ₗ[E] (Fin n → E)) Λ
def torb {n m : ℕ} (K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E))) (x : Fin m → Fin n → E) :
    Set (Fin m → Fin n → E) := {y | ∃ g ∈ K, y = fun a => g (x a)}
def CongId (L : LocE F E) (ϖ : 𝒪[F]) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (N : ℕ)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = algebraMap F E ((ϖ : F) ^ N) • w
def sigMass (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E))
    (Λ0 Mh : Submodule L.O (Fin n → E)) : ℝ≥0∞ :=
  ∑' o : MulAction.orbitRel.Quotient (fixG L Hm Y) (Submodule L.O (Fin n → E)),
    if IsSD L Hm o.out ∧ o.out ⊓ Y.restrictScalars L.O = Mh then
      ENNReal.ofReal (invVol (fixG L Hm Y ⊓ stabL L Λ0) (fixG L Hm Y ⊓ stabL L o.out)) else 0
def primCnt (L : LocE F E) (ϖ : 𝒪[F]) (n : ℕ) {m : ℕ} (j : ℕ) (Gm : Matrix (Fin m) (Fin m) E) : ℕ :=
  Set.ncard {C : Set (Fin m → Fin n → E) | ∃ x : Fin m → Fin n → E, (∀ a i, x a i ∈ L.O) ∧
    (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧ ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧
    (∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - Gm a b = algebraMap F E ((ϖ : F) ^ j) * c) ∧
    C = {y | ∀ a i, ∃ c ∈ L.O, y a i - x a i = algebraMap F E ((ϖ : F) ^ j) * c}}
def IsQRefl (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a : Fin n → E)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : Prop :=
  IsUnit (hf L Hm a a) ∧ g ∈ isomG L Hm ∧ ∃ c : E, ∀ v, g v = v + (c * hf L Hm v a) • a
end GlobalTheory.HL


