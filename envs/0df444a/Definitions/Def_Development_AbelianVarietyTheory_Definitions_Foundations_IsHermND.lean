-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:09.686893+00:00
-- url     : https://prove2.me/theorems/7e959ecf-d00a-4c68-8b29-df85e67302c7
-- title:
--   Is Herm ND
-- statement:
--   Definitions and structural lemmas for Is Herm ND, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHermND.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise
namespace GlobalTheory.HL
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
def hf (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ i, ∑ j, x i * Hm i j * L.cj (y j)
def cT (L : LocE F E) {m n : Type} (A : Matrix m n E) : Matrix n m E := fun i j => L.cj (A j i)
def IsHerm (L : LocE F E) {m : Type} (A : Matrix m m E) : Prop := cT L A = A
def IsHermND (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) : Prop :=
  IsHerm L Hm ∧ IsUnit Hm.det
def IsIntM (L : LocE F E) {m n : Type} (A : Matrix m n E) : Prop := ∀ i j, A i j ∈ L.O
def perp (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Y : Submodule E (Fin n → E)) :
    Submodule E (Fin n → E) where
  carrier := {x | ∀ y ∈ Y, hf L Hm x y = 0}
  zero_mem' := by intro y _; simp [hf]
  add_mem' := by
    intro a b ha hb y hy
    have h : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
      simp [hf, add_mul, Finset.sum_add_distrib]
    rw [h, ha y hy, hb y hy, add_zero]
  smul_mem' := by
    intro c a ha y hy
    have h : hf L Hm (c • a) y = c * hf L Hm a y := by
      simp [hf, Finset.mul_sum, mul_assoc]
    rw [h, ha y hy, mul_zero]
def IsLat (L : LocE F E) {n : ℕ} (Λ : Submodule L.O (Fin n → E)) : Prop :=
  Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤
def IsSD (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (Λ : Submodule L.O (Fin n → E)) : Prop :=
  IsLat L Λ ∧ ∀ y, (∀ x ∈ Λ, hf L Hm x y ∈ L.O) ↔ y ∈ Λ
def isomG (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) :
    Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | ∀ x y, hf L Hm (g x) (g y) = hf L Hm x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    exact (ha (b x) (b y)).trans (hb x y)
  inv_mem' := by
    intro a ha x y
    have h := ha (a.symm x) (a.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm
def unipOn {n : ℕ} (A B : Submodule E (Fin n → E)) : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)) where
  carrier := {g | (∀ v, g v ∈ A ↔ v ∈ A) ∧ ∀ v ∈ A, g v - v ∈ B}
  one_mem' := ⟨fun _ => Iff.rfl, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun v => (ha (b v)).trans (hb v), fun v hv => ?_⟩
    have h : (a * b) v - v = (a (b v) - b v) + (b v - v) := by simp
    rw [h]
    exact B.add_mem (ha' _ ((hb v).2 hv)) (hb' v hv)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ∀ v, a.symm v ∈ A ↔ v ∈ A := fun v => by
      have := ha (a.symm v)
      simp only [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    refine ⟨h1, fun v hv => ?_⟩
    have h2 := ha' _ ((h1 v).2 hv)
    simp only [LinearEquiv.apply_symm_apply] at h2
    have h3 : a⁻¹ v - v = -(v - a.symm v) := by
      rw [neg_sub]; rfl
    rw [h3]
    exact B.neg_mem h2
def eich (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x u : Fin n → E) (s : E)
    (v : Fin n → E) : Fin n → E :=
  v + hf L Hm v u • x - hf L Hm v x • (u + s • x)
def invVol {G : Type*} [Group G] (K0 K : Subgroup G) : ℝ :=
  (K.relIndex K0 : ℝ) / (K0.relIndex K : ℝ)
def resQ (ϖ : 𝒪[F]) : ℕ := Nat.card (𝒪[F] ⧸ Ideal.span {ϖ})
def vE (L : LocE F E) (ϖ : 𝒪[F]) (c : E) : ℤ :=
  sSup {m : ℤ | ∃ y ∈ L.O, c = algebraMap F E ((ϖ : F) ^ m) * y}
def lead {N : ℕ} (Z : Matrix (Fin N) (Fin N) E) (l : Fin (N + 1)) : E :=
  (Z.submatrix (Fin.castLE (Nat.lt_succ_iff.mp l.2)) (Fin.castLE (Nat.lt_succ_iff.mp l.2))).det
end GlobalTheory.HL


