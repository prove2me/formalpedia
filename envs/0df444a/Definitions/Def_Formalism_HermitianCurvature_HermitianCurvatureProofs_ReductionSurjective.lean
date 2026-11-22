-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:19:03.411836+00:00
-- url     : https://prove2.me/theorems/40600f95-123b-4226-8dba-d11c9a646bf8
-- title:
--   Reduction Surjective
-- statement:
--   Definitions and structural lemmas for Reduction Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
section Generic
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]
def IsUc (c : ι → ℕ) (x : Matrix ι ι A) : Prop :=
  ∀ i j, c j ≤ c i → x i j = (1 : Matrix ι ι A) i j
def IsLc (c : ι → ℕ) (x : Matrix ι ι A) : Prop := ∀ i j, c i ≠ c j → x i j = 0
variable {c : ι → ℕ} {x y : Matrix ι ι A}
theorem isUc_one : IsUc c (1 : Matrix ι ι A) := fun _ _ _ => rfl
theorem IsUc.mul (hx : IsUc c x) (hy : IsUc c y) : IsUc c (x * y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  have key : ∀ l ∈ Finset.univ, x i l * y l j = (1 : Matrix ι ι A) i l * y l j := by
    intro l _
    by_cases hl : c l ≤ c i
    · rw [hx i l hl]
    · have h1 : c j ≤ c l := by omega
      have hne : l ≠ j := by rintro rfl; omega
      rw [hy l j h1, Matrix.one_apply_ne hne, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl key, ← Matrix.mul_apply, Matrix.one_mul, hy i j hij]
theorem IsUc.blockTriangular (hx : IsUc c x) : BlockTriangular x c := by
  intro i j h
  have hne : i ≠ j := by rintro rfl; omega
  rw [hx i j h.le, Matrix.one_apply_ne hne]
theorem IsUc.det (hx : IsUc c x) : x.det = 1 := by
  rw [hx.blockTriangular.det]
  apply Finset.prod_eq_one
  intro a _
  have h1 : x.toSquareBlock c a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [Matrix.toSquareBlock_def, hx i j (by omega), Matrix.one_apply, Subtype.ext_iff]
  rw [h1, Matrix.det_one]
theorem IsUc.inv (hx : IsUc c x) : IsUc c x⁻¹ := by
  have hdet := hx.det
  let _ : Invertible x := Matrix.invertibleOfIsUnitDet x (by simp [hdet])
  have hT : BlockTriangular x⁻¹ c := Matrix.blockTriangular_inv_of_blockTriangular hx.blockTriangular
  intro i j hij
  have h1 : (x⁻¹ * x) i j = (1 : Matrix ι ι A) i j := by
    rw [Matrix.nonsing_inv_mul x (by simp [hdet])]
  rw [Matrix.mul_apply] at h1
  have key : ∀ l ∈ Finset.univ, x⁻¹ i l * x l j = x⁻¹ i l * (1 : Matrix ι ι A) l j := by
    intro l _
    by_cases hl : c j ≤ c l
    · rw [hx l j hl]
    · have h2 : c l < c i := by omega
      rw [hT h2, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl key, ← Matrix.mul_apply, Matrix.mul_one] at h1
  exact h1
theorem IsUc.conj {l l' n : Matrix ι ι A} (hl : IsLc c l) (hl' : IsLc c l') (h : l * l' = 1)
    (hn : IsUc c n) : IsUc c (l * n * l') := by
  intro i j hij
  have key : (l * (n - 1) * l') i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : c b = c j
    · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
      intro a _
      by_cases ha : c i = c a
      · rw [Matrix.sub_apply, hn a b (by omega), sub_self, mul_zero]
      · rw [hl i a ha, zero_mul]
    · rw [hl' b j hb, mul_zero]
  have h2 : l * n * l' = l * (n - 1) * l' + 1 := by
    rw [mul_sub, sub_mul, mul_one, h]; abel
  rw [h2, Matrix.add_apply, key, zero_add]
theorem IsUc.map {B : Type} [CommRing B] (f : A →+* B) (hx : IsUc c x) : IsUc c (x.map f) := by
  intro i j hij
  rw [Matrix.map_apply, hx i j hij]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]
variable (A) (c) in

def UcG : Subgroup (GL ι A) where
  carrier := {g | IsUc c (g : Matrix ι ι A)}
  one_mem' := by simpa using isUc_one
  mul_mem' := by intro a b ha hb; simpa using IsUc.mul ha hb
  inv_mem' := by intro a ha; simpa [Matrix.coe_units_inv] using IsUc.inv ha
noncomputable def toGL (x : Matrix ι ι A) (h : IsUnit x.det) : GL ι A := Matrix.nonsingInvUnit x h
@[simp] theorem coe_toGL (x : Matrix ι ι A) (h : IsUnit x.det) : (toGL x h : Matrix ι ι A) = x := rfl
end Generic
section Prod
variable {G : Type} [Group G]
def prodG (N H : Subgroup G) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) : Subgroup G where
  carrier := {g | ∃ n ∈ N, ∃ h ∈ H, g = n * h}
  one_mem' := ⟨1, N.one_mem, 1, H.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨n, hn, h, hh, rfl⟩ ⟨n', hn', h', hh', rfl⟩
    exact ⟨n * (h * n' * h⁻¹), N.mul_mem hn (hnorm h hh n' hn'), h * h', H.mul_mem hh hh', by group⟩
  inv_mem' := by
    rintro _ ⟨n, hn, h, hh, rfl⟩
    exact ⟨h⁻¹ * n⁻¹ * (h⁻¹)⁻¹, hnorm _ (H.inv_mem hh) _ (N.inv_mem hn), h⁻¹, H.inv_mem hh, by group⟩
end Prod
section Specific
variable {A : Type} [CommRing A] {r k : ℕ}
def cI (r k : ℕ) : Idx r k → ℕ
  | Sum.inl a => a
  | Sum.inr (Sum.inl _) => r
  | Sum.inr (Sum.inr a) => r + 1 + a
theorem hEmb_mul (h h' : Matrix (Fin k) (Fin k) A) : hEmb r (h * h') = hEmb r h * hEmb r h' := by
  simp [hEmb, midEmb, Matrix.fromBlocks_multiply]
theorem hEmb_one : hEmb r (1 : Matrix (Fin k) (Fin k) A) = 1 := by
  simp [hEmb, midEmb]
theorem isLc_hEmb (h : Matrix (Fin k) (Fin k) A) : IsLc (cI r k) (hEmb r h) := by
  rintro (a | a | a) (b | b | b) hij
  · have hne : a ≠ b := by rintro rfl; exact hij rfl
    simp [hEmb, hne]
  · simp [hEmb]
  · simp [hEmb]
  · simp [hEmb]
  · exact absurd rfl hij
  · simp [hEmb]
  · simp [hEmb]
  · simp [hEmb]
  · have hne : a ≠ b := by rintro rfl; exact hij rfl
    simp [hEmb, hne]
variable (A r k) in

def hEmbHom : Matrix (Fin k) (Fin k) A →* Matrix (Idx r k) (Idx r k) A where
  toFun := hEmb r
  map_one' := hEmb_one
  map_mul' := hEmb_mul
variable (A r k) in

def phi : GL (Fin k) A →* GL (Idx r k) A := Units.map (hEmbHom A r k)
theorem norm_phi (V : Subgroup (GL (Fin k) A)) :
    ∀ h ∈ V.map (phi A r k), ∀ n ∈ UcG A (cI r k), h * n * h⁻¹ ∈ UcG A (cI r k) := by
  rintro _ ⟨h, -, rfl⟩ n hn
  rw [← map_inv]
  change IsUc (cI r k) (hEmb r (h : Matrix (Fin k) (Fin k) A) * (n : Matrix _ _ A) *
    hEmb r ((h⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A))
  refine IsUc.conj (isLc_hEmb _) (isLc_hEmb _) ?_ hn
  rw [← hEmb_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, hEmb_one]
variable (r) in

def PG (V : Subgroup (GL (Fin k) A)) : Subgroup (GL (Idx r k) A) :=
  prodG (UcG A (cI r k)) (V.map (phi A r k)) (norm_phi V)
end Specific
section Local
variable (o : Type) [CommRing o] [IsLocalRing o]
local notation "𝔽" => IsLocalRing.ResidueField o
variable {o} {r k : ℕ}
end Local
end Formalism.FourierDecayAlt.P.S3x2
namespace Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2
end Formalism.FourierDecayAlt.P


