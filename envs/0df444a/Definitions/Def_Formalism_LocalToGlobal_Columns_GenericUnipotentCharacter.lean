-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
-- name    : Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:20.460399+00:00
-- url     : https://prove2.me/theorems/b44dae7a-2018-47a5-a99b-07ce4ebf0a09
-- title:
--   Generic Unipotent Character
-- statement:
--   Definitions and structural lemmas for Generic Unipotent Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GenericUnipotentCharacter.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
namespace Formalism.L2.Col
def blkIdx : List ℕ → ℕ → ℕ
  | [], _ => 0
  | b :: bs, i => if i < b then 0 else blkIdx bs (i - b) + 1
def coarse (a : ℕ) (bl : List ℕ) (i : ℕ) : ℕ := blkIdx (a :: bl) i
def fine (a : ℕ) (bl : List ℕ) (i : ℕ) : ℕ := if i < a then i else a + blkIdx bl (i - a)
theorem coarse_of_lt {a : ℕ} {bl : List ℕ} {i : ℕ} (h : i < a) : coarse a bl i = 0 := by
  simp [coarse, blkIdx, h]
theorem coarse_of_le {a : ℕ} {bl : List ℕ} {i : ℕ} (h : a ≤ i) : coarse a bl i = blkIdx bl (i - a) + 1 := by
  simp [coarse, blkIdx, Nat.not_lt.mpr h]
theorem coarse_eq_zero {a : ℕ} {bl : List ℕ} {i : ℕ} : coarse a bl i = 0 ↔ i < a := by
  constructor
  · intro h
    by_contra h'
    rw [coarse_of_le (Nat.not_lt.mp h')] at h
    omega
  · exact coarse_of_lt
theorem fine_lt_right {a : ℕ} {bl : List ℕ} {i l : ℕ} (hi : i < a) : fine a bl l < fine a bl i ↔ l < i := by
  unfold fine
  rw [if_pos hi]
  split_ifs <;> omega
theorem fine_lt_left {a : ℕ} {bl : List ℕ} {j l : ℕ} (hj : j < a) : fine a bl j < fine a bl l ↔ j < l := by
  unfold fine
  rw [if_pos hj]
  split_ifs <;> omega
theorem fine_lt_of_coarse_lt {a : ℕ} {bl : List ℕ} {i j : ℕ} (h : coarse a bl j < coarse a bl i) :
    fine a bl j < fine a bl i := by
  have hi : a ≤ i := by
    by_contra h'
    rw [coarse_of_lt (Nat.not_le.mp h')] at h
    omega
  rw [coarse_of_le hi] at h
  by_cases hj : j < a
  · rw [fine_lt_left hj]; omega
  · rw [coarse_of_le (Nat.not_lt.mp hj)] at h
    unfold fine
    rw [if_neg hj, if_neg (Nat.not_lt.mpr hi)]
    omega
section Groups
variable {n : ℕ} {κ : Type} [CommRing κ]
def btG (n : ℕ) (κ : Type) [CommRing κ] (β : ℕ → ℕ) : Subgroup (GL (Fin n) κ) where
  carrier := {M | (M : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => β i.val)}
  one_mem' := by
    show ((1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular _
    rw [Units.val_one]
    exact Matrix.blockTriangular_one
  mul_mem' := fun {a b} ha hb => by
    show ((a * b : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular _
    rw [Units.val_mul]
    exact Matrix.BlockTriangular.mul ha hb
  inv_mem' := fun {a} ha => by
    show ((a⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular _
    have : Invertible (a : Matrix (Fin n) (Fin n) κ) := a.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular ha
theorem toSquareBlock_mul {A B : Matrix (Fin n) (Fin n) κ} {b : Fin n → ℕ} (hA : A.BlockTriangular b)
    (hB : B.BlockTriangular b) (c : ℕ) :
    (A * B).toSquareBlock b c = A.toSquareBlock b c * B.toSquareBlock b c := by
  ext i j
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun l => b l = c)) (by simp) (fun l => A i l * B l j)]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro l _ hl
  have hl' : b l ≠ c := by simpa using hl
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hA (by rw [i.2]; exact h), zero_mul]
  · rw [hB (by rw [j.2]; exact h), mul_zero]
def blkHom (n : ℕ) (κ : Type) [CommRing κ] (β : ℕ → ℕ) (c : ℕ) :
    ↥(btG n κ β) →* Matrix {i : Fin n // β i.val = c} {i : Fin n // β i.val = c} κ where
  toFun M := (M.1 : Matrix (Fin n) (Fin n) κ).toSquareBlock (fun i => β i.val) c
  map_one' := by
    ext i j
    simp [Matrix.toSquareBlock_def, Matrix.one_apply, Subtype.ext_iff]
  map_mul' M N := by
    show ((M.1 * N.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).toSquareBlock _ c = _
    rw [Units.val_mul]
    exact toSquareBlock_mul M.2 N.2 c
def blkDet (n : ℕ) (κ : Type) [CommRing κ] (β : ℕ → ℕ) (c : ℕ) : ↥(btG n κ β) →* κˣ :=
  (Matrix.detMonoidHom.comp (blkHom n κ β c)).toHomUnits
theorem blkHom_apply {β : ℕ → ℕ} (c : ℕ) (M : ↥(btG n κ β)) (i j : {i : Fin n // β i.val = c}) :
    blkHom n κ β c M i j = (M.1 : Matrix (Fin n) (Fin n) κ) i.1 j.1 := rfl
abbrev blockUT (n : ℕ) (κ : Type) [CommRing κ] (a : ℕ) (bl : List ℕ) : Subgroup (GL (Fin n) κ) := btG n κ (coarse a bl)
theorem fine_diag_mul {a : ℕ} {bl : List ℕ} {A B : Matrix (Fin n) (Fin n) κ}
    (hA : A.BlockTriangular (fun i : Fin n => fine a bl i.val)) (hB : B.BlockTriangular (fun i : Fin n => fine a bl i.val))
    (i : Fin n) (hi : i.val < a) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro l _ hl
    have hl' : l.val ≠ i.val := fun h => hl (Fin.ext h)
    rcases lt_or_gt_of_ne hl' with h | h
    · rw [hA ((fine_lt_right hi).mpr h), zero_mul]
    · rw [hB ((fine_lt_left hi).mpr h), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
def uniUT (n : ℕ) (κ : Type) [CommRing κ] (a : ℕ) (bl : List ℕ) : Subgroup (GL (Fin n) κ) where
  carrier := {M | M ∈ btG n κ (fine a bl) ∧ ∀ i : Fin n, i.val < a → (M : Matrix (Fin n) (Fin n) κ) i i = 1}
  one_mem' := ⟨Subgroup.one_mem _, fun i _ => by simp⟩
  mul_mem' := fun {A B} hA hB => ⟨Subgroup.mul_mem _ hA.1 hB.1, fun i hi => by
    rw [Units.val_mul, fine_diag_mul hA.1 hB.1 i hi, hA.2 i hi, hB.2 i hi, one_mul]⟩
  inv_mem' := fun {A} hA => ⟨Subgroup.inv_mem _ hA.1, fun i hi => by
    have h1 := fine_diag_mul hA.1 (Subgroup.inv_mem _ hA.1) i hi
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq, hA.2 i hi, one_mul] at h1
    exact h1.symm⟩
theorem mem_uniUT {a : ℕ} {bl : List ℕ} {M : GL (Fin n) κ} :
    M ∈ uniUT n κ a bl ↔ M ∈ blockUT n κ a bl ∧
      (∀ i j : Fin n, i.val < a → j.val < i.val → (M : Matrix (Fin n) (Fin n) κ) i j = 0) ∧
      ∀ i : Fin n, i.val < a → (M : Matrix (Fin n) (Fin n) κ) i i = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j hij => h1 (fine_lt_of_coarse_lt hij), fun i j hi hji => h1 ((fine_lt_right hi).mpr hji), h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i j hij => ?_, h3⟩
    by_cases hi : i.val < a
    · exact h2 i j hi ((fine_lt_right hi).mp hij)
    · apply h1
      show coarse a bl j.val < coarse a bl i.val
      rw [coarse_of_le (Nat.not_lt.mp hi)]
      by_cases hj : j.val < a
      · rw [coarse_of_lt hj]; omega
      · rw [coarse_of_le (Nat.not_lt.mp hj)]
        have : fine a bl j.val < fine a bl i.val := hij
        unfold fine at this
        rw [if_neg hi, if_neg hj] at this
        omega
theorem uniUT_le_blockUT (n : ℕ) (κ : Type) [CommRing κ] (a : ℕ) (bl : List ℕ) : uniUT n κ a bl ≤ blockUT n κ a bl :=
  fun _ h => (mem_uniUT.mp h).1
def supSum (a : ℕ) (S : Finset ℕ) (M : Matrix (Fin n) (Fin n) κ) : κ :=
  ∑ i : Fin n, ∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < a ∧ i.val ∈ S then M i j else 0
theorem sup_mul {a : ℕ} {bl : List ℕ} {A B : GL (Fin n) κ} (hA : A ∈ uniUT n κ a bl) (hB : B ∈ uniUT n κ a bl)
    (i j : Fin n) (hij : i.val + 1 = j.val) (hj : j.val < a) :
    ((A * B : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j =
      (A : Matrix (Fin n) (Fin n) κ) i j + (B : Matrix (Fin n) (Fin n) κ) i j := by
  have hi : i.val < a := by omega
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add i j hne, hA.2 i hi, hB.2 j hj, one_mul, mul_one, add_comm]
  · rintro l _ ⟨h1, h2⟩
    have h1' : l.val ≠ i.val := fun h => h1 (Fin.ext h)
    have h2' : l.val ≠ j.val := fun h => h2 (Fin.ext h)
    by_cases h : l.val < i.val
    · rw [hA.1 ((fine_lt_right hi).mpr h), zero_mul]
    · rw [hB.1 ((fine_lt_left hj).mpr (by omega)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
  · intro h; exact absurd (Finset.mem_univ j) h
def supHom (n : ℕ) (κ : Type) [CommRing κ] (a : ℕ) (bl : List ℕ) (S : Finset ℕ) : ↥(uniUT n κ a bl) →* Multiplicative κ where
  toFun M := Multiplicative.ofAdd (supSum a S (M.1 : Matrix (Fin n) (Fin n) κ))
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    unfold supSum
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with h
    · have hne : i ≠ j := fun h' => by rw [h'] at h; omega
      simp [Matrix.one_apply_ne hne]
    · rfl
  map_mul' A B := by
    rw [← ofAdd_add]
    congr 1
    unfold supSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    split_ifs with h
    · exact sup_mul A.2 B.2 i j h.1 h.2.1
    · simp
variable {K : Type} [Field K]
def supChar (ψ : AddChar κ K) (n a : ℕ) (bl : List ℕ) (S : Finset ℕ) : ↥(uniUT n κ a bl) →* Kˣ :=
  ψ.toMonoidHom.toHomUnits.comp (supHom n κ a bl S)
def detChar (χ : ℕ → κˣ →* Kˣ) (n a : ℕ) (bl : List ℕ) : ↥(blockUT n κ a bl) →* Kˣ :=
  ∏ s ∈ Finset.range bl.length, (χ s).comp (blkDet n κ (coarse a bl) (s + 1))
def lamGen (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n a : ℕ) (bl : List ℕ) (S : Finset ℕ) : ↥(uniUT n κ a bl) →* Kˣ :=
  supChar ψ n a bl S * (detChar χ n a bl).comp (Subgroup.inclusion (uniUT_le_blockUT n κ a bl))
def extChi {m : ℕ} (χ : Fin m → κˣ →* Kˣ) (s : ℕ) : κˣ →* Kˣ := if h : s < m then χ ⟨s, h⟩ else 1
def diagMat (r n : ℕ) (g : Matrix (Fin r) (Fin r) κ) : Matrix (Fin n) (Fin n) κ :=
  fun i j => if h : i.val < r ∧ j.val < r then g ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else (1 : Matrix (Fin n) (Fin n) κ) i j
theorem diagMat_of_lt {r : ℕ} (g : Matrix (Fin r) (Fin r) κ) {i j : Fin n} (hi : i.val < r) (hj : j.val < r) :
    diagMat r n g i j = g ⟨i.val, hi⟩ ⟨j.val, hj⟩ := dif_pos ⟨hi, hj⟩
theorem diagMat_of_not_left {r : ℕ} (g : Matrix (Fin r) (Fin r) κ) {i : Fin n} (j : Fin n) (hi : ¬ i.val < r) :
    diagMat r n g i j = (1 : Matrix (Fin n) (Fin n) κ) i j := dif_neg fun h => hi h.1
theorem diagMat_of_not_right {r : ℕ} (g : Matrix (Fin r) (Fin r) κ) (i : Fin n) {j : Fin n} (hj : ¬ j.val < r) :
    diagMat r n g i j = (1 : Matrix (Fin n) (Fin n) κ) i j := dif_neg fun h => hj h.2
theorem diagMat_one (r : ℕ) : diagMat r n (1 : Matrix (Fin r) (Fin r) κ) = 1 := by
  ext i j
  unfold diagMat
  split_ifs with h
  · simp [Matrix.one_apply, Fin.ext_iff]
  · rfl
theorem diagMat_mul {r : ℕ} (h : r ≤ n) (g g' : Matrix (Fin r) (Fin r) κ) :
    diagMat r n (g * g') = diagMat r n g * diagMat r n g' := by
  ext i j
  by_cases hi : i.val < r
  · by_cases hj : j.val < r
    · rw [diagMat_of_lt _ hi hj, Matrix.mul_apply, Matrix.mul_apply]
      apply Finset.sum_of_injOn (Fin.castLE h) (fun a _ b _ hab => Fin.castLE_injective h hab) (by simp [Set.MapsTo])
      · intro l _ hl
        have hl' : ¬ l.val < r := fun hlt => hl ⟨⟨l.val, hlt⟩, by simp, Fin.ext rfl⟩
        rw [diagMat_of_not_right _ _ hl', Matrix.one_apply_ne (fun e => hl' (by rw [← e]; exact hi)), zero_mul]
      · intro l _
        rw [diagMat_of_lt g hi (show (Fin.castLE h l).val < r from l.2),
          diagMat_of_lt g' (show (Fin.castLE h l).val < r from l.2) hj]
        rfl
    · rw [diagMat_of_not_right _ _ hj]
      rw [Matrix.mul_apply]
      simp_rw [diagMat_of_not_right g' _ hj]
      rw [← Matrix.mul_apply, Matrix.mul_one, diagMat_of_not_right _ _ hj]
  · rw [diagMat_of_not_left _ _ hi, Matrix.mul_apply]
    simp_rw [diagMat_of_not_left g _ hi]
    rw [← Matrix.mul_apply, Matrix.one_mul, diagMat_of_not_left _ _ hi]
def diagEmb (κ : Type) [CommRing κ] {r n : ℕ} (h : r ≤ n) : GL (Fin r) κ →* GL (Fin n) κ :=
  Units.map ({ toFun := diagMat r n, map_one' := diagMat_one r, map_mul' := diagMat_mul h } :
    Matrix (Fin r) (Fin r) κ →* Matrix (Fin n) (Fin n) κ)
def fixCol (n : ℕ) (κ : Type) [CommRing κ] (c : ℕ) : Subgroup (GL (Fin n) κ) where
  carrier := {M | ∀ i j : Fin n, j.val = c → (M : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j}
  one_mem' := fun _ _ _ => by rw [Units.val_one]
  mul_mem' := fun {A B} hA hB i j hj => by
    rw [Units.val_mul, Matrix.mul_apply]
    simp_rw [hB _ j hj]
    rw [← Matrix.mul_apply, Matrix.mul_one, hA i j hj]
  inv_mem' := fun {A} hA i j hj => by
    have h1 : ((A⁻¹ * A : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j := by
      rw [inv_mul_cancel, Units.val_one]
    rw [Units.val_mul, Matrix.mul_apply] at h1
    simp_rw [hA _ j hj] at h1
    rwa [← Matrix.mul_apply, Matrix.mul_one] at h1
def HK (n : ℕ) (κ : Type) [CommRing κ] (r : ℕ) (bl : List ℕ) : Subgroup (GL (Fin n) κ) :=
  (blkHom n κ (coarse r bl) 0).ker.map (blockUT n κ r bl).subtype
theorem mem_HK {r : ℕ} {bl : List ℕ} {M : GL (Fin n) κ} :
    M ∈ HK n κ r bl ↔ M ∈ blockUT n κ r bl ∧
      ∀ i j : Fin n, i.val < r → j.val < r → (M : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j := by
  constructor
  · rintro ⟨⟨M, hM⟩, hk, rfl⟩
    refine ⟨hM, fun i j hi hj => ?_⟩
    have h1 := congrArg (fun X : Matrix {i : Fin n // coarse r bl i.val = 0} {i : Fin n // coarse r bl i.val = 0} κ =>
      X ⟨i, coarse_of_lt hi⟩ ⟨j, coarse_of_lt hj⟩) (MonoidHom.mem_ker.mp hk)
    show (M : Matrix (Fin n) (Fin n) κ) i j = _
    simpa only [blkHom_apply, Matrix.one_apply, Subtype.mk.injEq] using h1
  · rintro ⟨hM, h⟩
    refine ⟨⟨M, hM⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext i j
    have h1 := h i.1 j.1 (coarse_eq_zero.mp i.2) (coarse_eq_zero.mp j.2)
    rw [blkHom_apply, h1]
    simp only [Matrix.one_apply, Subtype.ext_iff]
theorem HK_le_blockUT (n : ℕ) (κ : Type) [CommRing κ] (r : ℕ) (bl : List ℕ) : HK n κ r bl ≤ blockUT n κ r bl :=
  fun _ h => (mem_HK.mp h).1
def lamK (χ : ℕ → κˣ →* Kˣ) (n r : ℕ) (bl : List ℕ) : ↥(HK n κ r bl) →* Kˣ :=
  (detChar χ n r bl).comp (Subgroup.inclusion (HK_le_blockUT n κ r bl))
def restr {r : ℕ} (h : r ≤ n) (A : Matrix (Fin n) (Fin n) κ) : Matrix (Fin r) (Fin r) κ :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)
theorem restr_one {r : ℕ} (h : r ≤ n) : restr h (1 : Matrix (Fin n) (Fin n) κ) = 1 :=
  Matrix.submatrix_one _ (Fin.castLE_injective h)
theorem restr_mul {r : ℕ} (h : r ≤ n) (bl : List ℕ) (A : Matrix (Fin n) (Fin n) κ) {B : Matrix (Fin n) (Fin n) κ}
    (hB : B.BlockTriangular (fun i => coarse r bl i.val)) : restr h (A * B) = restr h A * restr h B := by
  ext i j
  simp only [restr, Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  apply Finset.sum_of_injOn (Fin.castLE h) (fun x _ y _ hxy => Fin.castLE_injective h hxy) (by simp [Set.MapsTo])
  · intro l _ hl
    have hl' : ¬ l.val < r := fun hlt => hl ⟨⟨l.val, hlt⟩, by simp, Fin.ext rfl⟩
    have hc : coarse r bl (Fin.castLE h j).val < coarse r bl l.val := by
      rw [coarse_of_lt (show (Fin.castLE h j).val < r from j.2), coarse_of_le (Nat.not_lt.mp hl')]
      omega
    rw [hB hc, mul_zero]
  · intro l _
    rfl
def blk0 (n : ℕ) (κ : Type) [CommRing κ] {r : ℕ} (h : r ≤ n) (bl : List ℕ) : ↥(blockUT n κ r bl) →* GL (Fin r) κ where
  toFun M := ⟨restr h (M.1 : Matrix (Fin n) (Fin n) κ), restr h ((M.1⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ),
    by rw [← restr_mul h bl _ (Subgroup.inv_mem _ M.2), ← Units.val_mul, mul_inv_cancel, Units.val_one, restr_one],
    by rw [← restr_mul h bl _ M.2, ← Units.val_mul, inv_mul_cancel, Units.val_one, restr_one]⟩
  map_one' := by
    apply Units.ext
    show restr h ((1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = 1
    rw [Units.val_one, restr_one]
  map_mul' M N := by
    apply Units.ext
    show restr h ((M.1 * N.1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) =
      restr h (M.1 : Matrix (Fin n) (Fin n) κ) * restr h (N.1 : Matrix (Fin n) (Fin n) κ)
    rw [Units.val_mul, restr_mul h bl _ N.2]
def HPar (n : ℕ) (κ : Type) [CommRing κ] {r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) :
    Subgroup (GL (Fin n) κ) :=
  (H₀.comap (blk0 n κ h bl)).map (blockUT n κ r bl).subtype
theorem mem_HPar {r : ℕ} {h : r ≤ n} {bl : List ℕ} {H₀ : Subgroup (GL (Fin r) κ)} {M : GL (Fin n) κ} :
    M ∈ HPar n κ h bl H₀ ↔ ∃ hM : M ∈ blockUT n κ r bl, blk0 n κ h bl ⟨M, hM⟩ ∈ H₀ := by
  constructor
  · rintro ⟨M', hM', rfl⟩
    exact ⟨M'.2, hM'⟩
  · rintro ⟨hM, h0⟩
    exact ⟨⟨M, hM⟩, h0, rfl⟩
theorem HPar_le {r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) : HPar n κ h bl H₀ ≤ blockUT n κ r bl :=
  fun _ hM => (mem_HPar.mp hM).1
def HPar0 {r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) : ↥(HPar n κ h bl H₀) →* ↥H₀ :=
  ((blk0 n κ h bl).comp (Subgroup.inclusion (HPar_le h bl H₀))).codRestrict H₀ fun M => by
    obtain ⟨_, h0⟩ := mem_HPar.mp M.2
    exact h0
def lamPar {r : ℕ} (h : r ≤ n) (bl : List ℕ) {H₀ : Subgroup (GL (Fin r) κ)} (lam₀ : ↥H₀ →* Kˣ) (χ : ℕ → κˣ →* Kˣ) :
    ↥(HPar n κ h bl H₀) →* Kˣ :=
  lam₀.comp (HPar0 h bl H₀) * (detChar χ n r bl).comp (Subgroup.inclusion (HPar_le h bl H₀))
end Groups
section Levels
variable (κ : Type) [CommRing κ] {K : Type} [Field K]
abbrev HU (k : ℕ) : Subgroup (GL (Fin k) κ) := uniUT k κ k []
variable {κ}
def psiU (ψ : AddChar κ K) (k : ℕ) : ↥(HU κ k) →* Kˣ := supChar ψ k k [] (Finset.range (k - 1))
variable (κ)
abbrev HX (n k t j : ℕ) : Subgroup (GL (Fin n) κ) := uniUT n κ (k + j) (List.replicate j t)
def SX (k m j : ℕ) : Finset ℕ := (Finset.range (k + j - 1)).filter fun i => i + 1 ≠ k ∨ j + 1 = m
variable {κ}
def lamX (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n k m t j : ℕ) : ↥(HX κ n k t j) →* Kˣ :=
  lamGen ψ χ n (k + j) (List.replicate j t) (SX k m j)
variable (κ)
abbrev HJ (n r t j : ℕ) : Subgroup (GL (Fin n) κ) := uniUT n κ r (List.replicate j t)
variable {κ}
def lamJ (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n r t j : ℕ) : ↥(HJ κ n r t j) →* Kˣ :=
  lamGen ψ χ n r (List.replicate j t) (Finset.range (r - 1))
variable (κ)
def HJsharp (n k r t j : ℕ) : Subgroup (GL (Fin n) κ) := HJ κ n r t j ⊓ fixCol n κ k
variable {κ}
def lamJsharp (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n k r t j : ℕ) : ↥(HJsharp κ n k r t j) →* Kˣ :=
  (lamJ ψ χ n r t j).comp (Subgroup.inclusion inf_le_left)
variable (κ)
def HXm (n r t m : ℕ) : Subgroup (GL (Fin n) κ) := HJ κ n r t m ⊓ fixCol n κ (r + m * t)
variable {κ}
def lamXm (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n r t m : ℕ) : ↥(HXm κ n r t m) →* Kˣ :=
  (lamJ ψ χ n r t m).comp (Subgroup.inclusion inf_le_left)
variable (κ)
def HXmsharp (n k r t m : ℕ) : Subgroup (GL (Fin n) κ) := HXm κ n r t m ⊓ fixCol n κ k
variable {κ}
def lamXmsharp (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n k r t m : ℕ) : ↥(HXmsharp κ n k r t m) →* Kˣ :=
  (lamXm ψ χ n r t m).comp (Subgroup.inclusion inf_le_left)
variable (κ)
abbrev HV (n r t : ℕ) : Subgroup (GL (Fin n) κ) := uniUT n κ r [t]
variable {κ}
def lamV (ψ : AddChar κ K) (χj : κˣ →* Kˣ) (n r t : ℕ) : ↥(HV κ n r t) →* Kˣ :=
  lamGen ψ⁻¹ (fun _ => χj⁻¹) n r [t] (Finset.range (r - 1))
variable (κ)
def HVsharp (n k r t : ℕ) : Subgroup (GL (Fin n) κ) := HV κ n r t ⊓ fixCol n κ k
variable {κ}
def lamVsharp (ψ : AddChar κ K) (χj : κˣ →* Kˣ) (n k r t : ℕ) : ↥(HVsharp κ n k r t) →* Kˣ :=
  (lamV ψ χj n r t).comp (Subgroup.inclusion inf_le_left)
variable (κ)
abbrev HKJ (n r t j : ℕ) : Subgroup (GL (Fin n) κ) := HK n κ r (List.replicate j t)
variable {κ}
def lamKJ (χ : ℕ → κˣ →* Kˣ) (n r t j : ℕ) : ↥(HKJ κ n r t j) →* Kˣ := lamK χ n r (List.replicate j t)
variable (κ)
abbrev HKV (n r t : ℕ) : Subgroup (GL (Fin n) κ) := HK n κ r [t]
variable {κ}
def lamKV (χj : κˣ →* Kˣ) (n r t : ℕ) : ↥(HKV κ n r t) →* Kˣ := lamK (fun _ => χj⁻¹) n r [t]
variable (κ)
def HPsym (n k rS : ℕ) : Subgroup (GL (Fin n) κ) where
  carrier := {M | M ∈ uniUT n κ n [] ∧ ∀ i j : Fin n, rS ≤ i.val → i.val < rS + k → j.val = rS + k →
    (M : Matrix (Fin n) (Fin n) κ) i j = 0}
  one_mem' := ⟨Subgroup.one_mem _, fun i j _ h2 h3 => by
    rw [Units.val_one]; exact Matrix.one_apply_ne fun e => by rw [e] at h2; omega⟩
  mul_mem' := fun {A B} hA hB => ⟨Subgroup.mul_mem _ hA.1 hB.1, fun i j h1 h2 h3 => by
    rw [Units.val_mul, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases c1 : l.val < i.val
    · rw [hA.1.1 ((fine_lt_right i.2).mpr c1), zero_mul]
    · by_cases c2 : l.val < rS + k
      · rw [hB.2 l j (by omega) c2 h3, mul_zero]
      · by_cases c3 : l.val = rS + k
        · rw [hA.2 i l h1 h2 c3, zero_mul]
        · rw [hB.1.1 ((fine_lt_left j.2).mpr (by omega)), mul_zero]⟩
  inv_mem' := fun {A} hA => ⟨Subgroup.inv_mem _ hA.1, fun i j h1 h2 h3 => by
    have hX := Subgroup.inv_mem _ hA.1
    have h0 : ((A⁻¹ * A : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j = 0 := by
      rw [inv_mul_cancel, Units.val_one]; exact Matrix.one_apply_ne fun e => by rw [e] at h2; omega
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single j, hA.1.2 j j.2, mul_one] at h0
    · exact h0
    · intro l _ hl
      have hl' : l.val ≠ j.val := fun e => hl (Fin.ext e)
      by_cases c1 : l.val < i.val
      · rw [hX.1 ((fine_lt_right i.2).mpr c1), zero_mul]
      · by_cases c2 : l.val < rS + k
        · rw [hA.2 l j (by omega) c2 h3, mul_zero]
        · rw [hA.1.1 ((fine_lt_left j.2).mpr (by omega)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h⟩
theorem HPsym_le (n k rS : ℕ) : HPsym κ n k rS ≤ uniUT n κ n [] := fun _ h => h.1
variable {κ}
def offSum {n : ℕ} (k rS : ℕ) (M : Matrix (Fin n) (Fin n) κ) : κ :=
  ∑ i : Fin n, ∑ j : Fin n, if i.val + 1 = rS ∧ j.val = rS + k then M i j else 0
theorem off_mul {n k rS : ℕ} {A B : GL (Fin n) κ} (hA : A ∈ HPsym κ n k rS) (hB : B ∈ HPsym κ n k rS)
    (i j : Fin n) (hi : i.val + 1 = rS) (hj : j.val = rS + k) :
    ((A * B : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) i j =
      (A : Matrix (Fin n) (Fin n) κ) i j + (B : Matrix (Fin n) (Fin n) κ) i j := by
  have hne : i ≠ j := fun h => by rw [h] at hi; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add i j hne, hA.1.2 i i.2, hB.1.2 j j.2, one_mul, mul_one, add_comm]
  · rintro l _ ⟨h1, h2⟩
    have h1' : l.val ≠ i.val := fun h => h1 (Fin.ext h)
    have h2' : l.val ≠ j.val := fun h => h2 (Fin.ext h)
    by_cases c1 : l.val < i.val
    · rw [hA.1.1 ((fine_lt_right i.2).mpr c1), zero_mul]
    · by_cases c2 : l.val < rS + k
      · rw [hB.2 l j (by omega) c2 hj, mul_zero]
      · rw [hB.1.1 ((fine_lt_left j.2).mpr (by omega)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h
  · intro h; exact absurd (Finset.mem_univ j) h
def offHom (κ : Type) [CommRing κ] (n k rS : ℕ) : ↥(HPsym κ n k rS) →* Multiplicative κ where
  toFun M := Multiplicative.ofAdd (offSum k rS (M.1 : Matrix (Fin n) (Fin n) κ))
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    unfold offSum
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with h
    · have hne : i ≠ j := fun h' => by rw [h'] at h; omega
      simp [Matrix.one_apply_ne hne]
    · rfl
  map_mul' A B := by
    rw [← ofAdd_add]
    congr 1
    unfold offSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    split_ifs with h
    · exact off_mul A.2 B.2 i j h.1 h.2
    · simp
def SPsym (n k rS : ℕ) : Finset ℕ := (Finset.range (n - 1)).filter fun i => i + 1 ≠ rS ∧ i + 1 ≠ rS + k
def chiSym (ψ : AddChar κ K) (n k rS : ℕ) : ↥(HPsym κ n k rS) →* Kˣ :=
  (supChar ψ n n [] (SPsym n k rS)).comp (Subgroup.inclusion (HPsym_le κ n k rS)) *
    ψ.toMonoidHom.toHomUnits.comp (offHom κ n k rS)
variable (κ)
abbrev HQ (n a b : ℕ) : Subgroup (GL (Fin n) κ) := blockUT n κ a [b]
variable {κ}
def lamQ (ξ : κˣ →* Kˣ) (n a b : ℕ) : ↥(HQ κ n a b) →* Kˣ := detChar (fun _ => ξ) n a [b]
end Levels
section Products
variable {K : Type} [Field K]
def piProj {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) (i : ι) :
    ↥(Subgroup.pi Set.univ H) →* ↥(H i) where
  toFun x := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
def piChar {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) (lam : ∀ i, ↥(H i) →* Kˣ) :
    ↥(Subgroup.pi Set.univ H) →* Kˣ :=
  ∏ i, (lam i).comp (piProj H i)
variable (E : Type) [Field E] [NumberField E]
abbrev GLs (SG : Finset (HeightOneSpectrum (𝓞 E))) (n : ℕ) : Type := ∀ w : {w // w ∈ SG}, GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)
abbrev G0 (SG : Finset (HeightOneSpectrum (𝓞 E))) (r : ℕ) : Type := GLs E SG r
variable {E}
def diagonalEmbeddingProduct (SG : Finset (HeightOneSpectrum (𝓞 E))) {r n : ℕ} (h : r ≤ n) : G0 E SG r →* GLs E SG n where
  toFun g w := diagEmb _ h (g w)
  map_one' := by funext w; exact map_one _
  map_mul' a b := by funext w; exact map_mul _ _ _
def UpperUnipotentProduct (SG : Finset (HeightOneSpectrum (𝓞 E))) (r : ℕ) : Subgroup (G0 E SG r) :=
  Subgroup.pi Set.univ fun w => HU (𝓞 E ⧸ w.1.asIdeal) r
def genericUnipotentCharacter (SG : Finset (HeightOneSpectrum (𝓞 E))) (ψ : ∀ w : {w // w ∈ SG}, AddChar (𝓞 E ⧸ w.1.asIdeal) K) (r : ℕ) :
    ↥(UpperUnipotentProduct SG r) →* Kˣ :=
  piChar (fun w => HU (𝓞 E ⧸ w.1.asIdeal) r) fun w => psiU (ψ w) r
end Products
section Twist
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
def lamQP (ξ : Formalism.L2.DIV.Chr F E L) (P : HeightOneSpectrum (𝓞 E)) (n a b : ℕ) : ↥(HQ (𝓞 E ⧸ P.asIdeal) n a b) →* Lˣ :=
  lamQ (Formalism.L2.DIV.resChar ξ P) n a b
end Twist
end Formalism.L2.Col


