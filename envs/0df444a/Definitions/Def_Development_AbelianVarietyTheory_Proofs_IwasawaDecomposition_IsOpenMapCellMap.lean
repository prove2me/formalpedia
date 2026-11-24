-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenMapCellMap
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsOpenMapCellMap
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:25.215345+00:00
-- url     : https://prove2.me/theorems/e7a42057-d2ea-45be-874a-27e8f5958aed
-- title:
--   Is Open Map Cell Map
-- statement:
--   Definitions and structural lemmas for Is Open Map Cell Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsOpenMapCellMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LuLowerLowerTriangular
import Theorems.Thm_GlobalTheory_FlagPts_cellFrame_apply
import Theorems.Thm_GlobalTheory_FlagPts_luLower_apply_of_lt
import Theorems.Thm_GlobalTheory_FlagPts_luLower_apply_self
import Theorems.Thm_GlobalTheory_FlagPts_luLower_lowerTriangular
import Theorems.Thm_GlobalTheory_FlagPts_uniMat_apply_of_lt
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
import Theorems.Thm_GlobalTheory_FullFlag_ofBasis_eq_ofBasis_iff
import Theorems.Thm_GlobalTheory_mem_upperTriangularGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace GlobalTheory.FlagPts
namespace GlobalTheory.FlagPts
theorem exists_pow_mul_eval_mem {k : Type} [Field k] {X J : Type} (R : Subalgebra k (X → k)) (D : X → k) (g : J → X → k) (hD : D ∈ R)
    (hg : ∀ j, D * g j ∈ R) (q : MvPolynomial J k) :
    ∃ N : ℕ, (D ^ N * fun x => MvPolynomial.eval (fun j => g j x) q) ∈ R := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    convert R.algebraMap_mem a using 1
    funext x
    simp
  | add p q hp hq =>
    obtain ⟨N₁, h₁⟩ := hp
    obtain ⟨N₂, h₂⟩ := hq
    refine ⟨N₁ + N₂, ?_⟩
    have : (D ^ (N₁ + N₂) * fun x => MvPolynomial.eval (fun j => g j x) (p + q)) =
        D ^ N₂ * (D ^ N₁ * fun x => MvPolynomial.eval (fun j => g j x) p) +
          D ^ N₁ * (D ^ N₂ * fun x => MvPolynomial.eval (fun j => g j x) q) := by
      funext x
      simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply, map_add]
      ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hD _) h₁) (mul_mem (pow_mem hD _) h₂)
  | mul_X p j hp =>
    obtain ⟨N, h⟩ := hp
    refine ⟨N + 1, ?_⟩
    have : (D ^ (N + 1) * fun x => MvPolynomial.eval (fun j => g j x) (p * MvPolynomial.X j)) =
        (D ^ N * fun x => MvPolynomial.eval (fun j => g j x) p) * (D * g j) := by
      funext x
      simp only [Pi.mul_apply, Pi.pow_apply, map_mul, MvPolynomial.eval_X]
      ring
    rw [this]
    exact mul_mem h (hg j)
theorem flags_apply_eq_cellMap_iff (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b c : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) :
    c.flags i = cellMap b u i ↔ ((uniMat u i)⁻¹ * (b i).toMatrix (c i)).BlockTriangular id := by
  have hcell : (b i).toMatrix (cellFrame b u i) = uniMat u i := by
    ext a m
    rw [Basis.toMatrix_apply, cellFrame_apply]
    simp [Finsupp.single_apply]
  have h1 : IsUnit ((b i).toMatrix (cellFrame b u i)).det := by rw [hcell, det_uniMat]; exact isUnit_one
  have hchg : (cellFrame b u i).toMatrix (c i) = (uniMat u i)⁻¹ * (b i).toMatrix (c i) := by
    rw [← hcell, ← Basis.toMatrix_mul_toMatrix (b i) (cellFrame b u i) (c i), ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ h1, Matrix.one_mul]
  show FullFlag.ofBasis (c i) = FullFlag.ofBasis (cellFrame b u i) ↔ _
  rw [FullFlag.ofBasis_eq_ofBasis_iff]
  constructor
  · rintro ⟨g, hg, hgc⟩
    rw [← hchg, ← hgc, toMatrix_basisMulGL]
    exact hg
  · intro h
    refine ⟨basisChange (cellFrame b u i) (c i), ?_, basisMulGL_basisChange _ _⟩
    rw [mem_upperTriangularGL]
    intro a m hm
    rw [coe_basisChange, hchg]
    exact h hm
section Reg
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
theorem const_mem_regFns (x : k) : (fun _ : Frames k V => x) ∈ regFns k V := by
  convert (regFns k V).algebraMap_mem x
  rfl
theorem toMatrix_entry_mem_regFns (b : Frames k V) (i : ι) (a l : Fin (finrank k (V i))) :
    (fun c : Frames k V => (b i).toMatrix (c i) a l) ∈ regFns k V :=
  Algebra.subset_adjoin (Or.inl ⟨i, (b i).coord a, l, by funext c; simp [Basis.toMatrix_apply]⟩)
theorem det_mem_regFns {m : ℕ} (M : Frames k V → Matrix (Fin m) (Fin m) k)
    (hM : ∀ a c, (fun x => M x a c) ∈ regFns k V) : (fun x => (M x).det) ∈ regFns k V := by
  have : (fun x => (M x).det) = ∑ σ : Equiv.Perm (Fin m),
      (fun _ : Frames k V => ((Equiv.Perm.sign σ : ℤ) : k)) * ∏ a, fun x => M x (σ a) a := by
    funext x
    simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact Subalgebra.sum_mem _ fun σ _ => mul_mem (const_mem_regFns _) (Subalgebra.prod_mem _ fun a _ => hM _ _)
end Reg
theorem leadMinor_toMatrix_mem_regFns (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b : Frames k V) (i : ι) (m : Fin (finrank k (V i))) :
    (fun c : Frames k V => leadMinor ((b i).toMatrix (c i)) m) ∈ regFns k V :=
  det_mem_regFns (fun c => leadBlock ((b i).toMatrix (c i)) m) fun _ _ => toMatrix_entry_mem_regFns b i _ _
theorem luNum_toMatrix_mem_regFns (k : Type) [Field k] (ι : Type) (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (b : Frames k V) (i : ι) (a m : Fin (finrank k (V i))) :
    (fun c : Frames k V => luNum ((b i).toMatrix (c i)) a m) ∈ regFns k V := by
  have : (fun c : Frames k V => luNum ((b i).toMatrix (c i)) a m) = ∑ l : Fin (m + 1),
      (fun c : Frames k V => (b i).toMatrix (c i) a (Fin.castLE m.isLt l)) *
        fun c => ((leadBlock ((b i).toMatrix (c i)) m).updateCol l (Pi.single (Fin.last m) 1)).det := by
    funext c
    simp [luNum, Finset.sum_apply, Matrix.cramer_apply]
  rw [this]
  refine Subalgebra.sum_mem _ fun l _ => mul_mem (toMatrix_entry_mem_regFns b i _ _) (det_mem_regFns _ fun a' c' => ?_)
  by_cases h : c' = l
  · simp only [Matrix.updateCol_apply, h, if_true]
    exact const_mem_regFns _
  · simp only [Matrix.updateCol_apply, h, if_false]
    exact toMatrix_entry_mem_regFns b i _ _
theorem leadMinor_mul_ne_zero {k : Type} [Field k] {n : ℕ} (L U : Matrix (Fin n) (Fin n) k) (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) (hU : U.BlockTriangular id) (hdet : IsUnit (L * U).det) : ∀ m, leadMinor (L * U) m ≠ 0 := by
  intro m
  have hLd : L.det = 1 := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  have hUd : ∀ l, U l l ≠ 0 := by
    have : U.det ≠ 0 := by
      rw [Matrix.det_mul, hLd, one_mul] at hdet
      exact hdet.ne_zero
    rw [Matrix.det_of_upperTriangular hU] at this
    exact fun l => Finset.prod_ne_zero_iff.1 this l (Finset.mem_univ _)
  have hblock : leadBlock (L * U) m = leadBlock L m * leadBlock U m := by
    ext a c
    simp only [leadBlock, Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE m.isLt) (Fin.castLE_injective _) _ _ (fun l hl => ?_) (fun _ => rfl)
    have ha := a.isLt
    have : Fin.castLE m.isLt a < l := by
      rw [Fin.lt_def, Fin.coe_castLE]
      by_contra h
      push_neg at h
      exact hl ⟨⟨l, by omega⟩, Fin.ext (by simp)⟩
    rw [hL (by simpa using this), zero_mul]
  rw [leadMinor, hblock, Matrix.det_mul,
    Matrix.det_of_lowerTriangular (leadBlock L m) (fun a c h => hL (show OrderDual.toDual (Fin.castLE m.isLt c) < OrderDual.toDual (Fin.castLE m.isLt a) by
      rw [OrderDual.toDual_lt_toDual, Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact Fin.lt_def.1 (OrderDual.toDual_lt_toDual.1 h))),
    Matrix.det_of_upperTriangular (M := leadBlock U m) (fun a c h => hU (show Fin.castLE m.isLt c < Fin.castLE m.isLt a by
      rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact Fin.lt_def.1 h))]
  simp only [leadBlock, Matrix.submatrix_apply, hL1, Finset.prod_const_one, one_mul]
  exact Finset.prod_ne_zero_iff.2 fun l _ => hUd _
theorem exists_upperTriangular_mul_eq_luLower {k : Type} [Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k) (hΔ : ∀ m, leadMinor P m ≠ 0) :
    ∃ X : Matrix (Fin n) (Fin n) k, X.BlockTriangular id ∧ P * X = luLower P := by
  classical
  let X : Matrix (Fin n) (Fin n) k := fun l m => if h : (l : ℕ) ≤ m then
    (leadBlock P m).cramer (Pi.single (Fin.last m) 1) ⟨l, Nat.lt_succ_of_le h⟩ / leadMinor P m else 0
  refine ⟨X, fun a c hac => ?_, ?_⟩
  · have : ¬ (a : ℕ) ≤ c := not_le.2 (Fin.lt_def.1 hac)
    simp only [X, dif_neg this]
  · ext a m
    have key : (P * X) a m = luNum P a m / leadMinor P m := by
      rw [Matrix.mul_apply, luNum, Finset.sum_div]
      symm
      refine Fintype.sum_of_injective (Fin.castLE m.isLt) (Fin.castLE_injective _) _ _ (fun l hl => ?_) (fun l => ?_)
      · have hm := m.isLt
        have hn : ¬ (l : ℕ) ≤ m := fun h => hl ⟨⟨l, by omega⟩, Fin.ext (by simp)⟩
        simp only [X, dif_neg hn, mul_zero]
      · have hl : ((Fin.castLE m.isLt l : Fin n) : ℕ) ≤ m := by simpa using Nat.lt_succ_iff.1 l.isLt
        simp only [X, dif_pos hl, mul_div_assoc]
        rfl
    rw [key]
    rcases lt_or_ge m a with h | h
    · rw [luLower_apply_of_lt _ h]
    · have hmul := congrFun (Matrix.mulVec_cramer (leadBlock P m) (Pi.single (Fin.last m) 1))
        ⟨a, Nat.lt_succ_of_le h⟩
      have e : luNum P a m = (Matrix.mulVec (leadBlock P m) ((leadBlock P m).cramer (Pi.single (Fin.last m) 1)))
          ⟨a, Nat.lt_succ_of_le h⟩ := rfl
      rw [e, hmul, Pi.smul_apply, smul_eq_mul]
      rcases (show a ≤ m from h).eq_or_lt with rfl | h'
      · have : (⟨a, Nat.lt_succ_of_le h⟩ : Fin (a + 1)) = Fin.last a := Fin.ext rfl
        rw [this, Pi.single_eq_same, mul_one, luLower_apply_self]
        exact div_self (hΔ a)
      · have : (⟨a, Nat.lt_succ_of_le h⟩ : Fin (m + 1)) ≠ Fin.last m := fun h2 =>
          h'.ne (Fin.ext (by simpa [Fin.ext_iff] using h2))
        rw [Pi.single_eq_of_ne this, mul_zero, zero_div, luLower_lowerTriangular _ (by simpa using h')]
section
variable {k : Type} [Field k] {n : ℕ}
theorem eq_of_mul_upperTriangular {L L' T : Matrix (Fin n) (Fin n) k} (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) (hL' : L'.BlockTriangular OrderDual.toDual) (hL'1 : ∀ a, L' a a = 1)
    (hT : T.BlockTriangular id) (h : L * T = L') : L = L' := by
  have hdet : IsUnit L.det := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  letI := L.invertibleOfIsUnitDet hdet
  have hT' : T = L⁻¹ * L' := by
    rw [← h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hlow : T.BlockTriangular OrderDual.toDual := hT' ▸ (Matrix.blockTriangular_inv_of_blockTriangular hL).mul hL'
  have hT1 : T = 1 := by
    ext a c
    rcases lt_trichotomy a c with h1 | rfl | h1
    · rw [hlow (by simpa using h1), Matrix.one_apply_ne h1.ne]
    · have := congrFun (congrFun h a) a
      rw [Matrix.mul_apply, Finset.sum_eq_single a (fun l _ hl => ?_) (by simp), hL1, hL'1, one_mul] at this
      · rw [this, Matrix.one_apply_eq]
      · rcases lt_or_gt_of_ne hl with h2 | h2
        · rw [hlow (by simpa using h2), mul_zero]
        · rw [hL (by simpa using h2), zero_mul]
    · rw [hT h1, Matrix.one_apply_ne h1.ne']
  rw [← h, hT1, Matrix.mul_one]
theorem lu_criterion (P L : Matrix (Fin n) (Fin n) k) (hP : IsUnit P.det) (hL : L.BlockTriangular OrderDual.toDual)
    (hL1 : ∀ a, L a a = 1) : (L⁻¹ * P).BlockTriangular id ↔ (∀ m, leadMinor P m ≠ 0) ∧ L = luLower P := by
  have hLdet : IsUnit L.det := by rw [Matrix.det_of_lowerTriangular _ hL]; simp [hL1]
  have hPLU : L * (L⁻¹ * P) = P := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hLdet, Matrix.one_mul]
  constructor
  · intro hU
    have hΔ : ∀ m, leadMinor P m ≠ 0 := by
      have := leadMinor_mul_ne_zero L _ hL hL1 hU (by rw [hPLU]; exact hP)
      rwa [hPLU] at this
    refine ⟨hΔ, ?_⟩
    obtain ⟨X, hX, hPX⟩ := exists_upperTriangular_mul_eq_luLower P hΔ
    refine eq_of_mul_upperTriangular hL hL1 (luLower_lowerTriangular P) (luLower_apply_self P) (hU.mul hX) ?_
    rw [← Matrix.mul_assoc, hPLU, hPX]
  · rintro ⟨hΔ, rfl⟩
    obtain ⟨X, hX, hPX⟩ := exists_upperTriangular_mul_eq_luLower P hΔ
    have hXdet : IsUnit X.det := by
      have := congrArg Matrix.det hPX
      rw [Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_right (this ▸ hLdet)
    letI := X.invertibleOfIsUnitDet hXdet
    have : (luLower P)⁻¹ * P = X⁻¹ := by
      rw [← hPX, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    rw [this]
    exact Matrix.blockTriangular_inv_of_blockTriangular hX
end
variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def cellCoord (b c : Frames k V) : AffPts k (CellIdx k V) := fun j =>
  luNum ((b j.1).toMatrix (c j.1)) j.2.1.1 j.2.1.2 / leadMinor ((b j.1).toMatrix (c j.1)) j.2.1.2
theorem uniMat_eq_luLower_iff (b c : Frames k V) (u : AffPts k (CellIdx k V)) :
    (∀ i, uniMat u i = luLower ((b i).toMatrix (c i))) ↔ u = cellCoord b c := by
  constructor
  · intro H
    funext j
    obtain ⟨i, ⟨⟨a, m⟩, h⟩⟩ := j
    have := congrFun (congrFun (H i) a) m
    rwa [uniMat_apply_of_lt u i h, luLower_apply_of_lt _ h] at this
  · rintro rfl i
    ext a m
    rcases lt_trichotomy a m with h | rfl | h
    · rw [uniMat_apply_of_gt _ i h, luLower_lowerTriangular _ (by simpa using h)]
    · rw [uniMat_apply_self, luLower_apply_self]
    · rw [uniMat_apply_of_lt _ i h, luLower_apply_of_lt _ h]
      rfl
theorem flags_eq_cellMap_iff (b c : Frames k V) (u : AffPts k (CellIdx k V)) :
    c.flags = cellMap b u ↔ (∀ i m, leadMinor ((b i).toMatrix (c i)) m ≠ 0) ∧ u = cellCoord b c := by
  have e : c.flags = cellMap b u ↔ ∀ i, c.flags i = cellMap b u i := ⟨fun h _ => h ▸ rfl, fun h => funext h⟩
  rw [← uniMat_eq_luLower_iff, e, ← forall_and]
  refine forall_congr' fun i => ?_
  rw [flags_apply_eq_cellMap_iff, lu_criterion _ _ (Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _))
    (uniMat_blockTriangular u i) (uniMat_apply_self u i), eq_comm (a := uniMat u i)]
section Assembly
variable {k : Type} [Field k] {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
def cellDet (b c : Frames k V) : k :=
  ∏ p : (Σ i, Fin (finrank k (V i))), leadMinor ((b p.1).toMatrix (c p.1)) p.2
theorem cellDet_ne_zero_iff (b c : Frames k V) :
    cellDet b c ≠ 0 ↔ ∀ i m, leadMinor ((b i).toMatrix (c i)) m ≠ 0 := by
  simp [cellDet, Finset.prod_ne_zero_iff, Sigma.forall]
theorem cellDet_mem (b : Frames k V) : (fun c => cellDet b c) ∈ regFns k V := by
  have : (fun c => cellDet b c) = ∏ p : (Σ i, Fin (finrank k (V i))),
      fun c : Frames k V => leadMinor ((b p.1).toMatrix (c p.1)) p.2 := by
    funext c
    simp [cellDet, Finset.prod_apply]
  rw [this]
  exact Subalgebra.prod_mem _ fun p _ => leadMinor_toMatrix_mem_regFns k ι V b p.1 p.2
theorem cellDet_sq_mul_mem (b : Frames k V) (j : CellIdx k V) :
    ((fun c => cellDet b c) ^ 2 * fun c => cellCoord b c j) ∈ regFns k V := by
  classical
  obtain ⟨i, ⟨⟨a, m⟩, h⟩⟩ := j
  let E : Frames k V → k := ∏ p ∈ Finset.univ.erase (⟨i, m⟩ : Σ i, Fin (finrank k (V i))),
    fun c => leadMinor ((b p.1).toMatrix (c p.1)) p.2
  have hE : E ∈ regFns k V := Subalgebra.prod_mem _ fun p _ => leadMinor_toMatrix_mem_regFns k ι V b p.1 p.2
  have : ((fun c => cellDet b c) ^ 2 * fun c => cellCoord b c ⟨i, ⟨⟨a, m⟩, h⟩⟩) =
      (fun c => cellDet b c) * (fun c => luNum ((b i).toMatrix (c i)) a m) * E := by
    funext c
    have hprod : cellDet b c = leadMinor ((b i).toMatrix (c i)) m * E c := by
      simp only [cellDet, E, Finset.prod_apply]
      exact (Finset.mul_prod_erase _ (fun p : (Σ i, Fin (finrank k (V i))) =>
        leadMinor ((b p.1).toMatrix (c p.1)) p.2) (Finset.mem_univ (⟨i, m⟩ : Σ i, Fin (finrank k (V i))))).symm
    simp only [Pi.mul_apply, Pi.pow_apply, cellCoord]
    by_cases h0 : leadMinor ((b i).toMatrix (c i)) m = 0
    · simp [hprod, h0]
    · rw [hprod]; field_simp
  rw [this]
  exact mul_mem (mul_mem (cellDet_mem b) (luNum_toMatrix_mem_regFns k ι V b i a m)) hE
theorem preimage_image_cellMap (b : Frames k V) (O : Set (AffPts k (CellIdx k V))) :
    Frames.flags ⁻¹' (cellMap b '' O) = {c | cellDet b c ≠ 0 ∧ cellCoord b c ∈ O} := by
  ext c
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq, cellDet_ne_zero_iff]
  constructor
  · rintro ⟨u, hu, h⟩
    obtain ⟨h1, rfl⟩ := (flags_eq_cellMap_iff b c u).1 h.symm
    exact ⟨h1, hu⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h2, ((flags_eq_cellMap_iff b c _).2 ⟨h1, rfl⟩).symm⟩
theorem isOpen_cellCoord_mem (b : Frames k V) {O : Set (AffPts k (CellIdx k V))} (hO : IsOpen O) :
    IsOpen {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ O} := by
  have hO' : GenerateOpen {s | ∃ p : MvPolynomial (CellIdx k V) k, s = {x : AffPts k (CellIdx k V) | MvPolynomial.eval x p ≠ 0}} O := hO
  clear hO
  induction hO' with
  | basic s hs =>
    obtain ⟨q, rfl⟩ := hs
    obtain ⟨N, hN⟩ := exists_pow_mul_eval_mem (regFns k V) _ (fun j c => cellCoord b c j) (pow_mem (cellDet_mem b) 2)
      (cellDet_sq_mul_mem b) q
    have : {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ {x : AffPts k (CellIdx k V) | MvPolynomial.eval x q ≠ 0}} =
        {c | ((fun c => cellDet b c) * (((fun c => cellDet b c) ^ 2) ^ N *
          fun c => MvPolynomial.eval (fun j => cellCoord b c j) q)) c ≠ 0} := by
      ext c
      simp only [Set.mem_setOf_eq, Pi.mul_apply, Pi.pow_apply, mul_ne_zero_iff, ne_eq, pow_eq_zero_iff', not_and,
        not_not]
      tauto
    rw [this]
    exact isOpen_generateFrom_of_mem ⟨_, mul_mem (cellDet_mem b) hN, rfl⟩
  | univ =>
    convert (isClosed_zero (cellDet_mem b)).isOpen_compl using 1
    ext c
    simp
  | inter s t _ _ hs ht =>
    convert hs.inter ht using 1
    ext c
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  | sUnion S _ hS =>
    have : {c : Frames k V | cellDet b c ≠ 0 ∧ cellCoord b c ∈ ⋃₀ S} =
        ⋃ s ∈ S, {c | cellDet b c ≠ 0 ∧ cellCoord b c ∈ s} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_sUnion, Set.mem_iUnion, exists_prop]
      tauto
    rw [this]
    exact isOpen_biUnion hS
end Assembly
theorem isOpenMap_cellMap (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) : IsOpenMap (cellMap b) := by
  intro O hO
  rw [isOpen_coinduced, preimage_image_cellMap]
  exact isOpen_cellCoord_mem b hO
end GlobalTheory.FlagPts
example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    [∀ i, FiniteDimensional k (V i)] (b : Frames k V), IsOpenMap (cellMap b) := GlobalTheory.FlagPts.isOpenMap_cellMap


