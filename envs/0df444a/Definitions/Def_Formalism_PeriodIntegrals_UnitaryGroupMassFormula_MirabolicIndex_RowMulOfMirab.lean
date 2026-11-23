-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirabolicIndex_RowMulOfMirab
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:29.738549+00:00
-- url     : https://prove2.me/theorems/2bd5c3b0-effb-44fc-b252-ebaace2f614e
-- title:
--   Row Mul Of Mirab
-- statement:
--   Definitions and structural lemmas for Row Mul Of Mirab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirabolicIndex/RowMulOfMirab.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_MirabIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.MirabolicIndex₂
open Finset Matrix PI.MirabIndex
variable {k : Type} [Field k] [Fintype k]
def eLast (n : ℕ) : Fin (n + 1) → k := fun j => if j = Fin.last n then 1 else 0
theorem isMirab_iff (n : ℕ) (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :
    IsMirab h ↔ h (Fin.last n) = eLast n := by
  unfold PI.MirabIndex.IsMirab
  exact ⟨fun H => funext H, fun H j => congrFun H j⟩
theorem one_last (n : ℕ) : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = eLast n := by
  funext j
  by_cases h : j = Fin.last n
  · subst h
    simp [eLast]
  · simp [eLast, h, Matrix.one_apply, Ne.symm h]
theorem row_mul_eq (n : ℕ) {a b : Matrix (Fin (n + 1)) (Fin (n + 1)) k}
    (c : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (h : a (Fin.last n) = b (Fin.last n)) :
    (a * c) (Fin.last n) = (b * c) (Fin.last n) := by
  have h' : ∀ x, a (Fin.last n) x = b (Fin.last n) x := fun x => congrFun h x
  funext j
  simp only [Matrix.mul_apply, h']
theorem row_ne_zero (n : ℕ) (h : GL (Fin (n + 1)) k) :
    (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) ≠ 0 := by
  intro hz
  have h0 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero (Fin.last n) (fun j => by simp [hz])
  exact (isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units h)) h0
theorem exists_row (n : ℕ) (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = v := by
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n)
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) k := fun i j =>
    if i = Fin.last n then v (σ j) else if i = j then 1 else 0
  have hM : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    have hne : i ≠ j := ne_of_lt hij'
    simp [M, hi, hne]
  have hMdet : M.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular M hM]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [M, σ, hp]
    · simp [M, hi]
  have hNdet : (M.submatrix id σ).det ≠ 0 := by
    rw [Matrix.det_permute']
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs, hMdet]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (M.submatrix id σ) hNdet, ?_⟩
  funext j
  show M (Fin.last n) (σ j) = v j
  simp [M, σ]
def rowMap (n : ℕ) (h : GL (Fin (n + 1)) k) : {v : Fin (n + 1) → k // v ≠ 0} :=
  ⟨(h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n), row_ne_zero n h⟩
theorem mirab_mul_inv (n : ℕ) (h g : GL (Fin (n + 1)) k)
    (hh : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)) :
    IsMirab ((h * g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  rw [isMirab_iff, Units.val_mul, row_mul_eq n _ hh, Units.mul_inv, one_last]
theorem row_mul_of_mirab (n : ℕ) (p g : GL (Fin (n + 1)) k)
    (hp : IsMirab (p : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) :
    ((p * g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) := by
  rw [Units.val_mul,
    row_mul_eq n _ (((isMirab_iff n _).mp hp).trans (one_last (k := k) n).symm),
    one_mul]
noncomputable def fiberEquiv (n : ℕ) (v : {v : Fin (n + 1) → k // v ≠ 0}) :
    {h : GL (Fin (n + 1)) k // rowMap n h = v} ≃
      {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} :=
  let g := (exists_row n v.1 v.2).choose
  have hg : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = v.1 :=
    (exists_row n v.1 v.2).choose_spec
  { toFun := fun h => ⟨h.1 * g⁻¹, mirab_mul_inv n h.1 g (by rw [hg]; exact congrArg Subtype.val h.2)⟩
    invFun := fun p => ⟨p.1 * g, Subtype.ext (by
      show ((p.1 * g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = v.1
      rw [row_mul_of_mirab n p.1 g p.2, hg])⟩
    left_inv := fun h => Subtype.ext (by simp)
    right_inv := fun p => Subtype.ext (by simp) }
abbrev Pairs (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1 < p.2}
def uniMat {n : ℕ} (f : Pairs n → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0
theorem uniMat_upper {n : ℕ} (f : Pairs n → k) : (uniMat f).IsUpperTriangular := by
  intro i j hij
  have hji : j < i := hij
  simp [uniMat, ne_of_gt hji, not_lt.mpr hji.le]
theorem uniMat_det {n : ℕ} (f : Pairs n → k) : (uniMat f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (uniMat_upper f)]
  simp [uniMat]
noncomputable def uniGL {n : ℕ} (f : Pairs n → k) : GL (Fin (n + 1)) k :=
  GeneralLinearGroup.mkOfDetNeZero (uniMat f) (by rw [uniMat_det]; exact one_ne_zero)
theorem uniGL_coe {n : ℕ} (f : Pairs n → k) :
    ((uniGL f : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = uniMat f :=
  rfl
theorem isUniU_uniGL {n : ℕ} (f : Pairs n → k) :
    IsUniU ((uniGL f : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  rw [uniGL_coe]
  unfold PI.MirabIndex.IsUniU
  exact ⟨fun i => by simp [uniMat], fun i j hji => uniMat_upper f hji⟩
noncomputable def uniEquiv (n : ℕ) :
    {u : GL (Fin (n + 1)) k // IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} ≃
      (Pairs n → k) where
  toFun u p := (u.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p.1.1 p.1.2
  invFun f := ⟨uniGL f, isUniU_uniGL f⟩
  left_inv u := by
    obtain ⟨u, hd, hl⟩ := u
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro i j
    simp only [uniGL_coe, uniMat]
    by_cases h : i = j
    · subst h; simp [hd i]
    · by_cases h' : i < j
      · simp [h, h']
      · have : j < i := lt_of_le_of_ne (not_lt.mp h') (Ne.symm h)
        simp [h, h', hl i j this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h1 : i ≠ j := ne_of_lt h
    simp [uniGL_coe, uniMat, h1, h]
end PI.MirabolicIndex₂


