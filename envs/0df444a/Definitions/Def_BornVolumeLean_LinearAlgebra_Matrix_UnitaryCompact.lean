-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Matrix_UnitaryCompact
-- name    : BornVolumeLean_LinearAlgebra_Matrix_UnitaryCompact
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:12.303803+00:00
-- url     : https://prove2.me/theorems/9a97440d-60f6-481d-9730-4ac0b0018a2e
-- title:
--   Unitary Compact
-- statement:
--   Definitions and structural lemmas for Unitary Compact, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Matrix/UnitaryCompact.lean

module
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Algebra.Star.Unitary
set_option autoImplicit false
@[expose] public section
@[expose] public section
open scoped Matrix.Norms.Elementwise
namespace Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma sum_norm_sq_col (A : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ k : ι, ‖A.val k j‖ ^ 2 = 1 := by
  -- Start from the unitarity identity `star A.val * A.val = 1`.
  have h_unit : (star A.val : Matrix ι ι ℂ) * A.val
                  = (1 : Matrix ι ι ℂ) :=
    Unitary.coe_star_mul_self A
  -- Evaluate at (j, j): the (j,j) entry equals 1.
  have h_jj : ((star A.val : Matrix ι ι ℂ) * A.val) j j = 1 := by
    rw [h_unit, Matrix.one_apply_eq]
  -- Expand the matrix product:
  --   ∑ k, (star A.val) j k * A.val k j = 1.
  rw [Matrix.mul_apply] at h_jj
  -- Use Matrix.star_apply : (star M) j k = star (M k j), so the LHS
  -- becomes ∑ k, star (A.val k j) * A.val k j.
  -- For complex numbers, star z * z = ↑(‖z‖²) (as a complex coercion of a real).
  have h_eq : ∀ k : ι,
      (star A.val : Matrix ι ι ℂ) j k * A.val k j
        = ((‖A.val k j‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    rw [Matrix.star_apply]
    exact_mod_cast Complex.conj_mul' (A.val k j)
  rw [Finset.sum_congr rfl (fun k _ => h_eq k)] at h_jj
  -- Now h_jj : (∑ k, ↑(‖A.val k j‖^2 : ℝ) : ℂ) = 1
  -- Push the cast: ↑(∑ ‖A k j‖²) = 1, so ∑ ‖A k j‖² = 1.
  rw [← Complex.ofReal_sum] at h_jj
  exact_mod_cast h_jj
lemma val_norm_apply_le_one (A : Matrix.unitaryGroup ι ℂ) (i j : ι) :
    ‖A.val i j‖ ≤ 1 := by
  have h_sum : ∑ k : ι, ‖A.val k j‖ ^ 2 = 1 := sum_norm_sq_col A j
  have h_i_le : ‖A.val i j‖ ^ 2 ≤ ∑ k, ‖A.val k j‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖A.val k j‖ ^ 2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  rw [h_sum] at h_i_le
  -- h_i_le : ‖A.val i j‖² ≤ 1
  have h_nn : 0 ≤ ‖A.val i j‖ := norm_nonneg _
  nlinarith
lemma val_norm_le_one (A : Matrix.unitaryGroup ι ℂ) :
    ‖A.val‖ ≤ 1 := by
  rw [Matrix.norm_le_iff zero_le_one]
  exact fun i j => val_norm_apply_le_one A i j
lemma isBounded_underlyingSet :
    Bornology.IsBounded
      (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  refine Metric.isBounded_iff.mpr ⟨2, ?_⟩
  rintro A hA B hB
  rw [dist_eq_norm]
  calc ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le A B
    _ ≤ 1 + 1 := add_le_add (val_norm_le_one ⟨A, hA⟩) (val_norm_le_one ⟨B, hB⟩)
    _ = 2 := by norm_num
lemma isClosed_underlyingSet :
    IsClosed (Matrix.unitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) :=
  isClosed_unitary
instance instCompactSpace : CompactSpace (Matrix.unitaryGroup ι ℂ) := by
  have : ProperSpace (Matrix ι ι ℂ) :=
    FiniteDimensional.proper_rclike ℂ _
  have h_compact :
      IsCompact ((Matrix.unitaryGroup ι ℂ : Submonoid _) :
        Set (Matrix ι ι ℂ)) :=
    Metric.isCompact_of_isClosed_isBounded
      isClosed_underlyingSet isBounded_underlyingSet
  exact isCompact_iff_compactSpace.mp h_compact
noncomputable instance instMeasurableSpace :
    MeasurableSpace (Matrix.unitaryGroup ι ℂ) :=
  borel _
instance instBorelSpace : BorelSpace (Matrix.unitaryGroup ι ℂ) := ⟨rfl⟩
end Matrix.UnitaryGroup


