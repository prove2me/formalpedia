-- Prove2me | Definitions.Def_ChapterAbelianDiagonalCountable
-- name    : ChapterAbelianDiagonalCountable
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T05:41:21.246027+00:00
-- url     : https://prove2.me/theorems/e3c88689-d99d-4109-8262-fca6d64e24bd
-- title:
--   Chapter AbelianDiagonalCountable
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAbelianDiagonalCountable.lean`): generated def bundle for ChapterAbelianDiagonalCountable. See BookProof/ChapterAbelianDiagonalCountable.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAbelianDiagonalCountable.lean

import Mathlib


/-!
# The countable (type `I_∞`) case of the abelian von Neumann classification:
`ℓ∞(ℕ)` is a MASA of `B(ℓ²(ℕ))`

`BookProof/ChapterAbelianDiagonal.lean` proves the **finite** (type `Iₙ`) case of
von Neumann's classification of abelian von Neumann algebras: `ℓ∞({1,…,n})`,
realized as the diagonal subalgebra of `Mat(n, ℂ)`, is its own commutant.  This
file proves the next case of the list — the **countable** one, `ℓ∞(ℕ)` acting by
multiplication operators on `ℓ²(ℕ)`.

The full five-way classification (and its exhaustiveness) is a deep theorem and
is *not* claimed here; what is proved is the second isomorphism class as a
concrete MASA.

## Deliverables

* `Ell2C`, `EllInf` — the complex Hilbert space `ℓ²(ℕ)` and the algebra `ℓ∞(ℕ)`;
* `memℓp_diag_two` — a bounded sequence multiplies `ℓ²` into `ℓ²`;
* `diagOp d` — the **diagonal multiplication operator** of `d ∈ ℓ∞(ℕ)`, a bounded
  operator on `ℓ²(ℕ)` with `‖diagOp d‖ ≤ ‖d‖`;
* `diagOp_add`, `diagOp_smul`, `diagOp_mul`, `diagOp_one`, `diagOp_star` — `diagOp`
  is a unital `*`-algebra map;
* `diagOp_injective` — it is faithful, so `ℓ∞(ℕ)` really *is* an algebra of
  operators;
* `diagOp_comm` — the diagonal algebra is abelian;
* `commutes_diagOp_iff` — **maximal abelianness**: a bounded operator commutes
  with every diagonal operator iff it is itself diagonal;
* `vonNeumann_abelian_class_countable` — the headline packaging of the countable
  isomorphism class.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

open scoped ENNReal

noncomputable section

namespace BookProof.ChapterAbelianDiagonalCountable

/-- The complex Hilbert space `ℓ²(ℕ)`. -/
abbrev Ell2C := lp (fun _ : ℕ => ℂ) 2

/-- The algebra `ℓ∞(ℕ)` of bounded complex sequences. -/
abbrev EllInf := lp (fun _ : ℕ => ℂ) ∞

theorem norm_coord_le (d : EllInf) (i : ℕ) : ‖(d : ℕ → ℂ) i‖ ≤ ‖d‖ :=
  lp.norm_apply_le_norm (by simp) d i

/-- Multiplying an `ℓ²` sequence by a bounded sequence stays in `ℓ²`, with the
expected bound on the partial sums. -/
theorem memℓp_diag_two (d : EllInf) (f : Ell2C) :
    Memℓp (fun i => (d : ℕ → ℂ) i * (f : ℕ → ℂ) i) 2 := by
  have hd0 : 0 ≤ ‖d‖ := norm_nonneg _
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine memℓp_gen' (C := (‖d‖ * ‖f‖) ^ (2 : ℝ≥0∞).toReal) fun s => ?_
  have h1 : ∀ i ∈ s, ‖(d : ℕ → ℂ) i * (f : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ‖d‖ ^ (2:ℝ≥0∞).toReal * ‖(f : ℕ → ℂ) i‖ ^ (2:ℝ≥0∞).toReal := by
    intro i _
    rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    gcongr
    exact norm_coord_le d i
  calc ∑ i ∈ s, ‖(d : ℕ → ℂ) i * (f : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑ i ∈ s, ‖d‖ ^ (2:ℝ≥0∞).toReal * ‖(f : ℕ → ℂ) i‖ ^ (2:ℝ≥0∞).toReal :=
        Finset.sum_le_sum h1
    _ = ‖d‖ ^ (2:ℝ≥0∞).toReal * ∑ i ∈ s, ‖(f : ℕ → ℂ) i‖ ^ (2:ℝ≥0∞).toReal := by
        rw [Finset.mul_sum]
    _ ≤ ‖d‖ ^ (2:ℝ≥0∞).toReal * ‖f‖ ^ (2:ℝ≥0∞).toReal :=
        mul_le_mul_of_nonneg_left (lp.sum_rpow_le_norm_rpow hp f s)
          (Real.rpow_nonneg hd0 _)
    _ = (‖d‖ * ‖f‖) ^ (2:ℝ≥0∞).toReal := (Real.mul_rpow hd0 (norm_nonneg _)).symm

/-- The diagonal multiplication operator of `d ∈ ℓ∞(ℕ)`, as a linear map. -/
def diagLin (d : EllInf) : Ell2C →ₗ[ℂ] Ell2C where
  toFun f := ⟨fun i => (d : ℕ → ℂ) i * (f : ℕ → ℂ) i, memℓp_diag_two d f⟩
  map_add' f g := by
    apply lp.ext
    funext i
    simp [mul_add]
    rfl
  map_smul' c f := by
    apply lp.ext
    funext i
    simp [mul_left_comm]

@[simp] theorem diagLin_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagLin d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem norm_diagLin_le (d : EllInf) (f : Ell2C) : ‖diagLin d f‖ ≤ ‖d‖ * ‖f‖ := by
  have hp : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_forall_sum_le hp (by positivity) fun s => ?_
  have h1 : ∀ i ∈ s, ‖((diagLin d f : Ell2C) : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ‖d‖ ^ (2:ℝ≥0∞).toReal * ‖(f : ℕ → ℂ) i‖ ^ (2:ℝ≥0∞).toReal := by
    intro i _
    rw [diagLin_apply, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    gcongr
    exact norm_coord_le d i
  calc ∑ i ∈ s, ‖((diagLin d f : Ell2C) : ℕ → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑ i ∈ s, ‖d‖ ^ (2:ℝ≥0∞).toReal * ‖(f : ℕ → ℂ) i‖ ^ (2:ℝ≥0∞).toReal :=
        Finset.sum_le_sum h1
    _ = ‖d‖ ^ (2:ℝ≥0∞).toReal * ∑ i ∈ s, ‖(f : ℕ → ℂ) i‖ ^ (2:ℝ≥0∞).toReal := by
        rw [Finset.mul_sum]
    _ ≤ ‖d‖ ^ (2:ℝ≥0∞).toReal * ‖f‖ ^ (2:ℝ≥0∞).toReal :=
        mul_le_mul_of_nonneg_left (lp.sum_rpow_le_norm_rpow hp f s)
          (Real.rpow_nonneg (norm_nonneg _) _)
    _ = (‖d‖ * ‖f‖) ^ (2:ℝ≥0∞).toReal :=
        (Real.mul_rpow (norm_nonneg _) (norm_nonneg _)).symm

/-- **The diagonal multiplication operator** of a bounded sequence `d ∈ ℓ∞(ℕ)`:
a bounded operator on `ℓ²(ℕ)`, of norm at most `‖d‖`. -/
def diagOp (d : EllInf) : Ell2C →L[ℂ] Ell2C :=
  LinearMap.mkContinuous (diagLin d) ‖d‖ (fun f => norm_diagLin_le d f)





/-! ## `diagOp` is a faithful unital `*`-algebra map -/















/-! ## Maximal abelianness: the commutant of the diagonal algebra -/

/-- The coordinate atom `eᵢ ∈ ℓ²(ℕ)`. -/
def atom (i : ℕ) : Ell2C := lp.single 2 i (1 : ℂ)



/-- The coordinate projection, as a diagonal operator. -/
def coordUnit (i : ℕ) : EllInf := lp.single ∞ i (1 : ℂ)









end BookProof.ChapterAbelianDiagonalCountable

end


