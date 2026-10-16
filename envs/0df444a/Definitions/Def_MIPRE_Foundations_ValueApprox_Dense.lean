-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
-- name    : MIPRE_Foundations_ValueApprox_Dense
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:09:00.298625+00:00
-- url     : https://prove2.me/theorems/a5271547-6975-4ddd-989b-e1a0b676fd13
-- title:
--   Gaussian-rational unitaries and projective measurements are dense
-- statement:
--   This bundle contributes no definitions and two theorems, the density half of `lem:value-lower-approx` (blueprint `lem:rational-pvm-dense`), for a finite index type $n$ with decidable equality and complex $n \times n$ matrices in the $L^{2}$ operator norm.
--
--   `MIPRE.ValueApprox.exists_unitary_entriesIn_norm_smul_sub_le`: for every unitary $U$ (an element of `Matrix.unitaryGroup n ℂ`) and every $\eta > 0$ there are a unit scalar $z \in \mathbb{C}$, $\|z\| = 1$, and a unitary $V$ with entries in $\mathbb{Q}(i)$ (`EntriesIn GaussianRat V`) such that
--   $$\|z\,U - V\| \le \eta .$$
--   Up to a unit phase, every unitary is within $\eta$ of a Gaussian-rational unitary.
--
--   `MIPRE.ValueApprox.IsPVM.exists_entriesIn_norm_sub_le`: for every family `M : A → Matrix n n ℂ` with `IsPVM M` ($A$ a finite type with decidable equality) and every $\eta > 0$ there is a family $M'$ with `IsPVM M'`, every $M'_a$ having entries in $\mathbb{Q}(i)$, and $\|M_a - M'_a\| \le \eta$ for every outcome $a$: every projective measurement is within $\eta$, element by element, of a projective measurement with Gaussian-rational entries.
--
--   As the module docstring records, the first theorem is the Cayley transform of an entrywise rounding of the skew-Hermitian Cayley preimage of $zU$, and the second conjugates the coordinate pattern of `IsPVM.exists_unitary_pattern` by the approximating unitary; both feed the density of exact strategies in the bundle `MIPRE_Foundations_ValueApprox_Strategy`.
--
--   **Formalization Note**. This is the point where the Lean route departs from the paper's: the paper rounds the measurement operators themselves and repairs the result into a POVM (its Claims "Stability" and "Density"), whereas here the rounding happens at the level of the skew-Hermitian generator, so that the rounded object is an exact projective measurement and no repair is needed. The phase $z$ is present because $1 + U$ need not be invertible; a suitable unit scalar always makes $1 + zU$ invertible, and conjugation by $zU$ is conjugation by $U$, which is why the second statement carries no phase. Both bounds are non-strict, in the operator norm `Matrix.Norms.L2Operator`, with $\eta > 0$ strict.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/Dense.lean; blueprint lem:rational-pvm-dense

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/Dense.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms

/-!
# Gaussian-rational unitaries and projective measurements are dense

* `exists_unitary_entriesIn_norm_smul_sub_le`: up to a unit phase, every unitary is within `η`
  (in operator norm) of a unitary with Gaussian-rational entries — the Cayley transform of an
  entrywise rounding of the skew-Hermitian Cayley preimage;
* `IsPVM.exists_entriesIn_norm_sub_le`: every projective measurement is within `η`, element by
  element, of a projective measurement with Gaussian-rational entries — conjugate the coordinate
  pattern of `IsPVM.exists_unitary_pattern` by the approximating unitary.

This is the density half of `lem:value-lower-approx`, and the point where the Lean route departs
from the paper's: the paper rounds the measurement operators themselves and repairs the result
into a POVM (its Claims "Stability" and "Density"); here the rounding happens at the level of the
skew-Hermitian generator, so that the rounded object is an exact projective measurement and no
repair is needed.
-/

namespace MIPRE.ValueApprox

open Matrix
open scoped Matrix.Norms.L2Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Up to a unit phase `z`, every unitary `U` is within `η` of a Gaussian-rational unitary. -/
theorem exists_unitary_entriesIn_norm_smul_sub_le {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ V : Matrix n n ℂ, V ∈ Matrix.unitaryGroup n ℂ ∧
      EntriesIn GaussianRat V ∧ ‖z • U - V‖ ≤ η := by
  obtain ⟨z, hz, hz1⟩ := exists_norm_eq_one_isUnit_one_add_smul U
  obtain ⟨S, hS, hSU⟩ := exists_isSkewHermitian_cayley_eq (smul_mem_unitaryGroup hU hz) hz1
  have hδ : 0 < η / (2 * (Fintype.card n + 1)) := by positivity
  obtain ⟨T, hT, hTK, hTη⟩ := hS.exists_entriesIn_norm_sub_le hδ
  refine ⟨z, hz, cayley T, cayley_mem_unitaryGroup hT, hTK.cayley, ?_⟩
  have hST : ‖S - T‖ ≤ η / 2 := by
    have hc : (0 : ℝ) ≤ Fintype.card n := by positivity
    calc ‖S - T‖ ≤ Fintype.card n * (η / (2 * (Fintype.card n + 1))) :=
          l2_opNorm_le_card_mul_of_entry_le hδ.le fun i j => by
            rw [Matrix.sub_apply]
            exact hTη i j
      _ ≤ η / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  calc ‖z • U - cayley T‖ = ‖cayley S - cayley T‖ := by rw [hSU]
    _ ≤ 2 * ‖S - T‖ := norm_cayley_sub_cayley_le hS hT
    _ ≤ 2 * (η / 2) := by gcongr
    _ = η := by ring

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Every projective measurement is within `η`, element by element, of a projective measurement
with Gaussian-rational entries. -/
theorem IsPVM.exists_entriesIn_norm_sub_le {M : A → Matrix n n ℂ} (hM : IsPVM M) {η : ℝ}
    (hη : 0 < η) :
    ∃ M' : A → Matrix n n ℂ, IsPVM M' ∧ (∀ a, EntriesIn GaussianRat (M' a)) ∧
      ∀ a, ‖M a - M' a‖ ≤ η := by
  obtain ⟨U, r, hUr⟩ := hM.exists_unitary_pattern
  obtain ⟨z, hz, V, hV, hVK, hVη⟩ :=
    exists_unitary_entriesIn_norm_smul_sub_le U.2 (half_pos hη)
  refine ⟨fun a => V * patternProj r a * Vᴴ, (isPVM_patternProj r).conj ⟨V, hV⟩, fun a =>
    (hVK.mul (EntriesIn.patternProj r a)).mul (hVK.conjTranspose fun _ => GaussianRat.star_mem),
    fun a => ?_⟩
  rw [hUr a, Matrix.star_eq_conjTranspose,
    ← smul_mul_mul_conjTranspose_smul (U : Matrix n n ℂ) (patternProj r a) hz]
  calc ‖z • (U : Matrix n n ℂ) * patternProj r a * (z • (U : Matrix n n ℂ))ᴴ -
        V * patternProj r a * Vᴴ‖
      ≤ 2 * ‖z • (U : Matrix n n ℂ) - V‖ :=
        norm_mul_mul_conjTranspose_sub_le
          (norm_le_one_of_mem_unitaryGroup (smul_mem_unitaryGroup U.2 hz))
          (norm_le_one_of_mem_unitaryGroup hV) ((isPVM_patternProj r).norm_le_one a)
    _ ≤ 2 * (η / 2) := by gcongr
    _ = η := by ring

end MIPRE.ValueApprox


