-- Prove2me | Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
-- name    : MIPRE_Foundations_ValueApprox_Projective
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:07:12.15513+00:00
-- url     : https://prove2.me/theorems/8e817134-232c-40ea-8d98-1c925ed18a96
-- title:
--   Projective measurements on $\mathbb{C}^n$ are coordinate patterns in a unitary frame
-- statement:
--   Let $n$ be a finite index type with decidable equality and $A$ a finite outcome type. `MIPRE.ValueApprox.IsPVM M`, for a family `M : A → Matrix n n ℂ`, is a `Prop`-valued structure with three fields: `conjTranspose_eq`, $(M_a)^{\mathsf H} = M_a$; `mul_self`, $M_a M_a = M_a$; and `sum_eq_one`, $\sum_a M_a = 1$ — the measurement operators of one question of a projective measurement on $\mathbb{C}^{n}$. `MIPRE.ValueApprox.patternProj r a`, for an outcome pattern $r : n \to A$ (with $A$ having decidable equality), is the diagonal matrix projecting onto the coordinates $i$ with $r(i) = a$:
--   $$\mathrm{patternProj}(r)_a = \mathrm{diag}\bigl(i \mapsto [\,r(i) = a\,]\bigr).$$
--
--   The embedded lemmas: `dotProduct_conjTranspose_mul_self`, $\langle v, N^{\mathsf H}N v\rangle = \langle Nv, Nv\rangle$; `ProjectiveMeasurement.isPVM`, the operators of a `MIPRE.ProjectiveMeasurement` on a matrix algebra at any question form an `IsPVM`; `IsPVM.conj`, conjugation $M_a \mapsto U M_a U^{*}$ by a unitary $U$ preserves `IsPVM`; `IsPVM.mul_eq_zero`, distinct outcomes are orthogonal, $M_b M_a = 0$ for $a \ne b$; `isPVM_patternProj`, every pattern family is an `IsPVM`; and the structure theorem `IsPVM.exists_unitary_pattern`: for every `IsPVM M` there are a unitary $U$ (an element of `Matrix.unitaryGroup n ℂ`) and a pattern $r : n \to A$ with $M_a = U\,\mathrm{patternProj}(r)_a\,U^{*}$ for every $a$. So a projective measurement is exactly "a unitary and a pattern", and enumerating unitaries with Gaussian-rational entries together with patterns enumerates exact projective measurements, the route to approximating the quantum value from below without approximate POVMs, matrix square roots or Naimark dilation (blueprint `lem:rational-pvm-dense`).
--
--   **Formalization Note**. `IsPVM` is stated for an arbitrary indexed family rather than for the bundled `MIPRE.ProjectiveMeasurement`, so that it can be asserted of the raw data of an enumerated candidate (`ExactStrategy.IsValid` in the strategy bundle); the unitary of the structure theorem is an element of the subtype `Matrix.unitaryGroup n ℂ` coerced to a matrix, and `star U` is its conjugate transpose. `patternProj` and the lemmas from `IsPVM.conj` on assume `DecidableEq A`; `IsPVM` itself and `ProjectiveMeasurement.isPVM` do not.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/ValueApprox/Projective.lean; blueprint lem:rational-pvm-dense

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/ValueApprox/Projective.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games

/-!
# Projective measurements on `ℂ^n` are coordinate patterns in a unitary frame

The measurement operators `{M a}` of one question of a projective measurement on `ℂ^n`
(`MIPRE.ProjectiveMeasurement` on `Matrix n n ℂ`) are commuting orthogonal projections
summing to the identity. This file proves the structure theorem behind the enumeration of
`lem:value-lower-approx`: there are a unitary `U` and an outcome pattern `r : n → A` with

  `M a = U * diagonal (fun i => if r i = a then 1 else 0) * Uᴴ`

for every outcome `a` (`IsPVM.exists_unitary_pattern`). So a projective measurement is
exactly "a unitary and a pattern", and enumerating unitaries with Gaussian-rational entries
together with patterns enumerates *exact* projective measurements — the route to
approximating the quantum value from below without approximate POVMs, matrix square roots
or Naimark dilation.

The proof diagonalizes the single Hermitian matrix `H = ∑ a, w a • M a` for distinct real
weights `w`: an eigenvector `u` of `H` with eigenvalue `λ` satisfies
`(w a - λ) • M a u = 0`, so `M a u = 0` unless `λ = w a`, and `∑ a, M a u = u ≠ 0` forces
`λ = w a` for exactly one `a`, which is the pattern at `u`.
-/

namespace MIPRE.ValueApprox

open Matrix
open scoped ComplexOrder

/-- `⟨v, Nᴴ N v⟩ = ⟨N v, N v⟩`. -/
theorem dotProduct_conjTranspose_mul_self {n : Type*} [Fintype n] (N : Matrix n n ℂ)
    (v : n → ℂ) : star v ⬝ᵥ ((Nᴴ * N) *ᵥ v) = star (N *ᵥ v) ⬝ᵥ (N *ᵥ v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Type*} [Fintype A]

/-- The measurement operators of one question of a projective measurement on `ℂ^n`:
self-adjoint idempotents summing to the identity. -/
structure IsPVM (M : A → Matrix n n ℂ) : Prop where
  /-- Each operator is self-adjoint. -/
  conjTranspose_eq : ∀ a, (M a)ᴴ = M a
  /-- Each operator is idempotent. -/
  mul_self : ∀ a, M a * M a = M a
  /-- The operators sum to the identity. -/
  sum_eq_one : ∑ a, M a = 1

/-- The operators of a `ProjectiveMeasurement` on a matrix algebra, at a question `x`. -/
theorem _root_.MIPRE.ProjectiveMeasurement.isPVM {X : Type*}
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) : IsPVM (P.M x) :=
  ⟨fun a => P.selfAdjoint x a, fun a => P.projective x a, P.normalized x⟩

variable [DecidableEq A]

namespace IsPVM

variable {M : A → Matrix n n ℂ}

omit [DecidableEq A] in
/-- Conjugating by a unitary preserves the structure. -/
theorem conj (hM : IsPVM M) (U : Matrix.unitaryGroup n ℂ) :
    IsPVM fun a => (U : Matrix n n ℂ) * M a * star (U : Matrix n n ℂ) where
  conjTranspose_eq a := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, star_eq_conjTranspose,
      hM.conjTranspose_eq, Matrix.mul_assoc]
  mul_self a := by
    have h := Matrix.UnitaryGroup.star_mul_self U
    calc (U : Matrix n n ℂ) * M a * star (U : Matrix n n ℂ) *
          ((U : Matrix n n ℂ) * M a * star (U : Matrix n n ℂ))
        = (U : Matrix n n ℂ) * M a * (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) * M a *
            star (U : Matrix n n ℂ) := by simp only [Matrix.mul_assoc]
      _ = (U : Matrix n n ℂ) * M a * star (U : Matrix n n ℂ) := by
        rw [h, Matrix.mul_one, Matrix.mul_assoc _ (M a) (M a), hM.mul_self]
  sum_eq_one := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, hM.sum_eq_one, Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff.mp U.2

/-- Distinct outcomes are orthogonal: `M b * M a = 0` for `a ≠ b`. -/
theorem mul_eq_zero (hM : IsPVM M) {a b : A} (hab : a ≠ b) : M b * M a = 0 := by
  -- `M a = ∑ c, M a * M c * M a`, so the terms with `c ≠ a` sum to zero; each is
  -- `(M c * M a)ᴴ * (M c * M a)`, positive semidefinite, hence each vanishes.
  have hsum : ∑ c ∈ Finset.univ.erase a, M a * M c * M a = 0 := by
    have h1 : ∑ c, M a * M c * M a = M a := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hM.sum_eq_one, Matrix.mul_one, hM.mul_self]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), Matrix.mul_assoc, hM.mul_self,
      hM.mul_self] at h1
    exact add_left_cancel (h1.trans (add_zero (M a)).symm)
  have hterm : ∀ c, M a * M c * M a = (M c * M a)ᴴ * (M c * M a) := fun c => by
    rw [conjTranspose_mul, hM.conjTranspose_eq, hM.conjTranspose_eq]
    calc M a * M c * M a = M a * (M c * M c) * M a := by rw [hM.mul_self]
      _ = M a * M c * (M c * M a) := by simp only [Matrix.mul_assoc]
  -- Apply the quadratic form at an arbitrary vector `v`.
  have hv : ∀ v : n → ℂ, (M b * M a) *ᵥ v = 0 := by
    intro v
    have h0 : ∑ c ∈ Finset.univ.erase a,
        star ((M c * M a) *ᵥ v) ⬝ᵥ ((M c * M a) *ᵥ v) = 0 := by
      have := congrArg (fun N : Matrix n n ℂ => star v ⬝ᵥ (N *ᵥ v)) hsum
      simp only [Matrix.sum_mulVec, dotProduct_sum, zero_mulVec, dotProduct_zero, hterm,
        dotProduct_conjTranspose_mul_self] at this
      exact this
    have hnonneg : ∀ c ∈ Finset.univ.erase a,
        0 ≤ star ((M c * M a) *ᵥ v) ⬝ᵥ ((M c * M a) *ᵥ v) := fun c _ =>
      dotProduct_star_self_nonneg _
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h0 b
      (Finset.mem_erase.mpr ⟨fun h => hab h.symm, Finset.mem_univ b⟩)
    exact (dotProduct_star_self_eq_zero).mp hzero
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  rwa [mulVec_single_one] at this

end IsPVM

/-- The coordinate pattern projections of `r : n → A`: `patternProj r a` projects onto the
coordinates `i` with `r i = a`. -/
def patternProj (r : n → A) (a : A) : Matrix n n ℂ :=
  diagonal fun i => if r i = a then 1 else 0

theorem isPVM_patternProj (r : n → A) : IsPVM (patternProj r) where
  conjTranspose_eq a := by
    unfold patternProj
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : r i = a <;> simp [h]
  mul_self a := by
    unfold patternProj
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : r i = a <;> simp [h]
  sum_eq_one := by
    ext i j
    simp only [Matrix.sum_apply, patternProj, diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]

namespace IsPVM

variable {M : A → Matrix n n ℂ}

/-- **Structure theorem.** A projective measurement on `ℂ^n` is a coordinate pattern in a
unitary frame: `M a = U * patternProj r a * Uᴴ` for a unitary `U` and a pattern `r`. -/
theorem exists_unitary_pattern (hM : IsPVM M) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (r : n → A),
      ∀ a, M a = (U : Matrix n n ℂ) * patternProj r a * star (U : Matrix n n ℂ) := by
  classical
  -- distinct real weights, and the Hermitian matrix `H = ∑ a, w a • M a`
  obtain ⟨w, hw⟩ : ∃ w : A → ℝ, Function.Injective w :=
    ⟨fun a => ((Fintype.equivFin A a : ℕ) : ℝ), fun a b h =>
      (Fintype.equivFin A).injective (Fin.ext (Nat.cast_injective h))⟩
  set H : Matrix n n ℂ := ∑ a, ((w a : ℝ) : ℂ) • M a with hH_def
  have hH : H.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [hH_def, conjTranspose_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [conjTranspose_smul, hM.conjTranspose_eq]
    simp
  -- `M a * H = w a • M a`
  have hMH : ∀ a, M a * H = ((w a : ℝ) : ℂ) • M a := fun a => by
    rw [hH_def, Finset.mul_sum]
    rw [Finset.sum_eq_single a]
    · rw [mul_smul_comm, hM.mul_self]
    · intro b _ hba
      rw [mul_smul_comm, hM.mul_eq_zero hba, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  set U := hH.eigenvectorUnitary with hU_def
  set u : n → n → ℂ := fun j => ⇑(hH.eigenvectorBasis j) with hu_def
  set lam : n → ℝ := hH.eigenvalues with hlam_def
  have hHu : ∀ j, H *ᵥ u j = ((lam j : ℝ) : ℂ) • u j := fun j => by
    show H *ᵥ ⇑(hH.eigenvectorBasis j) = ((hH.eigenvalues j : ℝ) : ℂ) • ⇑(hH.eigenvectorBasis j)
    rw [hH.mulVec_eigenvectorBasis j]
    funext i
    simp [Complex.real_smul]
  -- `(w a - lam j) • M a u_j = 0`
  have hkey : ∀ a j, lam j ≠ w a → M a *ᵥ u j = 0 := fun a j hne => by
    have h1 : M a *ᵥ (H *ᵥ u j) = ((w a : ℝ) : ℂ) • (M a *ᵥ u j) := by
      rw [mulVec_mulVec, hMH, Matrix.smul_mulVec]
    have h2 : M a *ᵥ (H *ᵥ u j) = ((lam j : ℝ) : ℂ) • (M a *ᵥ u j) := by
      rw [hHu, mulVec_smul]
    have h3 : (((w a : ℝ) : ℂ) - ((lam j : ℝ) : ℂ)) • (M a *ᵥ u j) = 0 := by
      rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd (by exact_mod_cast (sub_eq_zero.mp h).symm) hne
    · exact h
  -- the eigenvectors are nonzero
  have hu_ne : ∀ j, u j ≠ 0 := fun j h => by
    have hnorm := hH.eigenvectorBasis.orthonormal.1 j
    have : hH.eigenvectorBasis j = 0 := by
      apply WithLp.ofLp_injective
      simpa [hu_def] using h
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  -- every eigenvalue is some `w a`, uniquely
  have hexists : ∀ j, ∃ a, lam j = w a := fun j => by
    by_contra hcon
    simp only [not_exists] at hcon
    apply hu_ne j
    have hsum : ∑ a, M a *ᵥ u j = u j := by
      rw [← Matrix.sum_mulVec, hM.sum_eq_one, one_mulVec]
    rw [← hsum]
    exact Finset.sum_eq_zero fun a _ => hkey a j (hcon a)
  choose r hr using hexists
  refine ⟨U, r, fun a => ?_⟩
  -- `M a *ᵥ u j = if r j = a then u j else 0`
  have hMu : ∀ j, M a *ᵥ u j = if r j = a then u j else 0 := fun j => by
    split_ifs with hja
    · have hsum : ∑ b, M b *ᵥ u j = u j := by
        rw [← Matrix.sum_mulVec, hM.sum_eq_one, one_mulVec]
      rw [Finset.sum_eq_single a] at hsum
      · exact hsum
      · intro b _ hba
        apply hkey b j
        rw [hr j, hja]
        exact fun h => hba (hw h).symm
      · intro h
        exact absurd (Finset.mem_univ a) h
    · exact hkey a j (by rw [hr j]; exact fun h => hja (hw h))
  -- assemble: `M a * U = U * patternProj r a`, then multiply by `Uᴴ`
  have hMU : M a * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * patternProj r a := by
    ext i j
    have hcol : (fun k => (U : Matrix n n ℂ) k j) = u j := by
      funext k
      simp [hU_def, hu_def, Matrix.IsHermitian.eigenvectorUnitary_apply]
    rw [Matrix.mul_apply, patternProj, mul_diagonal]
    have : ∑ k, M a i k * (U : Matrix n n ℂ) k j = (M a *ᵥ u j) i := by
      rw [← hcol]
      rfl
    rw [this, hMu j]
    split_ifs <;> simp [hcol.symm]
  calc M a = M a * (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) := by
        rw [Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff.mp U.2, Matrix.mul_one]
    _ = (U : Matrix n n ℂ) * patternProj r a * star (U : Matrix n n ℂ) := by rw [hMU]

end IsPVM

end MIPRE.ValueApprox


