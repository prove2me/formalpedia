-- Prove2me | Definitions.Def_ModernConvex_FinsetSchur
-- name    : ModernConvex_FinsetSchur
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:06:31.855196+00:00
-- url     : https://prove2.me/theorems/0321152e-56c3-4ef3-a357-2ae3d0442d71
-- title:
--   The Schur step on an arbitrary finite index set
-- statement:
--   **The Schur step on an arbitrary finite index set.**
--
--   `schurStep` eliminates one coordinate of a matrix indexed by $\mathrm{Fin}\,n$, producing a matrix indexed by the complement subtype $\{j : j\ne i\}$. To *iterate* the elimination the index set shrinks at each step, so this file states the step for a matrix indexed by an arbitrary `Finset s`: eliminating `i ∈ s` leaves a matrix indexed by `s.erase i`,
--   $$(\texttt{schurStepS}\ M\ i)_{jk}=M_{jk}-M_{ji}M_{ii}^{-1}M_{ik}\qquad(j,k\in s\setminus\{i\}),$$
--   i.e. $M_{s\setminus\{i\},s\setminus\{i\}}-M_{s\setminus\{i\},i}M_{ii}^{-1}M_{i,s\setminus\{i\}}$.
--
--   `extendAtS i w` extends a vector on $s\setminus\{i\}$ by $0$ at $i$. `schurStepS_isHermitian` records that the step preserves symmetry, so the recursion may assume symmetry at every stage.
--
--   These are the data carried by the well-founded recursion of the PSD oracle: the index set loses one element per step, so `s.card` decreases and the recursion is well founded.
-- source:
--   Schur complement / symmetric elimination at a 1x1 pivot, on an arbitrary finite index set; data for the recursive PSD oracle of the MAXCUT SDP separation problem.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurStep

/-!
# The Schur step on an arbitrary finite index set

`schurStep` eliminates one coordinate of a matrix indexed by `Fin n`. To *iterate* the elimination
the index set shrinks each time, so this file states the step for a matrix indexed by an arbitrary
`Finset s`: eliminating `i ∈ s` leaves a matrix indexed by `s.erase i`. The recursion of the PSD
oracle descends on `s.card` along these steps.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- The Schur complement at the pivot `i ∈ s`, as a matrix on `s.erase i`. -/
noncomputable def schurStepS {n : ℕ} {s : Finset (Fin n)} (M : Matrix s s ℝ) (i : s) :
    Matrix (s.erase i) (s.erase i) ℝ :=
  fun j k =>
    M ⟨j.1, Finset.mem_of_mem_erase j.2⟩ ⟨k.1, Finset.mem_of_mem_erase k.2⟩
      - M ⟨j.1, Finset.mem_of_mem_erase j.2⟩ i * (M i i)⁻¹
        * M i ⟨k.1, Finset.mem_of_mem_erase k.2⟩

/-- Extend a vector on `s.erase i` by zero at `i`. -/
def extendAtS {n : ℕ} {s : Finset (Fin n)} (i : s) (w : (s.erase i) → ℝ) : s → ℝ :=
  fun j => if h : (j : Fin n) = (i : Fin n) then 0
    else w ⟨j.1, Finset.mem_erase.mpr ⟨h, j.2⟩⟩

@[simp] theorem extendAtS_self {n : ℕ} {s : Finset (Fin n)} (i : s)
    (w : (s.erase i) → ℝ) : extendAtS i w i = 0 := by
  simp [extendAtS]

theorem extendAtS_of_ne {n : ℕ} {s : Finset (Fin n)} (i : s) (w : (s.erase i) → ℝ)
    {j : s} (hj : (j : Fin n) ≠ (i : Fin n)) :
    extendAtS i w j = w ⟨j.1, Finset.mem_erase.mpr ⟨hj, j.2⟩⟩ := by
  simp [extendAtS, hj]

/-- **The Schur step preserves symmetry.** -/
theorem schurStepS_isHermitian {n : ℕ} {s : Finset (Fin n)} {M : Matrix s s ℝ}
    (hM : M.IsHermitian) (i : s) : (schurStepS M i).IsHermitian := by
  have hsymm : ∀ j : s, M j i = M i j := by
    intro j
    simpa using (hM.apply j i).symm
  ext j k
  simp only [schurStepS, Matrix.conjTranspose_apply, star_trivial]
  have h1 : M ⟨k.1, Finset.mem_of_mem_erase k.2⟩ ⟨j.1, Finset.mem_of_mem_erase j.2⟩
      = M ⟨j.1, Finset.mem_of_mem_erase j.2⟩ ⟨k.1, Finset.mem_of_mem_erase k.2⟩ := by
    simpa using (hM.apply ⟨k.1, Finset.mem_of_mem_erase k.2⟩
      ⟨j.1, Finset.mem_of_mem_erase j.2⟩).symm
  rw [h1, hsymm ⟨k.1, Finset.mem_of_mem_erase k.2⟩, hsymm ⟨j.1, Finset.mem_of_mem_erase j.2⟩]
  ring

end ModernConvex.Relaxations


