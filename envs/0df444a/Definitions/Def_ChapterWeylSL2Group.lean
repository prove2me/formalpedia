-- Prove2me | Definitions.Def_ChapterWeylSL2Group
-- name    : ChapterWeylSL2Group
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T07:07:57.125206+00:00
-- url     : https://prove2.me/theorems/347358b6-cde1-4fae-9cb7-7295670bb773
-- title:
--   Chapter WeylSL2Group
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterWeylSL2Group.lean`): generated def bundle for ChapterWeylSL2Group. See BookProof/ChapterWeylSL2Group.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterWeylSL2Group.lean

import Definitions.Def_ChapterWeylSl2
import Mathlib


/-!
# From `sl(2,ℂ)` to `SL(2,ℂ)`: Weyl's theorem for group representations

`BookProof.ChapterWeylSl2` proves Weyl's complete-reducibility theorem for the Lie algebra
`sl(2,ℂ)`.  This file transports it to representations of the **group** `SL(2,ℂ)` that are
differentiable in the sense that the two unipotent one-parameter subgroups

`u₊(t) = !![1, t; 0, 1]`,  `u₋(t) = !![1, 0; t, 1]`

act by the exponentials of the raising and lowering operators `E`, `F` of an `sl₂`-triple
(`IsExpOfSl2`).  Every finite-dimensional holomorphic representation of `SL(2,ℂ)` is of this
form, with the `sl₂`-triple being the differential of the representation.

The two ingredients are:

* `coeff_mem_of_poly_mem` — if all values of a polynomial curve `t ↦ ∑ tᵏ cₖ` lie in a
  subspace `W`, then so do all its coefficients (proved by pushing to `V ⧸ W` and using that
  a polynomial over `ℂ` vanishing identically is zero).  This turns invariance under the
  one-parameter groups into invariance under `E` and `F`.
* `exists_factorization` — every element of `SL(2,ℂ)` is a product of four elementary
  (unipotent) matrices, so invariance under `u₊` and `u₋` gives invariance under the whole
  group.

The conclusion is `weyl_complete_reducibility_SL2`: every invariant subspace of such a
representation has an invariant complement.  `rho_mem_of_unipotent_inv` is the group-level
half (invariance under the two unipotent subgroups already gives invariance under the whole
group), and `isInv_of_rho` the Lie-algebra half.

Finally `stdRep`, `stdSl2` and `isExpOfSl2_stdRep` exhibit the defining representation of
`SL(2,ℂ)` on `ℂ²` as an instance of the hypothesis, so the theorem is not vacuous.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterWeylSL2Group

open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-! ### Coefficients of a polynomial curve inside a subspace -/



/-! ### The unipotent one-parameter subgroups of `SL(2,ℂ)` -/

/-- The upper unipotent matrix `!![1, t; 0, 1]`. -/
def uPlus (t : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The lower unipotent matrix `!![1, 0; t, 1]`. -/
def uMinus (t : ℂ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two_of]⟩







/-! ### Representations that exponentiate an `sl₂`-triple -/

/-- A representation of `SL(2,ℂ)` **exponentiates** the `sl₂`-triple `R` (whose raising and
lowering operators are nilpotent of order at most `N`) when the two unipotent one-parameter
subgroups act by the exponential series of `E` and `F`.  This is exactly what the
differential of a finite-dimensional holomorphic representation of `SL(2,ℂ)` provides. -/
structure IsExpOfSl2 (rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (R : Sl2Rep V) (N : ℕ) : Prop where
  /-- Two terms of the exponential series are needed to see the generator. -/
  two_le : 2 ≤ N
  /-- The upper unipotent subgroup acts by `exp (t E)`. -/
  expE : ∀ t : ℂ, rho (uPlus t) = ∑ k ∈ Finset.range N, (t ^ k / (Nat.factorial k : ℂ)) • R.E ^ k
  /-- The lower unipotent subgroup acts by `exp (t F)`. -/
  expF : ∀ t : ℂ, rho (uMinus t) = ∑ k ∈ Finset.range N, (t ^ k / (Nat.factorial k : ℂ)) • R.F ^ k

variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}







/-! ### From the unipotent subgroups to the whole group -/



/-! ### Weyl's theorem for `SL(2,ℂ)` -/



/-! ### The hypothesis is satisfiable: the defining representation -/

/-- The raising matrix of `sl(2,ℂ)`. -/
def eMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]

/-- The lowering matrix of `sl(2,ℂ)`. -/
def fMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]

/-- The Cartan matrix of `sl(2,ℂ)`. -/
def hMat : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The defining representation of `SL(2,ℂ)` on `ℂ²`. -/
def stdRep : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) (Fin 2 → ℂ) where
  toFun g := Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) ℂ)
  map_one' := by
    ext v i
    simp
  map_mul' g h := by
    ext v i
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_apply]

/-- The `sl₂`-triple of the defining representation. -/
def stdSl2 : Sl2Rep (Fin 2 → ℂ) where
  E := Matrix.toLin' eMat
  F := Matrix.toLin' fMat
  H := Matrix.toLin' hMat
  he := by
    have hm : hMat * eMat - eMat * hMat = eMat + eMat := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hMat, eMat]
    have hL := congrArg Matrix.toLin' hm
    rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul, map_add] at hL
    rw [two_nsmul]
    exact hL
  hf := by
    have hm : hMat * fMat - fMat * hMat = -(fMat + fMat) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hMat, fMat]
      ring1
    have hL := congrArg Matrix.toLin' hm
    rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul, map_neg, map_add] at hL
    rw [two_nsmul]
    exact hL
  hef := by
    have hm : eMat * fMat - fMat * eMat = hMat := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hMat, eMat, fMat]
    have hL := congrArg Matrix.toLin' hm
    rw [map_sub, Matrix.toLin'_mul, Matrix.toLin'_mul] at hL
    exact hL



end BookProof.ChapterWeylSL2Group


