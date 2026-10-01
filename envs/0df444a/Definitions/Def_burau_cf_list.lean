-- Prove2me | Definitions.Def_burau_cf_list
-- name    : burau_cf_list
-- status  : Definition
-- author  : @lt9
-- created : 2026-09-30T23:24:34.438845+00:00
-- url     : https://prove2.me/theorems/1af342f6-9003-4f0f-85e5-ed3123607357
-- title:
--   The matrix descent and quotient list cfList of the continued-fraction section
-- statement:
--   **The matrix descent behind the continued-fraction section of $\mathrm{SL}(2,\mathbb Z)$.**
--
--   For $2\times2$ integer matrices the definition node provides the two elementary matrices
--   $$ S=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad T(n)=\begin{pmatrix}1&n\\0&1\end{pmatrix}, $$
--   the Euclidean descent step $M\mapsto (M\cdot T^{-n})\cdot S$ with $n=M_{01}/M_{00}$, the measure lemma
--   showing that the new $(0,0)$-entry is $M_{01}\bmod M_{00}$ and hence strictly smaller in absolute value
--   (so the recursion terminates), and the recorded quotient list
--   $$ \mathtt{cfList}(M)=\begin{cases}[] & M_{00}=0,\\ \dfrac{M_{01}}{M_{00}} :: \mathtt{cfList}\bigl((M T^{-n})S\bigr) & \text{else,}\end{cases} $$
--   with its recursion and terminating-case lemmas. This is the combinatorial skeleton of the descent section
--   $\rho$ of the reduced braid quotient $Q$, and its agreement with the integer recursion `cfPair` is the
--   statement proved in the companion nodes.
-- source:
--   Euclidean algorithm in SL(2,Z); cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3; J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Mathlib

set_option autoImplicit false

open Matrix

namespace BurauNC

abbrev M2 := Matrix (Fin 2) (Fin 2) ℤ

/-- `S = !![0,-1;1,0]` (matrix form). -/
def Sm : M2 := !![0, -1; 1, 0]

/-- `T^n = !![1,n;0,1]` (matrix form). -/
def Tm (n : ℤ) : M2 := !![1, n; 0, 1]


theorem euclid_decrease (M : M2) (h : M 0 0 ≠ 0) :
    (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs < (M 0 0).natAbs := by
  have hkey : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0) = M 0 1 % M 0 0 := by
    rw [Tm, Sm]
    simp [Matrix.mul_apply, Fin.sum_univ_two, Int.emod_def]
    ring
  rw [hkey, Int.natAbs_lt_iff_sq_lt]
  exact sq_lt_sq.mpr ((abs_of_nonneg (Int.emod_nonneg (M 0 1) h)).trans_lt
    (Int.emod_lt_abs (M 0 1) h))

noncomputable def cfList : M2 → List ℤ
  | M => if h : M 0 0 = 0 then []
    else (M 0 1 / M 0 0) :: cfList ((M * Tm (-(M 0 1 / M 0 0))) * Sm)
termination_by M => (M 0 0).natAbs
decreasing_by exact euclid_decrease M h

theorem cfList_cons (M : M2) (h : M 0 0 ≠ 0) :
    cfList M = (M 0 1 / M 0 0) :: cfList ((M * Tm (-(M 0 1 / M 0 0))) * Sm) := by
  rw [cfList.eq_def]
  exact dif_neg h

theorem cfList_eq_nil (M : M2) (h : M 0 0 = 0) : cfList M = [] := by
  rw [cfList.eq_def]
  exact dif_pos h

end BurauNC


