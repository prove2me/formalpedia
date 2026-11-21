-- Prove2me | Definitions.Def_MasulloAudit_TruncConv
-- name    : MasulloAudit_TruncConv
-- status  : Definition
-- author  : @lll
-- created : 2026-11-21T00:27:13.586271+00:00
-- url     : https://prove2.me/theorems/f6ab8202-ca50-4c0c-a03c-33c3a530bdaa
-- title:
--   Truncated convolution operators on $\ell^2(\mathbb Z)$
-- statement:
--   Let $\ell^2(\mathbb Z)$ denote the Hilbert space of square-summable complex sequences $x=(x_n)_{n\in\mathbb Z}$ with norm $\|x\|=\big(\sum_{n\in\mathbb Z}|x_n|^2\big)^{1/2}$. This file introduces three families of bounded linear operators on $\ell^2(\mathbb Z)$.
--
--   1. **Shifts.** For $k\in\mathbb Z$, the shift $S_k$ is
--   $$
--   (S_k x)_n = x_{n-k}\qquad(n\in\mathbb Z).
--   $$
--   It is an isometry: $\|S_k x\|=\|x\|$.
--
--   2. **Truncation.** The truncation $T_{\le 0}$ keeps the coordinates with non-positive index and sets the others to zero:
--   $$
--   (T_{\le 0}x)_n=\begin{cases}x_n,& n\le 0,\\ 0,& n>0,\end{cases}
--   $$
--   so $\|T_{\le0}x\|\le\|x\|$. It is the discrete analogue of multiplication by the indicator $\mathbf 1_{(-\infty,L]}$.
--
--   3. **Truncated convolution.** For a finitely supported sequence $a=(a_k)_{k\in\mathbb Z}$ (only finitely many $a_k\neq0$),
--   $$
--   \mathrm{TC}_a \;=\; T_{\le 0}\circ\sum_{k\in\operatorname{supp}a} a_k\,S_k,\qquad (\mathrm{TC}_a x)_n=\begin{cases}\displaystyle\sum_{k\in\operatorname{supp}a} a_k\,x_{n-k},& n\le 0,\\ 0,& n>0.\end{cases}
--   $$
--   In other words, $\mathrm{TC}_a x=\mathbf 1_{\{n\le0\}}\cdot(a*x)$.
--
--   The operator $\mathrm{TC}_a$ is a discrete model of a one-sided multiplicative cutoff composed with a convolution operator, as in the cutoff extension discussed in footnote 2, p. 514 of Masullo's draft (compare the operator $P_{\rho,\lambda}\circ A_{\widetilde\varphi}\circ\widehat P_{\rho,\lambda'}$ on pp. 516-517). It is used to state that such one-sided cutoffs do not produce compact operators.
--
--   **Formalization Note** In Lean, $\ell^2(\mathbb Z)$ is `L2Z := lp (fun _ : ℤ => ℂ) 2`. The operators are `shiftCLM k`, `truncCLM` and `truncConv a` for `a : ℤ →₀ ℂ`, all of type `L2Z →L[ℂ] L2Z`; shift and truncation are built from linear maps via `mkContinuous` with bound $1$. The file also proves the isometry identity for shifts and the coordinate formula `truncConv_apply` displayed above.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, footnote 2 on p. 514 and the operator $P_{\rho,\lambda}\circ A_{\widetilde\varphi}\circ\widehat P_{\rho,\lambda'}$ on pp. 516-517; cf. A. Connes, Selecta Math. 5 (1999), §VII.

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Data.Finsupp.Defs

/-!
# Truncated convolution operators on `ℓ²(ℤ)`

Shift operators `S_k x = x(· - k)`, the truncation `T_{≤0}` to indices `n ≤ 0`, and the
truncated convolution `T_{≤0} ∘ ∑_k a_k S_k` for finitely supported `a : ℤ →₀ ℂ`.
-/

namespace MasulloAudit

/-- `ℓ²(ℤ)` with complex coefficients. -/
noncomputable abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

lemma two_toReal_pos : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num

lemma memℓp_shift (k : ℤ) (x : L2Z) : Memℓp (fun n => x (n - k)) 2 := by
  rw [memℓp_gen_iff two_toReal_pos]
  exact (Equiv.subRight k).summable_iff.mpr ((lp.memℓp x).summable two_toReal_pos)

/-- Shift by `k`: `(S_k x) n = x (n - k)`. -/
noncomputable def shiftL (k : ℤ) : L2Z →ₗ[ℂ] L2Z where
  toFun x := ⟨fun n => x (n - k), memℓp_shift k x⟩
  map_add' x y := by ext n; simp; rfl
  map_smul' c x := by ext n; simp

lemma norm_shiftL (k : ℤ) (x : L2Z) : ‖shiftL k x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow two_toReal_pos, lp.norm_eq_tsum_rpow two_toReal_pos]
  congr 1
  exact (Equiv.subRight k).tsum_eq (fun m => ‖x m‖ ^ (2 : ENNReal).toReal)

/-- The shift `S_k` as a bounded operator on `ℓ²(ℤ)`. -/
noncomputable def shiftCLM (k : ℤ) : L2Z →L[ℂ] L2Z :=
  (shiftL k).mkContinuous 1 fun x => by rw [one_mul, norm_shiftL]

/-- Truncation to indices `n ≤ 0` (discrete analogue of multiplying by `1_{(-∞, L]}`). -/
noncomputable def truncL : L2Z →ₗ[ℂ] L2Z where
  toFun x := ⟨fun n => if n ≤ 0 then x n else 0,
    (lp.memℓp x).mono' fun n => by split_ifs <;> simp⟩
  map_add' x y := by ext n; simp only [lp.coeFn_add, Pi.add_apply]; split_ifs <;> simp
  map_smul' c x := by ext n; simp only [lp.coeFn_smul, Pi.smul_apply]; split_ifs <;> simp

/-- The truncation `T_{≤0}` as a bounded operator on `ℓ²(ℤ)`. -/
noncomputable def truncCLM : L2Z →L[ℂ] L2Z :=
  truncL.mkContinuous 1 fun x => by
    rw [one_mul]
    refine lp.norm_mono (by norm_num) fun n => ?_
    change ‖(if n ≤ 0 then x n else 0)‖ ≤ ‖x n‖
    split_ifs <;> simp

/-- The truncated convolution operator `x ↦ 1_{n ≤ 0} · (a * x)` on `ℓ²(ℤ)`. -/
noncomputable def truncConv (a : ℤ →₀ ℂ) : L2Z →L[ℂ] L2Z :=
  truncCLM ∘L ∑ k ∈ a.support, a k • shiftCLM k

/-- `truncConv a` really is truncation composed with convolution by `a`. -/
theorem truncConv_apply (a : ℤ →₀ ℂ) (x : L2Z) (n : ℤ) :
    truncConv a x n = if n ≤ 0 then ∑ k ∈ a.support, a k * x (n - k) else 0 := by
  change (if n ≤ 0 then ((∑ k ∈ a.support, a k • shiftCLM k) x) n else 0) = _
  congr 1
  rw [FunLike.coe_sum, Finset.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  rfl

end MasulloAudit


