-- Prove2me | Definitions.Def_burau_srule_defs
-- name    : burau_srule_defs
-- status  : Definition
-- author  : @lt9
-- created : 2026-10-01T06:17:50.959327+00:00
-- url     : https://prove2.me/theorems/3105f5c7-6d44-40ca-9ffa-2f4319b16a22
-- title:
--   Matrix generators L^k and the S-rule reductions
-- statement:
--   **The $L$-rule from the $S$-rule.** For a unimodular $2\times2$ integer matrix $X$, an integer
--   $k$, and $S=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$,
--   $L^k=\left(\begin{smallmatrix}1&0\\k&1\end{smallmatrix}\right)$: if the descent section $\rho$ is
--   multiplicative against $S$ both at $X$ and at $X L^k$, then it is multiplicative against $L^k$,
--   $$ \rho\bigl(X L^k\bigr) = \rho(X)\cdot \mathrm{liftS}^{-1}\,\mathrm{liftT}^{-k}\,\mathrm{liftS}. $$
--   The proof is the conjugation identity $L^k = S^{-1}T^{-k}S$ together with the already-established
--   $T$-rule $\rho(YT^j)=\rho(Y)\mathrm{liftT}^j$ and the symmetry
--   $\mathrm{liftS}\,\mathrm{liftT}^n\mathrm{liftS}^{-1}=\mathrm{liftS}^{-1}\mathrm{liftT}^n\mathrm{liftS}$.
--   This reformulates the milestone's $S$-rule as a one-parameter $L$-rule, which is the shape in which
--   the induction on the Euclidean descent is run.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_cf_list

set_option autoImplicit false

open Matrix

namespace BurauNC

noncomputable def Lm (k : ℤ) : M2 := !![1, 0; k, 1]

theorem Lm_mul_zero_zero (d : ℤ) (M : M2) : (Lm (-d) * M) 0 0 = M 0 0 := by
  simp [Lm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Lm_mul_zero_one (d : ℤ) (M : M2) : (Lm (-d) * M) 0 1 = M 0 1 := by
  simp [Lm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Sm_mul_Tm (d : ℤ) : Sm * Tm d = Lm (-d) * Sm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, Tm, Lm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Sm_det_eq_one : Sm.det = 1 := by simp [Sm, Matrix.det_fin_two]

end BurauNC


