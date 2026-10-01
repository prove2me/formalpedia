-- Prove2me | Definitions.Def_burau_srule_defs2
-- name    : burau_srule_defs2
-- status  : Definition
-- author  : @lt9
-- created : 2026-10-01T06:37:30.652333+00:00
-- url     : https://prove2.me/theorems/dc47d786-76ab-42b9-9333-7c15b37cb18f
-- title:
--   Descent-recursion lemmas for the section rho
-- statement:
--   **One step of the Euclidean descent for the section $\rho$.** If $M_{00}\neq0$ then
--   $$\rho(M)=\rho\bigl((M\,T^{-n})S\bigr)\,\mathrm{liftS}^{-1}\,\mathrm{liftT}^{n},\qquad n=M_{01}/M_{00}.$$
--   This is the recursion the section is defined by, isolated as a reusable rewrite.
-- source:
--   Euclidean algorithm in SL(2,Z) and the reduced Burau representation; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_rho
import Definitions.Def_burau_srule_defs

set_option autoImplicit false

open Matrix

namespace BurauNC

theorem rhoIter_eq_rhoIter (j : ℕ) (M : M2) (hk : (M 0 0).natAbs ≤ j) :
    rhoIter j M = rhoIter ((M 0 0).natAbs) M := by
  revert M
  refine Nat.strong_induction_on j ?_
  intro j ih M hk
  match j with
  | 0 =>
      have h0 : M 0 0 = 0 := Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
      simp only [h0, Int.natAbs_zero]
  | k + 1 =>
      by_cases h0 : M 0 0 = 0
      · simp only [rhoIter, h0, Int.natAbs_zero, ↓reduceIte]
      · have hdec : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs < (M 0 0).natAbs :=
          euclid_decrease M h0
        have hle2 : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs ≤ (M 0 0).natAbs - 1 := by
          omega
        have hlt : (M 0 0).natAbs - 1 < k + 1 := by omega
        have hN : (M 0 0).natAbs = ((M 0 0).natAbs - 1) + 1 := by omega
        simp only [rhoIter, if_neg h0]
        rw [hN]
        simp only [rhoIter, if_neg h0]
        congr 1
        rw [ih k (by omega) (M * Tm (-(M 0 1 / M 0 0)) * Sm) (by omega),
          ih ((M 0 0).natAbs - 1) hlt (M * Tm (-(M 0 1 / M 0 0)) * Sm) hle2]

theorem mul_Sm_eq (M : M2) :
    M * Sm = ((M * Tm (-(M 0 1 / M 0 0))) * Sm) * Lm (-(M 0 1 / M 0 0)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, Tm, Lm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end BurauNC


