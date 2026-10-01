-- Prove2me | Definitions.Def_burau_srule_defs3
-- name    : burau_srule_defs3
-- status  : Definition
-- author  : @lt9
-- created : 2026-10-01T07:04:57.540259+00:00
-- url     : https://prove2.me/theorems/af450fc3-869d-44f5-9552-060f3ca98431
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

theorem rhoIter_eq_rho (k : ℕ) (M : M2) (hk : (M 0 0).natAbs ≤ k) :
    rhoIter k M = rho M := by
  rw [rhoIter_eq_rhoIter k M hk]
  rfl

theorem mul_Sm_eq (M : M2) :
    M * Sm = ((M * Tm (-(M 0 1 / M 0 0))) * Sm) * Lm (-(M 0 1 / M 0 0)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sm, Tm, Lm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem Tm_det (a : ℤ) : (Tm a).det = 1 := by
  simp [Tm, Matrix.det_fin_two]

theorem rho_eq_rho_step (M : M2) (h0 : M 0 0 ≠ 0) :
    rho M = rho ((M * Tm (-(M 0 1 / M 0 0))) * Sm) * liftS⁻¹ * liftT ^ (M 0 1 / M 0 0) := by
  have hbud : (((M * Tm (-(M 0 1 / M 0 0))) * Sm) 0 0).natAbs ≤ (M 0 0).natAbs - 1 := by
    have h := euclid_decrease M h0
    omega
  have hN : (M 0 0).natAbs = ((M 0 0).natAbs - 1) + 1 := by
    have h : 1 ≤ (M 0 0).natAbs := Int.natAbs_pos.mpr h0
    omega
  rw [rho, hN]
  simp only [rhoIter, if_neg h0]
  rw [rhoIter_eq_rho ((M 0 0).natAbs - 1) _ hbud]

end BurauNC


