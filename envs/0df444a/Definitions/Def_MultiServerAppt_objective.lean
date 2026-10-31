-- Prove2me | Definitions.Def_MultiServerAppt_objective
-- name    : MultiServerAppt_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:21.847694+00:00
-- url     : https://prove2.me/theorems/6d67a87a-6bca-4043-bd34-e4bfcb6ad19b
-- title:
--   The objective (20) through the matrices
-- statement:
--   The value at the schedule $x$ of the objective of Eq. (20), written with the formulas of §4.2 alone. With $n=s+m$ and $f(t)=\alpha_n\exp(S_nt)(-S_n\mathbf 1)$,
--
--   $$c_I\Big(s\big(-\alpha_nS_n^{-1}\mathbf 1+t_n\big)-n\big(-\alpha S^{-1}\mathbf 1\big)\Big)+\sum_{i=1}^{m}-\alpha_i^{\mathrm{wait}}(S_i^{\mathrm{wait}})^{-1}\mathbf 1+c_O\,s\int_0^\infty\max\{t+t_n-T,0\}f(t)\,\mathrm dt.$$
--
--   **Formalization Note** $-\alpha S^{-1}\mathbf 1$ is the phase-type mean of $B_i$, and $f$ is the density of $F_{M_n}$.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eqs. (17)-(20), pp.14-15, 17

import Mathlib
import Definitions.Def_MultiServerAppt_pVec
import Definitions.Def_MultiServerAppt_waitMat
import Definitions.Def_MultiServerAppt_waitAlpha
import Definitions.Def_MultiServerAppt_arr

open Matrix MeasureTheory

namespace MultiServerAppt

/-- The value at the schedule `x` of the objective (20), written with the formulas of §4.2 only:
Eq. (18) with `E M_n = -α_n S_n⁻¹ 𝟙`, Eq. (17), and Eq. (19). Kuiper–Lee, Appointment Scheduling for
Multiple Servers, SSRN 3975471, Eqs. (17)-(20), pp.14-15, 17.

**Formalization Note** `n = s + m`, and `-α S⁻¹ 𝟙` is the phase-type mean of `B_i`, so `∑ E B_i` of
Eq. (18) is `n` times it. `f t = α_n exp(S_n t) t_n` is the density of `F_{M_n}`, which replaces the
Stieltjes `dF_{M_n}` of Eq. (19). -/
noncomputable def objective {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ)
    (S : Matrix ι ι ℝ) (s m : ℕ) (x : ℕ → ℝ) (T cI cO : ℝ) : ℝ :=
  cI * ((s : ℝ) * (-(alphaSys α S s x m ⬝ᵥ ((sysMat α S s m)⁻¹ *ᵥ fun _ => (1 : ℝ))) +
        arr s x (s + m)) -
      ((s + m : ℕ) : ℝ) * (-(α ⬝ᵥ (S⁻¹ *ᵥ fun _ => (1 : ℝ))))) +
  ∑ i ∈ Finset.Icc 1 m,
    (-(waitAlpha α S s x i ⬝ᵥ ((waitMat α S s i)⁻¹ *ᵥ fun _ => (1 : ℝ)))) +
  cO * ((s : ℝ) * ∫ t in Set.Ioi (0 : ℝ),
    max (t + arr s x (s + m) - T) 0 *
      (alphaSys α S s x m ᵥ* NormedSpace.exp (t • sysMat α S s m)) ⬝ᵥ
        MatrixAnalytic.PH.exitRates (sysMat α S s m))

end MultiServerAppt


