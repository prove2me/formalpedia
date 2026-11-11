-- Prove2me | Definitions.Def_SwitchingStable_Universal_Counts
-- name    : SwitchingStable_Universal_Counts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:16.297225+00:00
-- url     : https://prove2.me/theorems/bac702b9-87c8-4bc0-8f4d-9e6706e97bbe
-- title:
--   Actual occurrence counts and the Appendix E count identity
-- statement:
--   Fix a direction and sum all occurrences over the entire stable set. Write $r_0,r_1,e,s,f_a,w,b,t_0,d_0,d_1,e_{\rm adj},b_E,b_W,b_C,b_3$ for the counts of the corresponding classes and source occurrences. In particular,
--   $$N=r_0+r_1+e+s+f_a+w+b,\qquad d=d_0+d_1,\qquad c=r_0-t_0-d_0.$$
--   The file defines $L_0$, the transported increment, the weight sum $P_0$, the full expression $Q$, and the fourteen-term decomposition of $Q-\vartheta N$, exactly as in the proof of Theorem 1 and the unnumbered Appendix E display “The exact count identity”. The exceptional coefficient $B_C$ is distinguished from the exceptional occurrence class and its count $b_C$.
--
--   Counts are computed from the market; they are not free optimization variables. Real casts and signed differences preserve the source's subtraction formulas.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 5–7, 10–12, 28, PDF pp. 6–8, 11–13, 29, Sections 3, 5 and Appendix E, The exact count identity (unnumbered)

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Model
import Definitions.Def_SwitchingStable_Universal_Constants

namespace SwitchingStable.Universal
open StableMatching

/-- Actual occurrence counts in Section 3; c,d,N are derived to avoid truncated subtraction. -/
structure Counts where
  r0 : ℝ
  r1 : ℝ
  e : ℝ
  s : ℝ
  fa : ℝ
  w : ℝ
  b : ℝ
  t0 : ℝ
  d0 : ℝ
  d1 : ℝ
  eadj : ℝ
  bE : ℝ
  bW : ℝ
  bC : ℝ
  b3 : ℝ
noncomputable def occurrenceCounts {n : ℕ} (I : Instance n) (ε : Direction) : Counts where
  r0 := count I (fun μ u => R0 I μ ε u)
  r1 := count I (fun μ u => R1 I μ ε u)
  e := count I (fun μ u => E I μ ε u)
  s := count I (fun μ u => S I μ ε u)
  fa := count I (fun μ u => Fa I μ ε u)
  w := count I (fun μ u => W I μ ε u)
  b := count I (fun μ u => B I μ ε u)
  t0 := count I (fun μ u => T0 I μ ε u)
  d0 := count I (fun μ u => D0 I μ ε u)
  d1 := count I (fun μ u => D1 I μ ε u)
  eadj := count I (fun μ u => Eadj I μ ε u)
  bE := count I (fun μ u => badE I μ ε u)
  bW := count I (fun μ u => badW I μ ε u)
  bC := count I (fun μ u => Exceptional I μ ε u)
  b3 := count I (fun μ u => Failure I μ ε u)
def Counts.c (v : Counts) : ℝ := v.r0 - v.t0 - v.d0
def Counts.d (v : Counts) : ℝ := v.d0 + v.d1
def Counts.N (v : Counts) : ℝ := v.r0 + v.r1 + v.e + v.s + v.fa + v.w + v.b
noncomputable def Counts.L0 (v : Counts) : ℝ :=
  alpha*v.r0 + eta*v.r1 + delta 2*v.e + sigma*v.s + delta 2*v.d +
  (zeta-delta 2)*v.eadj + gamma*v.w + delta 2*v.t0 + (lambda+delta 2)*v.d0 +
  delta 2*(v.c-v.bC) + delta 2*v.fa
noncomputable def Counts.extra (v : Counts) : ℝ :=
  (gamma+delta 4)*(v.e-v.eadj-v.bE) + (delta 4+delta 5)*(v.w-v.bW) +
  gamma*v.t0 - (gamma+delta 4+delta 5)*v.b3
noncomputable def Counts.P0 (v : Counts) : ℝ :=
  omega 1*v.r0 + omega 2*(v.e+v.fa) + omega 3*v.w - omega 1*(v.r1+v.s+v.b) -
  2*omega 1*v.d0 - (omega 1+omega 2)*v.eadj
noncomputable def Counts.Q (v : Counts) : ℝ :=
  v.L0 + v.extra + v.P0 - xi*(v.bC+v.bE+v.bW+v.fa) -
  psi*(v.c+v.fa+v.bE+v.bW+3*v.b3)
/-- Appendix E, the unnumbered exact count identity's right-hand side. -/
noncomputable def Counts.decomposition (v : Counts) : ℝ :=
  coeffA 1*(v.r0-v.e) + coeffA 2*(v.r1-v.fa-v.bC) + coeffA 3*(v.t0+v.r1-v.w-v.b) +
  coeffA 4*(v.eadj+v.fa+v.s+v.d-v.b) + coeffA 5*(v.c-v.bC) +
  coeffA 6*(v.r0-v.t0-v.bE) + coeffA 7*(v.bE-v.bW) + coeffA 8*(v.d0+v.fa-v.b3) +
  coeffB 0*v.s + coeffB 1*v.fa + coeffB 2*v.d0 + coeffB 3*v.d1 +
  coeffB 4*v.eadj + coeffB 5*v.bC

noncomputable def occurrenceType {n : ℕ} (I : Instance n) (μ : Matching n)
    (ε : Direction) (u : Fin n) : ℕ := by
  classical
  exact if R0 I μ ε u ∧ ¬ D0 I μ ε u then 1 else
    if (E I μ ε u ∧ ¬ Eadj I μ ε u) ∨ Fa I μ ε u then 2 else
    if W I μ ε u then 3 else 0

end SwitchingStable.Universal


