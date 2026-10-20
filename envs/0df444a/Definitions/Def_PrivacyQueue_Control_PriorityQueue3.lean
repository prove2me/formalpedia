-- Prove2me | Definitions.Def_PrivacyQueue_Control_PriorityQueue3
-- name    : PrivacyQueue_Control_PriorityQueue3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:38.130432+00:00
-- url     : https://prove2.me/theorems/37e835ec-a6df-411a-a412-b5f8dd51e78d
-- title:
--   Three-class preemptive-priority queue: H > N > L
-- statement:
--   A **three-class preemptive-priority queue** has classes $H>N>L$. For each class $i$, let $B_i$ be its mean service time, $R_i$ its mean residual service time, and $\rho_i$ its workload. The class waiting times used in the paper are the mean times in the system:
--
--   $$
--   W_H=\frac{\rho_HR_H}{1-\rho_H}+B_H,\qquad
--   W_N=\frac{\rho_HR_H+\rho_NR_N}{(1-\rho_H-\rho_N)(1-\rho_H)}+\frac{B_N}{1-\rho_H},
--   $$
--   $$
--   W_L=\frac{\rho_HR_H+\rho_NR_N+\rho_LR_L}{(1-\rho_H-\rho_N-\rho_L)(1-\rho_H-\rho_N)}+\frac{B_L}{1-\rho_H-\rho_N}.
--   $$
--
--   This interface separates the general queueing calculation from the paper's disclosure-dependent class parameters.
--
--   **Formalization Note** The formulas are algebraic definitions over $\mathbb R$. Their use as finite expected times requires positive load denominators, supplied by the paper-specific standing assumptions and $\gamma\in[0,1]$ in the theorem items.
-- source:
--   Hu, Momot & Wang, Privacy Management in Service Systems, submitted manuscript (draft of 12 Feb 2022; SSRN 3628751), Online Appendix p. 1 (PDF 35), A.1, citing Adan and Resing (2015), Ch. 9.2

import Mathlib

namespace PrivacyQueue.Control

/-- Mean service times, mean residual service times, and loads for three
preemptive priority classes ordered H > N > L. -/
structure PriorityQueue3 where
  BH : ℝ
  BN : ℝ
  BL : ℝ
  RH : ℝ
  RN : ℝ
  RL : ℝ
  rhoH : ℝ
  rhoN : ℝ
  rhoL : ℝ

/-- Mean time in the system for the highest-priority class. -/
noncomputable def PriorityQueue3.waitH (Q : PriorityQueue3) : ℝ :=
  Q.rhoH * Q.RH / (1 - Q.rhoH) + Q.BH

/-- Mean time in the system for the middle-priority class. -/
noncomputable def PriorityQueue3.waitN (Q : PriorityQueue3) : ℝ :=
  (Q.rhoH * Q.RH + Q.rhoN * Q.RN) /
      ((1 - Q.rhoH - Q.rhoN) * (1 - Q.rhoH)) + Q.BN / (1 - Q.rhoH)

/-- Mean time in the system for the lowest-priority class. -/
noncomputable def PriorityQueue3.waitL (Q : PriorityQueue3) : ℝ :=
  (Q.rhoH * Q.RH + Q.rhoN * Q.RN + Q.rhoL * Q.RL) /
      ((1 - Q.rhoH - Q.rhoN - Q.rhoL) * (1 - Q.rhoH - Q.rhoN)) +
      Q.BL / (1 - Q.rhoH - Q.rhoN)

end PrivacyQueue.Control


