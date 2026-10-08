-- Prove2me | Definitions.Def_WardropTraffic_MeanSpeed_Setting
-- name    : WardropTraffic_MeanSpeed_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:00.029804+00:00
-- url     : https://prove2.me/theorems/382dbb6d-b250-474c-8e36-c2ba33096c1b
-- title:
--   Equations (1)–(3), (7): traffic-stream flow, concentration, speed means, and space variance
-- statement:
--   A traffic stream consists of a finite positive number $C$ of subsidiary streams. Stream $i$ has positive flow $q_i$ and positive speed $v_i$. Its **concentration** is $k_i=q_i/v_i$; total flow and concentration are $Q=\sum_i q_i$ and $K=\sum_i k_i$. The time and space frequencies are $f_i=q_i/Q$ and $f'_i=k_i/K$.
--
--   The **time-mean speed** and **space-mean speed** are
--
--   $$\bar v_t=\frac{\sum_i q_i v_i}{Q},\qquad \bar v_s=\frac{\sum_i k_i v_i}{K}.$$
--
--   The space-distribution variance is defined independently by
--
--   $$\sigma_s^2=\frac{\sum_i k_i(v_i-\bar v_s)^2}{K}.$$
--
--   Its standard deviation is $\sigma_s=\sqrt{\sigma_s^2}$ and its coefficient of variation is $c_s=\sigma_s/\bar v_s$. The ordered-speed overtaking count per unit road length and time is $\sum_{i<j} k_i k_j(v_j-v_i)$.
--
--   These definitions are the common model for the speed-mean, sampling, and overtaking statements. Positivity of $C$, $q_i$, and $v_i$ is required in the theorems using the means; the definitions themselves are total real functions in Lean.
-- source:
--   Wardrop, Some theoretical aspects of road traffic research, Proc. Instn Civ. Engrs Part II 1 (1952), pp. 327–331, (1)–(3), (7); pp. 333–334, (9)–(10)

import Mathlib
noncomputable section

namespace WardropTraffic.MeanSpeed

/-- Concentration of subsidiary stream i, equation (1). -/
def conc {C : ℕ} (q v : Fin C → ℝ) (i : Fin C) : ℝ := q i / v i

/-- Total flow Q. -/
def totalFlow {C : ℕ} (q : Fin C → ℝ) : ℝ := ∑ i, q i

/-- Total concentration K. -/
def totalConc {C : ℕ} (q v : Fin C → ℝ) : ℝ := ∑ i, conc q v i

/-- Frequency of stream i among vehicles passing a point. -/
def timeFreq {C : ℕ} (q : Fin C → ℝ) (i : Fin C) : ℝ := q i / totalFlow q

/-- Frequency of stream i among vehicles occupying road space. -/
def spaceFreq {C : ℕ} (q v : Fin C → ℝ) (i : Fin C) : ℝ :=
  conc q v i / totalConc q v

/-- Time-mean speed, equation (2). -/
def timeMean {C : ℕ} (q v : Fin C → ℝ) : ℝ :=
  (∑ i, q i * v i) / totalFlow q

/-- Space-mean speed, equation (3). -/
def spaceMean {C : ℕ} (q v : Fin C → ℝ) : ℝ :=
  (∑ i, conc q v i * v i) / totalConc q v

/-- Variance of the space distribution, equation (7). -/
def spaceVar {C : ℕ} (q v : Fin C → ℝ) : ℝ :=
  (∑ i, conc q v i * (v i - spaceMean q v) ^ 2) / totalConc q v

/-- Standard deviation of the space distribution. -/
def spaceSD {C : ℕ} (q v : Fin C → ℝ) : ℝ := Real.sqrt (spaceVar q v)

/-- Coefficient of variation of the space distribution. -/
def spaceCV {C : ℕ} (q v : Fin C → ℝ) : ℝ := spaceSD q v / spaceMean q v

/-- Number of overtakings per unit road length and time, in the ordered-speed model. -/
def overtakingRate {C : ℕ} (q v : Fin C → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then conc q v i * conc q v j * (v j - v i) else 0

end WardropTraffic.MeanSpeed


