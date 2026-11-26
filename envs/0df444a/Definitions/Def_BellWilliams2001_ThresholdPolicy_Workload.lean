-- Prove2me | Definitions.Def_BellWilliams2001_ThresholdPolicy_Workload
-- name    : BellWilliams2001_ThresholdPolicy_Workload
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T05:48:17.646246+00:00
-- url     : https://prove2.me/theorems/8f687c76-be4e-497a-a802-b5ee2edeae8a
-- title:
--   The centered renewal inputs, workload, and idle-time driver
-- statement:
--   The centered arrival and service processes are scaled by $r^{-1}$ in space and $r^2$ in time. The shifted two-dimensional input $\widehat X^r$ evaluates the service terms on the fluid allocation clocks and includes the two prelimit drift coefficients. The scalar workload and projected input use the weights $(1,\mu_2^r/\mu_3^r)$. Adding the weighted idle time of server 1 produces the input for the reflection associated with the idleness of server 2.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, equations (17)–(18), (23), (31)–(32), (96)–(97), (162)–(163)

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

namespace BellWilliams2001.ThresholdPolicy.SystemSequence

variable {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)

/-- The centered diffusion-scaled arrival primitive in equation (17). -/
noncomputable def Ahat (n : ℕ) (ω : Ω) (t : ℝ) (k : Fin 2) : ℝ :=
  (M.A n k ω (M.r n ^ 2 * t) - M.lamR n k * (M.r n ^ 2 * t)) / M.r n

/-- The centered diffusion-scaled service primitive in equation (18). -/
noncomputable def Shat (n : ℕ) (ω : Ω) (t : ℝ) (j : Fin 3) : ℝ :=
  (M.S n j ω (M.r n ^ 2 * t) - M.muR n j * (M.r n ^ 2 * t)) / M.r n

/-- The two drift coordinates of equations (23), (31), and (32). -/
noncomputable def driftR (n : ℕ) (k : Fin 2) : ℝ :=
  if k = 0 then M.r n * M.muR n 1 *
    ((M.lamR n 0 - M.muR n 0) / M.muR n 1 - (M.lam 0 - M.mu 0) / M.mu 1)
  else M.r n * M.muR n 2 * (M.lamR n 1 / M.muR n 2 - M.lam 1 / M.mu 2)

/-- The process `X̂^r` in equations (31) and (32), whose service coordinates are evaluated on
    the fluid time allocations. -/
noncomputable def Xhat (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) (k : Fin 2) : ℝ :=
  if k = 0 then M.Ahat n ω t 0 - M.Shat n ω (M.Tbar n T ω t 0) 0
    - M.Shat n ω (M.Tbar n T ω t 1) 1 + M.driftR n 0 * t
  else M.Ahat n ω t 1 - M.Shat n ω (M.Tbar n T ω t 2) 2 + M.driftR n 1 * t

/-- The class 2 workload weight in system `r` from equation (96). The class 1 weight is one. -/
noncomputable def poolingWeight (n : ℕ) : ℝ := M.muR n 1 / M.muR n 2

/-- The workload `Ŵ^r` in equation (96). -/
noncomputable def workload (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) : ℝ :=
  M.Qhat n T ω t 0 + M.poolingWeight n * M.Qhat n T ω t 1

/-- The diffusion input projected onto the one-dimensional pooled workload. -/
noncomputable def workloadInput (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) : ℝ :=
  M.Xhat n T ω t 0 + M.poolingWeight n * M.Xhat n T ω t 1

/-- The input for the server 2 reflection, with server 1 idle time included as in (162). -/
noncomputable def serverTwoInput (n : ℕ) (T : Allocation Ω) (ω : Ω) (t : ℝ) : ℝ :=
  M.workloadInput n T ω t + M.muR n 0 * M.Ihat n T ω t 0

end BellWilliams2001.ThresholdPolicy.SystemSequence


