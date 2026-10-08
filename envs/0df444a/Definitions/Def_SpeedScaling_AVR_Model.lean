-- Prove2me | Definitions.Def_SpeedScaling_AVR_Model
-- name    : SpeedScaling_AVR_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:43.953296+00:00
-- url     : https://prove2.me/theorems/060744a2-e06a-4521-8eb3-8fdec3281383
-- title:
--   Scheduling instances, feasible schedules, energy, intensity, and average rate
-- statement:
--   The model has finitely many jobs in a fixed, nondegenerate window $[t_0,t_1]$. Job $j$ arrives at $a_j$, has deadline $b_j>a_j$, and requires $R_j\ge 0$ cycles. Its whole window lies inside $[t_0,t_1]$. A schedule specifies a nonnegative processor speed and at most one assigned job at each time, both constant between finitely many breakpoints. It is feasible when each job receives exactly $R_j$ cycles in its window.
--
--   For a power function $P$, energy is $E_P(S)=\int_{t_0}^{t_1}P(s(t))\,dt$. The intensity of $[z,z']$ is the work of jobs wholly contained in it divided by $z'-z$; a critical interval maximizes this quantity among subintervals of $[t_0,t_1]$. Each job's density is $d_j=R_j/(b_j-a_j)$, extended as a step function on its window. The quadratic average-rate cost is
--   $$\operatorname{AVR}(J)=\int_{t_0}^{t_1}\bigl(\sum_jd_j(t)\bigr)^2\,dt.$$
--
--   These definitions provide the common model for all results in the mission. The formalization also defines the analogous cost for a real exponent $p$.
-- source:
--   Yao, Demers & Shenker, A scheduling model for reduced CPU energy, Proc. 36th IEEE FOCS (1995), DOI 10.1109/SFCS.1995.492493, p. 375, §§2–3 and Eq. (2) on p. 376.

import Mathlib

namespace SpeedScaling.AVR
noncomputable section
open MeasureTheory
open scoped Classical

/-- A finite set of jobs in a nondegenerate time window. -/
structure Instance (n : ℕ) where
  t0 : ℝ
  t1 : ℝ
  ht : t0 < t1
  a : Fin n → ℝ
  b : Fin n → ℝ
  R : Fin n → ℝ
  ha : ∀ j, t0 ≤ a j
  hab : ∀ j, a j < b j
  hb : ∀ j, b j ≤ t1
  hR : ∀ j, 0 ≤ R j

/-- A speed and an assignment of at most one job at each time. -/
structure Schedule (n : ℕ) where
  s : ℝ → ℝ
  job : ℝ → Option (Fin n)

/-- The speed and assignment are constant between finitely many breakpoints. -/
def IsSchedule {n : ℕ} (J : Instance n) (S : Schedule n) : Prop :=
  (∀ t ∈ Set.Icc J.t0 J.t1, 0 ≤ S.s t) ∧
  ∃ m : ℕ, ∃ τ : Fin (m + 1) → ℝ,
    0 < m ∧ StrictMono τ ∧ τ 0 = J.t0 ∧ τ (Fin.last m) = J.t1 ∧
    ∀ k : Fin m, (∃ v : ℝ, ∀ t ∈ Set.Ioo (τ k.castSucc) (τ k.succ), S.s t = v) ∧
      (∃ q : Option (Fin n), ∀ t ∈ Set.Ioo (τ k.castSucc) (τ k.succ), S.job t = q)

/-- The portion of the processor speed assigned to job `j`. -/
def execSpeed {n : ℕ} (S : Schedule n) (j : Fin n) (t : ℝ) : ℝ :=
  S.s t * if S.job t = some j then 1 else 0

/-- Each job receives its required work inside its own window. -/
def Feasible {n : ℕ} (J : Instance n) (S : Schedule n) : Prop :=
  ∀ j, (∫ t in J.a j..J.b j, execSpeed S j t) = J.R j

/-- Energy for a given power function. -/
def energy {n : ℕ} (P : ℝ → ℝ) (J : Instance n) (S : Schedule n) : ℝ :=
  ∫ t in J.t0..J.t1, P (S.s t)

/-- An optimal schedule among all admissible feasible schedules. -/
def IsOptimal {n : ℕ} (P : ℝ → ℝ) (J : Instance n) (S : Schedule n) : Prop :=
  IsSchedule J S ∧ Feasible J S ∧
    ∀ S', IsSchedule J S' → Feasible J S' → energy P J S ≤ energy P J S'

/-- Average work per unit time of one job. -/
def density {n : ℕ} (J : Instance n) (j : Fin n) : ℝ :=
  J.R j / (J.b j - J.a j)

/-- The job's average-rate step function. -/
def densityFun {n : ℕ} (J : Instance n) (j : Fin n) (t : ℝ) : ℝ :=
  if t ∈ Set.Icc (J.a j) (J.b j) then density J j else 0

/-- Equation (2): quadratic energy of the average-rate speed. -/
def AVR {n : ℕ} (J : Instance n) : ℝ :=
  ∫ t in J.t0..J.t1, (∑ j : Fin n, densityFun J j t) ^ 2

/-- Average-rate energy for a real power exponent. -/
def AVRp (p : ℝ) {n : ℕ} (J : Instance n) : ℝ :=
  ∫ t in J.t0..J.t1, (∑ j : Fin n, densityFun J j t) ^ p

/-- Work density of jobs whose entire windows lie in `[z,z']`. -/
def intensity {n : ℕ} (J : Instance n) (z z' : ℝ) : ℝ :=
  (∑ j ∈ Finset.univ.filter (fun j : Fin n => z ≤ J.a j ∧ J.b j ≤ z'), J.R j) / (z' - z)

/-- An intensity-maximizing nondegenerate interval within the instance window. -/
def IsCriticalInterval {n : ℕ} (J : Instance n) (z z' : ℝ) : Prop :=
  J.t0 ≤ z ∧ z < z' ∧ z' ≤ J.t1 ∧
    ∀ y y', J.t0 ≤ y → y < y' → y' ≤ J.t1 →
      intensity J y y' ≤ intensity J z z'

end
end SpeedScaling.AVR


