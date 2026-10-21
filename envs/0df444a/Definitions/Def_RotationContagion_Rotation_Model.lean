-- Prove2me | Definitions.Def_RotationContagion_Rotation_Model
-- name    : RotationContagion_Rotation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:53.884976+00:00
-- url     : https://prove2.me/theorems/f06ebdbe-c31c-415c-af6c-7e16b01c2683
-- title:
--   §2–§2.1, pp. 5–8 — rotation schedules, logistic prevalence (2) in integral form, exposure time, ℓ and b, the rotation problem (P1)
-- statement:
--   This file sets up the rotation problem of Ely, Galeotti and Steiner.
--
--   An organization consists of two groups $i \in \{0,1\}$, each of measure $K > 1$. At each time one group is active and the other isolated. The **parameters** are the transmission rate $\gamma > 0$, the group size $K > 1$ and the reaction delay $R \ge 0$; together these are the **standing assumptions**.
--
--   1. A **rotation schedule** is a pair of measurable functions $r(0,\cdot), r(1,\cdot) : \mathbb R \to [0,1]$ with $r(0,t) + r(1,t) = 1$ for every $t$; $r(i,t)$ is the share of time group $i$ is active near $t$. The **frequent rotation** is $r(i,t) = 1/2$ for both $i$ and all $t$; the schedule **activating group $i$ throughout** is $r(i,t) = 1$, $r(1-i,t) = 0$.
--   2. At a random time $t^* \ge 0$ with law $\mu$, one group $\omega$, equally likely to be either and independent of $t^*$, is infected with initial prevalence $1/K$. A **prevalence path** of the infected group after an infection at $t^*$ is a function $p$, continuous and $[0,1]$-valued on $[t^*,\infty)$, solving equation (2)
--   $$\dot p_t = \gamma\, r(\omega,t)\, p_t\,(1-p_t), \qquad p_{t^*} = 1/K,$$
--   in integral form: $p_t = 1/K + \int_{t^*}^{t} \gamma\, r(\omega,s)\, p_s (1-p_s)\, ds$ for all $t \ge t^*$. A **prevalence family** gives such a path for every group $\omega$ and every infection time $t^* \ge 0$.
--   3. The **exposure time** of group $\omega$ is $\tau = \int_{t^*}^{t^*+R} r(\omega,t)\,dt$.
--   4. The **loss** and the **summary parameter** are
--   $$\ell(t) = \frac{e^{\gamma(t-b)}}{1+e^{\gamma(t-b)}}, \qquad b = \frac{1}{\gamma}\ln(K-1),$$
--   and the **relaxed objective** of (P2) is $\ell(\tau) + \ell(R-\tau)$.
--   5. The objective of the **rotation problem (P1)** is the expected terminal prevalence $\mathrm E\, p^\omega_{t^*+R}(\omega) = \tfrac12 \sum_{\omega} \int p^{\omega,t^*}_{t^*+R}\, d\mu(t^*)$. A schedule $r$ is **optimal** if it is a schedule, it has a prevalence family, and for every prevalence family of $r$ and every schedule $r'$ with any prevalence family, the objective under $r$ is at most that under $r'$.
--
--   These objects are shared by every statement of the mission; Proposition 1 is a statement about optimality in (P1).
--
--   **Formalization Note** Groups are `Fin 2`. Schedules are defined on all of $\mathbb R$ rather than on $\mathbb R_+$: values before $0$ never enter (P1) because $t^* \ge 0$, and every schedule on $\mathbb R_+$ extends. Measurability of $r$ is added because the page integrates $r$; $R \ge 0$ and $t^* \ge 0$ are added (a delay; schedules live on $\mathbb R_+$). Equation (2) is used in integral (Carathéodory) form because a measurable schedule gives a derivative only almost everywhere; this keeps the paper's periodic schedules of p. 6. Only the infected group's prevalence is modelled: the other group's stays at $0$ (p. 6) and does not enter (P1). Terminal prevalence is the value of the solution of (2), not $\ell(\tau)$; the link between the two is Lemma 1.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), pp. 5–8, §2, §2.1, equation (2), (P1), (P2); p. 11 (frequent and infrequent rotation)

import Mathlib

namespace RotationContagion.Rotation

open MeasureTheory

/-- Parameters of the rotation problem (§2, pp. 5–7): the transmission rate `γ`, the measure `K`
of each of the two groups, and the reaction delay `R`. -/
structure Params where
  /-- transmission rate `γ` in the logistic equation (2) -/
  γ : ℝ
  /-- measure `K` of each group -/
  K : ℝ
  /-- reaction delay `R` between the infection and the organization's reaction -/
  R : ℝ

/-- Standing assumptions of §2: `γ > 0` (p. 6), `K > 1` (p. 5), and `R ≥ 0` (added: `R` is a
delay, p. 7). -/
def Params.Standing (P : Params) : Prop := 0 < P.γ ∧ 1 < P.K ∧ 0 ≤ P.R

/-- The summary parameter `b = (1/γ) ln(K - 1)` (§2.1, p. 7). -/
noncomputable def b (P : Params) : ℝ := Real.log (P.K - 1) / P.γ

/-- The loss `ℓ(t) = e^{γ(t-b)} / (1 + e^{γ(t-b)})` (§2.1, p. 7). -/
noncomputable def loss (P : Params) (t : ℝ) : ℝ :=
  Real.exp (P.γ * (t - b P)) / (1 + Real.exp (P.γ * (t - b P)))

/-- The objective of the relaxed rotation problem (P2) (p. 8): `ℓ(τ) + ℓ(R - τ)`. -/
noncomputable def relaxedObj (P : Params) (τ : ℝ) : ℝ := loss P τ + loss P (P.R - τ)

/-- A rotation schedule (p. 6), with `Fin 2` for the groups `{0, 1}`: each `r i` is measurable,
takes values in `[0, 1]`, and `r 0 t + r 1 t = 1` at every time `t`. -/
def IsSchedule (r : Fin 2 → ℝ → ℝ) : Prop :=
  (∀ i, Measurable (r i)) ∧ ∀ t : ℝ, (∀ i, r i t ∈ Set.Icc (0 : ℝ) 1) ∧ r 0 t + r 1 t = 1

/-- The frequent rotation `r(i, t) = 1/2` for both `i` and all `t` (p. 11). -/
noncomputable def freqSched : Fin 2 → ℝ → ℝ := fun _ _ => 1 / 2

/-- The schedule activating group `i` at all times: `r(i, t) = 1`, `r(1 - i, t) = 0` (p. 11). -/
noncomputable def oneGroupSched (i : Fin 2) : Fin 2 → ℝ → ℝ := fun j _ => if j = i then 1 else 0

/-- `p` is the prevalence of the infected group `ω` under the schedule `r` after an infection at
time `t0`: continuous on `[t0, ∞)`, valued in `[0, 1]` there, and solving equation (2),
`ṗ = γ r(ω, t) p (1 - p)` with `p(t0) = 1/K`, in integral form. -/
def IsPrevalencePath (P : Params) (r : Fin 2 → ℝ → ℝ) (ω : Fin 2) (t0 : ℝ) (p : ℝ → ℝ) : Prop :=
  ContinuousOn p (Set.Ici t0) ∧
    (∀ t : ℝ, t0 ≤ t → p t ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ t : ℝ, t0 ≤ t → p t = 1 / P.K + ∫ s in t0..t, P.γ * r ω s * p s * (1 - p s)

/-- A family of prevalence paths: `p ω t0` is a prevalence path of the infected group `ω` after
an infection at `t0`, for every group `ω` and every infection time `t0 ≥ 0`. -/
def IsPrevalenceFamily (P : Params) (r : Fin 2 → ℝ → ℝ) (p : Fin 2 → ℝ → ℝ → ℝ) : Prop :=
  ∀ (ω : Fin 2) (t0 : ℝ), 0 ≤ t0 → IsPrevalencePath P r ω t0 (p ω t0)

/-- Exposure time `τ = ∫_{t0}^{t0+R} r(ω, t) dt` of group `ω` after an infection at `t0` (p. 7). -/
noncomputable def exposure (P : Params) (r : Fin 2 → ℝ → ℝ) (ω : Fin 2) (t0 : ℝ) : ℝ :=
  ∫ s in t0..t0 + P.R, r ω s

/-- The objective of (P1) (p. 7): the expected prevalence of the infected group at the reaction
time `t0 + R`, with `t0 ∼ μ` and `ω` uniform on `{0, 1}` independent of `t0`. -/
noncomputable def expectedTerminal (P : Params) (μ : Measure ℝ) (p : Fin 2 → ℝ → ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ ω : Fin 2, ∫ t0, p ω t0 (t0 + P.R) ∂μ

/-- `r` solves the rotation problem (P1) for the law `μ` of the infection time: `r` is a schedule,
it has a prevalence family, and for every prevalence family of `r` and every schedule `r'` with
any prevalence family, the expected terminal prevalence under `r` is at most that under `r'`. -/
def IsOptimal (P : Params) (μ : Measure ℝ) (r : Fin 2 → ℝ → ℝ) : Prop :=
  IsSchedule r ∧ (∃ p, IsPrevalenceFamily P r p) ∧
    ∀ p, IsPrevalenceFamily P r p →
      ∀ (r' : Fin 2 → ℝ → ℝ) (p' : Fin 2 → ℝ → ℝ → ℝ), IsSchedule r' →
        IsPrevalenceFamily P r' p' → expectedTerminal P μ p ≤ expectedTerminal P μ p'

end RotationContagion.Rotation


