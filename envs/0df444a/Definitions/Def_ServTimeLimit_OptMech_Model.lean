-- Prove2me | Definitions.Def_ServTimeLimit_OptMech_Model
-- name    : ServTimeLimit_OptMech_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:07.121889+00:00
-- url     : https://prove2.me/theorems/a11a2213-ac4e-40a4-a3b6-e4acaf94401b
-- title:
--   §3, §4, §7, pp. 6–19 — discretionary M/G/1 service: allocations, PK waiting time, first-best welfare, direct mechanisms with IC, IR and revenue
-- statement:
--   This file fixes the model of Feldman and Segev (§3, pp. 6–8) in its main case $\beta = 0$, together with the first-best program of §4 (p. 8) and the direct mechanisms of §7 (p. 19).
--
--   **Parameters.** Service needs arise as a Poisson process of rate $\Lambda$. A customer's type $\theta$ is her ideal time in service, uniformly distributed on $[0,\bar\theta]$; spending $t$ units of time in service is worth $v_\theta(t) = \min\{t,\theta\}$ to her. Customers pay a waiting cost $c$ per unit of expected waiting time. Standing assumptions: $\Lambda > 0$, $c > 0$, $\bar\theta > 0$.
--
--   **Allocations.** An allocation is a pair $(\Phi, t)$: a measurable admitted set $\Phi \subseteq [0,\bar\theta]$ and a measurable time function $t$ with $0 \le t(\theta) \le \theta$ for $\theta \in \Phi$; only the values of $t$ on $\Phi$ matter. Its expected waiting time is the Pollaczek–Khinchine formula specialised to uniform types,
--   $$W(\Phi, t) = \frac{\Lambda \int_\Phi t(\theta)^2\, d\theta}{2\left(\bar\theta - \Lambda \int_\Phi t(\theta)\, d\theta\right)},$$
--   and feasibility includes queue stability $\Lambda \int_\Phi t < \bar\theta$. Its social welfare is
--   $$SW(\Phi, t) = \frac{\Lambda}{\bar\theta} \int_\Phi \big(t(\theta) - c\,W(\Phi,t)\big)\, d\theta .$$
--   An allocation is **first-best** if it is feasible and no feasible allocation has larger welfare.
--
--   **Mechanisms.** A direct mechanism $(\Phi, t, p)$ is a feasible allocation with a measurable, integrable, non-negative price function $p$ on $\Phi$. It is **incentive compatible** (IC) if $\min\{t(\theta),\theta\} - p(\theta) \ge \min\{t(\theta'),\theta\} - p(\theta')$ for all $\theta, \theta' \in \Phi$, and **individually rational** (IR) if $\min\{t(\theta),\theta\} - p(\theta) - cW \ge 0$ for all $\theta \in \Phi$. Its revenue is $\pi = \frac{\Lambda}{\bar\theta}\int_\Phi p(\theta)\, d\theta$.
--
--   **Constants of Theorem 1.**
--   $$\Lambda_1 = \frac{32\left(4c+5-\sqrt{2c(8c+7)}\right)}{3(26c+25)\,\bar\theta},\qquad \Lambda_2 = \frac{4\left(1-\sqrt{c/(c+2)}\right)}{\bar\theta},$$
--   $$\widetilde T = \sqrt{\frac{\bar\theta}{\Lambda}\left(1-\sqrt{\frac{c}{c+2}}\right)},\qquad \mathcal{FB} = \frac12 (c+2)\left(1-\sqrt{\frac{c}{c+2}}\right)^2 .$$
--
--   These objects are shared by every statement of the mission: Theorem 1 characterises the first-best allocations, and Theorem 8 shows that a revenue-maximising IC and IR mechanism attains them.
--
--   **Formalization Note** No queue is modelled: the waiting time is *defined* by the displayed formula, which is the Pollaczek–Khinchine mean $\lambda E[S^2]/(2(1-\lambda E[S]))$ with $\lambda E[S] = (\Lambda/\bar\theta)\int_\Phi t$ and $\lambda E[S^2] = (\Lambda/\bar\theta)\int_\Phi t^2$. The program's "$W(t(\theta)) \ge 0$" is read as stability $\Lambda\int_\Phi t < \bar\theta$. Welfare integrates over the admitted set $\Phi$, as in the proof of Theorem 1 (p. 35) and the program of Theorem 8; §4's display integrates over $[0,\bar\theta]$, which would charge the waiting cost to customers who are not admitted. IC is stated on $\Phi \times \Phi$, as printed (the waiting cost is common to both sides and omitted, as on the page). $c > 0$ is made explicit. The integrability of $p$ is required so that revenue is not Lean's junk value $0$ for a non-integrable price. All quantities are real numbers; `Lam` stands for $\Lambda$ and `θbar` for $\bar\theta$.
-- source:
--   Feldman & Segev, The Important Role of Time Limits when Consumers Choose their Time in Service, SSRN 3424317 (version of 2021-10-07), pp. 6–9, 19, 35 and 39, §3, §4 (Theorem 1), §7, proof of Theorem 1

import Mathlib

namespace ServTimeLimit.OptMech

open MeasureTheory

/-- Parameters of the model of §3 (pp. 6–8) with `β = 0`: the potential arrival rate `Λ`
(`Lam`), the waiting cost `c` per unit of waiting time, and the upper end `θ̄` (`θbar`) of the
type distribution `U[0, θ̄]`. -/
structure Params where
  /-- `Λ`, the rate of the Poisson process of service needs. -/
  Lam : ℝ
  /-- `c`, the waiting cost per unit of time spent waiting. -/
  c : ℝ
  /-- `θ̄`, types are uniform on `[0, θ̄]`. -/
  θbar : ℝ

/-- Standing assumptions: `Λ > 0`, `c > 0`, `θ̄ > 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.Lam ∧ 0 < P.c ∧ 0 < P.θbar

/-- The load integral `∫_Φ t(θ) dθ` of an allocation `(Φ, t)`. -/
noncomputable def load (Φ : Set ℝ) (t : ℝ → ℝ) : ℝ :=
  ∫ θ in Φ, t θ

/-- The second-moment integral `∫_Φ t(θ)² dθ` of an allocation `(Φ, t)`. -/
noncomputable def moment2 (Φ : Set ℝ) (t : ℝ → ℝ) : ℝ :=
  ∫ θ in Φ, t θ ^ 2

/-- The Pollaczek–Khinchine expected waiting time of the allocation `(Φ, t)` with uniform types
(display on p. 8): `W = Λ ∫_Φ t² / (2 (θ̄ − Λ ∫_Φ t))`. -/
noncomputable def waitTime (P : Params) (Φ : Set ℝ) (t : ℝ → ℝ) : ℝ :=
  P.Lam * moment2 Φ t / (2 * (P.θbar - P.Lam * load Φ t))

/-- Social welfare of the allocation `(Φ, t)`: `SW = (Λ/θ̄) ∫_Φ (t(θ) − c W) dθ`
(proof of Theorem 1, p. 35; integrated over the admitted set only). -/
noncomputable def welfare (P : Params) (Φ : Set ℝ) (t : ℝ → ℝ) : ℝ :=
  P.Lam / P.θbar * ∫ θ in Φ, (t θ - P.c * waitTime P Φ t)

/-- A feasible allocation: a measurable admitted set `Φ ⊆ [0, θ̄]`, a measurable time function
`t` with `0 ≤ t(θ) ≤ θ` on `Φ`, and a stable queue `Λ ∫_Φ t < θ̄` (the page's `W ≥ 0`). -/
def IsAllocation (P : Params) (Φ : Set ℝ) (t : ℝ → ℝ) : Prop :=
  MeasurableSet Φ ∧ Φ ⊆ Set.Icc 0 P.θbar ∧ Measurable t ∧
    (∀ θ ∈ Φ, 0 ≤ t θ ∧ t θ ≤ θ) ∧ P.Lam * load Φ t < P.θbar

/-- `(Φ, t)` is a first-best allocation: feasible, and its welfare is at least that of every
feasible allocation (§4, p. 8). -/
def IsFirstBest (P : Params) (Φ : Set ℝ) (t : ℝ → ℝ) : Prop :=
  IsAllocation P Φ t ∧
    ∀ (Φ' : Set ℝ) (t' : ℝ → ℝ), IsAllocation P Φ' t' → welfare P Φ' t' ≤ welfare P Φ t

/-- A direct price-and-time mechanism `(Φ, t, p)` (§7, p. 19): a feasible allocation and a
measurable, integrable, nonnegative price function `p : Φ → ℝ₊`. -/
def IsMechanism (P : Params) (Φ : Set ℝ) (t p : ℝ → ℝ) : Prop :=
  IsAllocation P Φ t ∧ Measurable p ∧ IntegrableOn p Φ ∧ ∀ θ ∈ Φ, 0 ≤ p θ

/-- Incentive compatibility (IC) as printed on p. 19, for reports in `Φ`:
`min{t(θ), θ} − p(θ) ≥ min{t(θ'), θ} − p(θ')`. -/
def IsIC (Φ : Set ℝ) (t p : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Φ, ∀ θ' ∈ Φ, min (t θ') θ - p θ' ≤ min (t θ) θ - p θ

/-- Individual rationality (IR) as printed on p. 19: `min{t(θ), θ} − p(θ) − c W ≥ 0` on `Φ`. -/
def IsIR (P : Params) (Φ : Set ℝ) (t p : ℝ → ℝ) : Prop :=
  ∀ θ ∈ Φ, 0 ≤ min (t θ) θ - p θ - P.c * waitTime P Φ t

/-- The firm's revenue `π = Λ (1/θ̄) ∫_Φ p(θ) dθ` (p. 19). -/
noncomputable def revenue (P : Params) (Φ : Set ℝ) (p : ℝ → ℝ) : ℝ :=
  P.Lam / P.θbar * ∫ θ in Φ, p θ

/-- `Λ₁ = 32 (4c + 5 − √(2c(8c + 7))) / (3 (26c + 25) θ̄)` (Theorem 1, p. 8; bracketing from
p. 39). -/
noncomputable def lam1 (P : Params) : ℝ :=
  32 * (4 * P.c + 5 - Real.sqrt (2 * P.c * (8 * P.c + 7))) / (3 * (26 * P.c + 25) * P.θbar)

/-- `Λ₂ = 4 (1 − √(c/(c + 2))) / θ̄` (Theorem 1, p. 8). -/
noncomputable def lam2 (P : Params) : ℝ :=
  4 * (1 - Real.sqrt (P.c / (P.c + 2))) / P.θbar

/-- `T̃ = √((θ̄/Λ)(1 − √(c/(c + 2))))` (Theorem 1, p. 9). -/
noncomputable def Ttilde (P : Params) : ℝ :=
  Real.sqrt (P.θbar / P.Lam * (1 - Real.sqrt (P.c / (P.c + 2))))

/-- The first-best value `(1/2)(c + 2)(1 − √(c/(c + 2)))²` for `Λ ≥ Λ₂` (proof of Theorem 1,
p. 39). -/
noncomputable def fbValue (P : Params) : ℝ :=
  (P.c + 2) * (1 - Real.sqrt (P.c / (P.c + 2))) ^ 2 / 2

end ServTimeLimit.OptMech


