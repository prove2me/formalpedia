-- Prove2me | Definitions.Def_DelegStop_Commit_Model
-- name    : DelegStop_Commit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:34.326054+00:00
-- url     : https://prove2.me/theorems/6abfe25f-9d8e-4f43-b40c-ba151f2183e5
-- title:
--   §3–§3.2, pp. 6320–6322, T = 2 — delegated innovation: effort choice, exponential quality law, flexible and committed stopping
-- statement:
--   This module defines the two-round ($T = 2$) delegated innovation game of Rahmani and Ramachandran, §3 and §3.2, under its two stopping policies.
--
--   **Parameters.** The provider chooses, in each round in which it is asked for a solution, an effort level $\mu_t \in \{\mu_l, \mu_h\}$ at cost $c(\mu_l) = c_l$ or $c(\mu_h) = c_h$. Its capability is $k$. The client pays a fixed payment $p$ to the provider when the project stops with a feasible solution, and incurs an evaluation cost $c_I$ for every submitted solution. The **standing assumptions** of §3.2 are
--   $$0 < \mu_l < \mu_h < 1, \qquad 0 \le c_l < c_h, \qquad \frac{c_h}{\mu_h} \ge \frac{c_l}{\mu_l}, \qquad k > 0 .$$
--
--   **Solution quality.** Under effort $\mu$ the quality $v \ge 0$ of a solution has distribution function
--   $$\Phi_\mu(x) = 1 - \mu e^{-x/k}, \qquad x \ge 0,$$
--   that is, an atom of mass $1-\mu$ at $v = 0$ (an infeasible solution) and density $f_\mu(v) = \frac{\mu}{k} e^{-v/k}$ on $(0,\infty)$. A Stieltjes integral $\int_a^{\infty} g\, d\Phi_\mu$ of the paper is the integral of $g f_\mu$ over the open ray $(a,\infty)$; the atom is carried by the separate $\Phi_\mu(a)\cdot(\dots)$ terms of the recursions.
--
--   **Provider's best response.** Given an objective over the two effort levels, the provider takes $\mu_h$ when indifferent.
--
--   **Round 2.** By (9), and by (5) at the deadline, after an infeasible first solution the provider maximizes $-c(\mu) + (1-\Phi_\mu(0))p$; this gives $\mu^C_2$ and $\mu^{F-}_2$. By (4) at the deadline, after a feasible first solution under the flexible policy it maximizes $-c(\mu) + p$, giving $\mu^{F+}_2$. The provider's continuation values $U^C_2$, $U^{F+}_2$, $U^{F-}_2$ follow from (6), (7), (10).
--
--   **The flexible client after round 1.** After a feasible first solution $v_1 > 0$ the client compares stopping, worth $v_1 - p$, with continuing, worth
--   $$-c_I + \int_{v_1}^{\infty} (v-p)\, d\Phi_{\mu^{F+}_2}(v) + \Phi_{\mu^{F+}_2}(v_1)(v_1 - p),$$
--   as in (1) with (3), and stops when stopping is at least as good. $\Pi^{F+}_2(v_1)$ is the larger of the two. After an infeasible first solution its value is $\Pi^{F-}_2 = -c_I + \int_0^\infty (v-p)\,d\Phi_{\mu^{F-}_2}(v)$, by (2). Under the committed policy, $\Pi^C_2 = -c_I + \int_0^\infty (v-p)\,d\Phi_{\mu^C_2}(v)$, by (8).
--
--   **Round 1.** By (9), $\mu^C_1$ maximizes $-c(\mu) + (1-\Phi_\mu(0))p + \Phi_\mu(0) U^C_2$. By (5), $\mu^F_1$ maximizes
--   $$-c(\mu) + (1-\Phi_\mu(v^F_s))\,p + (\Phi_\mu(v^F_s) - \Phi_\mu(0))\,U^{F+}_2 + \Phi_\mu(0)\,U^{F-}_2,$$
--   where $1 - \Phi_\mu(v^F_s)$ is read as the probability, under effort $\mu$, that the first solution falls in the client's stop set $\{v_1 > 0 : \text{the client stops}\}$. No threshold $v^F_s$ is named in the model; Proposition 2 proves that the stop set is a ray.
--
--   **Client profits.** For given efforts, the flexible client's profit is
--   $$\Pi^F_1 = -c_I + \int_0^\infty \Pi^{F+}_2(v)\, d\Phi_{\mu_1}(v) + \Phi_{\mu_1}(0)\,\Pi^{F-}_2$$
--   and the committed client's is $\Pi^C_1 = -c_I + \int_0^\infty (v-p)\,d\Phi_{\mu_1}(v) + \Phi_{\mu_1}(0)\,\Pi^C_2$. The equilibrium profits $\Pi^F_1$ and $\Pi^C_1$ of (11) evaluate these at the provider's equilibrium efforts.
--
--   The module also names the threshold properties stated in Propositions 2 and 3: $v_s$ is a stopping threshold if $v_s \ge 0$ and the client stops after a feasible $v_1$ exactly when $v_1 \ge v_s$; $(\underline p, \bar p^C)$ and $(\underline p, \bar p^F)$ are effort thresholds if the provider's equilibrium efforts switch at them as in Proposition 3 (a) and (b), for every payment $p > 0$.
--
--   **Formalization Note.** Only $T = 2$ is modelled. The standing assumption $c_h/\mu_h \ge c_l/\mu_l$ is written cross-multiplied, $c_l\mu_h \le c_h\mu_l$, which is equivalent since $\mu_l, \mu_h > 0$; $c_l \ge 0$ is the reading that costs are non-negative. Effort levels are an inductive type with two constructors. The client stops on ties (Proposition 2 (a): "if $v_1 \ge v^F_s$"); the provider takes high effort on ties (the closed intervals of Proposition 3). The round-2 threshold at the deadline does not affect (4) and (5) there and is set to $0$. Integrals are Bochner integrals over open rays; every integrand is (affine in $v$) times $e^{-v/k}$ or bounded by such a function, hence integrable when $k > 0$.
-- source:
--   Rahmani & Ramachandran, Delegating Innovation Projects with Deadline: Committed vs. Flexible Stopping, Management Science 67(10):6317–6332 (2021), pp. 6320–6323 (PDF 5–8), §3, Equations (1)–(11), §3.2, §4 (T = 2)

import Mathlib

namespace DelegStop.Commit

/-- The provider's two effort levels, `μ_l` (low) and `μ_h` (high). -/
inductive Effort
  | low
  | high
  deriving DecidableEq

/-- Primitive parameters of the model (§3.2): effort levels `μl < μh`, their costs `cl < ch`,
and the provider's capability `k`. The evaluation cost `cI` and the payment `p` are kept
as separate arguments. -/
structure Params where
  μl : ℝ
  μh : ℝ
  cl : ℝ
  ch : ℝ
  k : ℝ

/-- Standing assumptions of §3.2 on effort levels and costs: `(μl, μh) ∈ (0,1)` with `μh > μl`,
`ch > cl ≥ 0`, and `ch/μh ≥ cl/μl` (written cross-multiplied). -/
def EffortStanding (μl μh cl ch : ℝ) : Prop :=
  0 < μl ∧ μl < μh ∧ μh < 1 ∧ 0 ≤ cl ∧ cl < ch ∧ cl * μh ≤ ch * μl

/-- All standing assumptions of §3.2: `EffortStanding` and capability `k > 0`. -/
def Params.Standing (P : Params) : Prop :=
  EffortStanding P.μl P.μh P.cl P.ch ∧ 0 < P.k

/-- Success probability `μ(e)` of an effort level. -/
def Params.mu (P : Params) : Effort → ℝ
  | .low => P.μl
  | .high => P.μh

/-- Cost `c(e)` of an effort level. -/
def Params.cost (P : Params) : Effort → ℝ
  | .low => P.cl
  | .high => P.ch

/-- The solution-quality distribution function `Φ_μ(x) = 1 − μ e^{−x/k}` (§3.2). -/
noncomputable def qualCDF (μ k x : ℝ) : ℝ := 1 - μ * Real.exp (-x / k)

/-- The density `(μ/k) e^{−v/k}` of `Φ_μ` on `(0, ∞)`; `Φ_μ` also has an atom of mass `1 − μ`
at `v = 0` (an infeasible solution). -/
noncomputable def qualDensity (μ k v : ℝ) : ℝ := μ / k * Real.exp (-v / k)

/-- `Φ_{μ(e)}` for an effort level `e`. -/
noncomputable def Params.Phi (P : Params) (e : Effort) (x : ℝ) : ℝ := qualCDF (P.mu e) P.k x

/-- The density of `Φ_{μ(e)}` on `(0, ∞)`. -/
noncomputable def Params.dens (P : Params) (e : Effort) (v : ℝ) : ℝ := qualDensity (P.mu e) P.k v

/-- The provider's best response to an objective `f` over the two effort levels;
ties go to high effort. -/
noncomputable def best (f : Effort → ℝ) : Effort := if f .low ≤ f .high then .high else .low

/-! ### Round 2 (T = 2) -/

/-- `μ^C_2`, by (9) at `t = T = 2` with `U^C_3 = 0`. -/
noncomputable def effort2C (P : Params) (p : ℝ) : Effort :=
  best (fun e => -P.cost e + (1 - P.Phi e 0) * p + P.Phi e 0 * 0)

/-- `μ^{F+}_2`, by (4) at `t = T = 2` with `U^{F+}_3 = p`. At the deadline the client takes any
feasible solution, so the round-2 threshold is `0` (the objective does not depend on it). -/
noncomputable def effort2Fplus (P : Params) (p : ℝ) : Effort :=
  best (fun e => -P.cost e + (1 - P.Phi e 0) * p + P.Phi e 0 * p)

/-- `μ^{F−}_2`, by (5) at `t = T = 2` with `U^{F+}_3 = p`, `U^{F−}_3 = 0` and round-2
threshold `0`. -/
noncomputable def effort2Fminus (P : Params) (p : ℝ) : Effort :=
  best (fun e => -P.cost e + (1 - P.Phi e 0) * p + (P.Phi e 0 - P.Phi e 0) * p + P.Phi e 0 * 0)

/-- `U^C_2`, by (10) at `t + 1 = 2`. -/
noncomputable def U2C (P : Params) (p : ℝ) : ℝ :=
  -P.cost (effort2C P p) + (1 - P.Phi (effort2C P p) 0) * p + P.Phi (effort2C P p) 0 * 0

/-- `U^{F+}_2`, by (6) at `t + 1 = 2`. -/
noncomputable def U2Fplus (P : Params) (p : ℝ) : ℝ :=
  -P.cost (effort2Fplus P p) + (1 - P.Phi (effort2Fplus P p) 0) * p
    + P.Phi (effort2Fplus P p) 0 * p

/-- `U^{F−}_2`, by (7) at `t + 1 = 2`. -/
noncomputable def U2Fminus (P : Params) (p : ℝ) : ℝ :=
  -P.cost (effort2Fminus P p) + (1 - P.Phi (effort2Fminus P p) 0) * p
    + (P.Phi (effort2Fminus P p) 0 - P.Phi (effort2Fminus P p) 0) * p
    + P.Phi (effort2Fminus P p) 0 * 0

/-! ### The client's round-2 values -/

/-- Flexible client after a feasible first solution `v1 > 0`, facing round-2 effort `e2`:
the value of continuing, `−cI + ∫_{v1}^{∞} (v − p) dΦ_{μ(e2)}(v) + Φ_{μ(e2)}(v1)(v1 − p)`
((1) at `t = 2` with (3)). -/
noncomputable def contValF (P : Params) (cI p : ℝ) (e2 : Effort) (v1 : ℝ) : ℝ :=
  -cI + (∫ v in Set.Ioi v1, (v - p) * P.dens e2 v) + P.Phi e2 v1 * (v1 - p)

/-- `Π^{F+}_2(v1)`: the maximum of stopping (`v1 − p`) and continuing ((1) at `t = 2`). -/
noncomputable def PiFplus2 (P : Params) (cI p : ℝ) (e2 : Effort) (v1 : ℝ) : ℝ :=
  max (v1 - p) (contValF P cI p e2 v1)

/-- `Π^{F−}_2`: the flexible client's value after an infeasible first solution ((2) at `t = 2`,
with `Π^{F−}_3 = 0`). -/
noncomputable def PiFminus2 (P : Params) (cI p : ℝ) (e2 : Effort) : ℝ :=
  -cI + (∫ v in Set.Ioi 0, (v - p) * P.dens e2 v) + P.Phi e2 0 * 0

/-- `Π^C_2` after an infeasible first solution ((8) at `t = 2`, with `Π^C_3 = 0` when `v_2 = 0`). -/
noncomputable def PiC2 (P : Params) (cI p : ℝ) (e2 : Effort) : ℝ :=
  -cI + (∫ v in Set.Ioi 0, (v - p) * P.dens e2 v) + P.Phi e2 0 * 0

/-- The equilibrium flexible client's stopping rule after a feasible first solution `v1`:
stop iff stopping is at least as good as continuing (ties: stop), with the round-2 effort
`μ^{F+}_2` the provider chooses by (4). -/
def stopsF (P : Params) (cI p v1 : ℝ) : Prop :=
  contValF P cI p (effort2Fplus P p) v1 ≤ v1 - p

/-- The stop set `{v1 > 0 : the flexible client stops}`. -/
def stopSet (P : Params) (cI p : ℝ) : Set ℝ := {v1 | 0 < v1 ∧ stopsF P cI p v1}

/-- Probability, under effort `e` in round 1, that the first solution lies in the stop set;
this is the paper's `1 − Φ_{μ}(v^F_s)` without naming the threshold. -/
noncomputable def probStop (P : Params) (cI p : ℝ) (e : Effort) : ℝ :=
  ∫ v in stopSet P cI p, P.dens e v

/-! ### Round 1 -/

/-- `μ^C_1`, by (9) at `t = 1`. -/
noncomputable def effort1C (P : Params) (p : ℝ) : Effort :=
  best (fun e => -P.cost e + (1 - P.Phi e 0) * p + P.Phi e 0 * U2C P p)

/-- `μ^F_1 = μ^{F−}_1`, by (5) at `t = 1`, with `1 − Φ_μ(v^F_s)` the probability of the stop set
and `Φ_μ(v^F_s) − Φ_μ(0) = (1 − Φ_μ(0)) − (1 − Φ_μ(v^F_s))`. -/
noncomputable def effort1F (P : Params) (cI p : ℝ) : Effort :=
  best (fun e => -P.cost e + probStop P cI p e * p
    + ((1 - P.Phi e 0) - probStop P cI p e) * U2Fplus P p + P.Phi e 0 * U2Fminus P p)

/-! ### Client values and equilibrium profits -/

/-- The flexible client's expected profit `Π^F_1` at given efforts: round-1 effort `e1`,
round-2 effort `e2plus` after a feasible and `e2minus` after an infeasible first solution
((2) at `t = 1`). -/
noncomputable def valueF (P : Params) (cI p : ℝ) (e1 e2plus e2minus : Effort) : ℝ :=
  -cI + (∫ v in Set.Ioi 0, PiFplus2 P cI p e2plus v * P.dens e1 v)
    + P.Phi e1 0 * PiFminus2 P cI p e2minus

/-- The committed client's expected profit `Π^C_1` at given efforts ((8) at `t = 1`). -/
noncomputable def valueC (P : Params) (cI p : ℝ) (e1 e2 : Effort) : ℝ :=
  -cI + (∫ v in Set.Ioi 0, (v - p) * P.dens e1 v) + P.Phi e1 0 * PiC2 P cI p e2

/-- Equilibrium client profit under the flexible stopping policy. -/
noncomputable def profitF (P : Params) (cI p : ℝ) : ℝ :=
  valueF P cI p (effort1F P cI p) (effort2Fplus P p) (effort2Fminus P p)

/-- Equilibrium client profit under the committed stopping policy. -/
noncomputable def profitC (P : Params) (cI p : ℝ) : ℝ :=
  valueC P cI p (effort1C P p) (effort2C P p)

/-! ### Threshold properties (used to state Propositions 2 and 3) -/

/-- `vs` is a stopping threshold of the flexible client (Proposition 2 (a)–(b)). -/
def IsStopThreshold (P : Params) (cI p vs : ℝ) : Prop :=
  0 ≤ vs ∧ ∀ v1 : ℝ, 0 < v1 → (stopsF P cI p v1 ↔ vs ≤ v1)

/-- `pLow, pBarC` are the effort thresholds of Proposition 3 (a) under committed stopping. -/
def CommittedEffortThresholds (P : Params) (pLow pBarC : ℝ) : Prop :=
  ∀ p : ℝ, 0 < p →
    (p < pLow → (effort1C P p, effort2C P p) = (Effort.low, Effort.low)) ∧
    (pLow ≤ p → p < pBarC → (effort1C P p, effort2C P p) = (Effort.low, Effort.high)) ∧
    (pBarC ≤ p → (effort1C P p, effort2C P p) = (Effort.high, Effort.high))

/-- `pLow, pBarF` are the effort thresholds of Proposition 3 (b) under flexible stopping. -/
def FlexibleEffortThresholds (P : Params) (cI pLow pBarF : ℝ) : Prop :=
  ∀ p : ℝ, 0 < p →
    (p < pLow → (effort1F P cI p, effort2Fminus P p) = (Effort.low, Effort.low)) ∧
    (pLow ≤ p → p < pBarF → (effort1F P cI p, effort2Fminus P p) = (Effort.low, Effort.high)) ∧
    (pBarF ≤ p → (effort1F P cI p, effort2Fminus P p) = (Effort.high, Effort.high))

end DelegStop.Commit


