-- Prove2me | Definitions.Def_TamingMonster_Regret_Setting
-- name    : TamingMonster_Regret_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T08:16:54.972909+00:00
-- url     : https://prove2.me/theorems/5bb61066-7291-4996-a97f-4dbe6ef591a4
-- title:
--   Contextual bandit setting, IPS estimate (Eq. (1)), smoothed projection, (OP), $d_t$, $\mu_m$, $m(t)$
-- statement:
--   This file fixes the model and the basic quantities of the i.i.d. contextual bandit problem of Agarwal et al. (2014).
--
--   There are $K$ actions $A=\{0,\dots,K-1\}$, a measurable context space $X$, and a finite policy class $\Pi\subseteq A^X$. An **interaction record** is a quadruple $(x,a,r(a),p(a))\in X\times A\times\mathbb R\times\mathbb R$: the context, the chosen action, the reward observed for that action only, and the probability with which the action was chosen. A **history** $H_t$ is the list of the first $t$ records, in order.
--
--   1. **Expected reward and regret.** For a distribution $\mathcal D$ of context/reward-vector pairs $(x,r)$, $\mathcal R(\pi)=\mathbb E_{(x,r)\sim\mathcal D}[r(\pi(x))]$ and $\mathrm{Reg}(\pi)=\max_{\pi'\in\Pi}\mathcal R(\pi')-\mathcal R(\pi)$.
--   2. **Empirical average.** $\widehat{\mathbb E}_{x\sim H}[f(x)]$ is the average of $f$ over the contexts of $H$, with multiplicity.
--   3. **Inverse propensity scoring** (Eq. (1)):
--   $$\widehat{\mathcal R}_t(\pi)=\frac1t\sum_{i=1}^t\frac{r_i(a_i)\,\mathbb 1\{\pi(x_i)=a_i\}}{p_i(a_i)},$$
--   and the estimated regret $\widehat{\mathrm{Reg}}_t(\pi)=\max_{\pi'\in\Pi}\widehat{\mathcal R}_t(\pi')-\widehat{\mathcal R}_t(\pi)$.
--   4. **Smoothed projection** (§2.4): for weights $Q$ on $\Pi$ and $\mu\ge 0$, $Q^\mu(a\mid x)=(1-K\mu)\sum_{\pi\in\Pi:\pi(x)=a}Q(\pi)+\mu$; and the **completion** $\widetilde Q=Q+\bigl(1-\sum_{\pi}Q(\pi)\bigr)\mathbb 1_{\bar\pi}$ with a default policy $\bar\pi$ (Algorithm 4).
--   5. **The optimization problem (OP)** (p. 5): with $\psi=100$ and $b_\pi=\widehat{\mathrm{Reg}}_t(\pi)/(\psi\mu)$, a vector $Q$ solves (OP) for $(H_t,\mu)$ if $Q\ge0$, $\sum_\pi Q(\pi)\le1$,
--   $$\sum_{\pi\in\Pi}Q(\pi)b_\pi\le 2K,\qquad \widehat{\mathbb E}_{x\sim H_t}\Bigl[\frac{1}{Q^{\mu}(\pi(x)\mid x)}\Bigr]\le 2K+b_\pi\ \ \forall\pi\in\Pi.$$
--   6. **Schedule quantities.** $d_t=\ln(16t^2|\Pi|/\delta)$ (Eq. (12)); for an epoch schedule $0=\tau_0<\tau_1<\cdots$, $\mu_m=\min\{1/(2K),\sqrt{d_{\tau_m}/(K\tau_m)}\}$ for $m\ge1$ and $\mu_0=1/(2K)$ (Algorithm 1); and $m(t)=\min\{m:t\le\tau_m\}$, the epoch containing round $t$ (Eq. (10)).
--
--   These objects are shared by the algorithm, the event $\mathcal E$, and every statement of the regret analysis.
--
--   **Formalization Note** Actions are `Fin K`; weights on $\Pi$ are functions on the subtype of the `Finset` $\Pi$. $\mathrm{Reg}$ and $\widehat{\mathrm{Reg}}_t$ use the maximum over $\Pi$, which equals the value at any maximizer $\pi_\star$ or $\pi_t$. Algorithm 1 prints $\mu_m$ "for all $m\ge0$", which is $0/0$ at $\tau_0=0$; the convention $\mu_0=1/(2K)$ is the value the paper's proofs of Lemmas 12 and 14 use. An empty history gives $\widehat{\mathcal R}=0$ for every policy.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 3 (§2.1), p. 4 (Eq. (1), §2.2, §2.4), p. 5 (Algorithm 1, (OP) Eqs. (2)-(3)), p. 14 (Algorithm 4), p. 16 (Eq. (10)), p. 17 (Eq. (12))

import Mathlib

namespace TamingMonster.Regret

open MeasureTheory

/-- An interaction record `(x, a, r(a), p(a)) ∈ X × A × [0,1] × [0,1]` (§2.1, p. 3), with the
action set `A = Fin K`: the context `x`, the chosen action `a`, the observed reward `r(a)` of the
chosen action only, and the probability `p(a)` with which `a` was chosen. A history `H_t` is the
list of the first `t` records, in chronological order. -/
abbrev Rec (X : Type*) (K : ℕ) : Type _ := X × Fin K × ℝ × ℝ

/-- Context `x` of a record. -/
abbrev Rec.ctx {X : Type*} {K : ℕ} (e : Rec X K) : X := e.1
/-- Chosen action `a` of a record. -/
abbrev Rec.act {X : Type*} {K : ℕ} (e : Rec X K) : Fin K := e.2.1
/-- Observed reward `r(a)` of a record. -/
abbrev Rec.rew {X : Type*} {K : ℕ} (e : Rec X K) : ℝ := e.2.2.1
/-- Recorded propensity `p(a)` of a record. -/
abbrev Rec.prop {X : Type*} {K : ℕ} (e : Rec X K) : ℝ := e.2.2.2

variable {X : Type*} {K : ℕ}

/-- Expected (instantaneous) reward `R(π) = E_{(x,r)∼D}[r(π(x))]` of a policy (§2.1, p. 3). -/
noncomputable def expReward [MeasurableSpace X] (D : Measure (X × (Fin K → ℝ)))
    (π : X → Fin K) : ℝ :=
  ∫ z, z.2 (π z.1) ∂D

/-- Expected (instantaneous) regret `Reg(π) = R(π⋆) − R(π)` (§2.1, p. 3), where
`R(π⋆) = max_{π' ∈ Π} R(π')`; the value does not depend on which maximizer `π⋆` is taken.
(`Π` is finite, so the supremum over the finite index type `Π` is a maximum when `Π ≠ ∅`.) -/
noncomputable def polRegret [MeasurableSpace X] (Pi : Finset (X → Fin K))
    (D : Measure (X × (Fin K → ℝ))) (π : X → Fin K) : ℝ :=
  (⨆ π' : Pi, expReward D (π' : X → Fin K)) - expReward D π

/-- Empirical average `Ê_{x∼H}[f(x)]` over the contexts of a history, with multiplicity
(§2.1, p. 3): `(1/|H|) ∑_{(x,a,r,p) ∈ H} f(x)`. -/
noncomputable def empAvg (h : List (Rec X K)) (f : X → ℝ) : ℝ :=
  (h.map (fun e => f e.ctx)).sum / h.length

/-- Inverse propensity scoring estimate, Eq. (1), p. 4:
`R̂_t(π) = (1/t) ∑_{i=1}^t r_i(a_i) 1{π(x_i) = a_i} / p_i(a_i)` for a history of length `t`. -/
noncomputable def ipsEst (h : List (Rec X K)) (π : X → Fin K) : ℝ :=
  (h.map (fun e => if π e.ctx = e.act then e.rew / e.prop else 0)).sum / h.length

/-- Estimated regret `R̂eg_t(π) = R̂_t(π_t) − R̂_t(π)` (§2.2, p. 4), where `π_t` maximizes
`R̂_t` over `Π`, so `R̂_t(π_t) = max_{π' ∈ Π} R̂_t(π')` whichever maximizer is chosen. -/
noncomputable def estRegret (Pi : Finset (X → Fin K)) (h : List (Rec X K))
    (π : X → Fin K) : ℝ :=
  (⨆ π' : Pi, ipsEst h (π' : X → Fin K)) - ipsEst h π

/-- Smoothed projection (§2.4, p. 4): for weights `Q` on `Π` and `μ`,
`Q^μ(a|x) = (1 − Kμ) ∑_{π ∈ Π : π(x) = a} Q(π) + μ`. -/
noncomputable def smoothProj (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (μ : ℝ) (x : X)
    (a : Fin K) : ℝ :=
  (1 - (K : ℝ) * μ) * (∑ π ∈ Finset.univ.filter (fun π : Pi => (π : X → Fin K) x = a), Q π) + μ

open Classical in
/-- Completion with a default policy (Algorithm 4, step 1, p. 14):
`Q̃ = Q + (1 − ∑_{π ∈ Π} Q(π)) 1_{π̄}`. -/
noncomputable def complete (Pi : Finset (X → Fin K)) (Q : Pi → ℝ) (πbar : Pi) : Pi → ℝ :=
  fun π => Q π + if π = πbar then 1 - ∑ π', Q π' else 0

/-- The constant `ψ := 100` of (OP), p. 5. -/
noncomputable def psi : ℝ := 100

/-- The optimization problem (OP), p. 5. Given a history `H_t` and a minimum probability `μ`,
put `b_π = R̂eg_t(π)/(ψμ)`; `Q` solves (OP) if `Q ∈ Δ^Π` (i.e. `Q(π) ≥ 0` for all `π` and
`∑_π Q(π) ≤ 1`, §2.1) and
(2) `∑_{π ∈ Π} Q(π) b_π ≤ 2K`, and
(3) `∀ π ∈ Π, Ê_{x∼H_t}[1/Q^μ(π(x)|x)] ≤ 2K + b_π`. -/
def IsOPSolution (Pi : Finset (X → Fin K)) (μ : ℝ) (h : List (Rec X K)) (Q : Pi → ℝ) : Prop :=
  (∀ π, 0 ≤ Q π) ∧ (∑ π, Q π ≤ 1) ∧
  (∑ π, Q π * (estRegret Pi h (π : X → Fin K) / (psi * μ)) ≤ 2 * K) ∧
  ∀ π : Pi, empAvg h (fun x => 1 / smoothProj Pi Q μ x ((π : X → Fin K) x)) ≤
    2 * K + estRegret Pi h (π : X → Fin K) / (psi * μ)

/-- `d_t := ln(16 t² |Π| / δ)`, Eq. (12), p. 17. -/
noncomputable def dT (Pi : Finset (X → Fin K)) (δ : ℝ) (t : ℕ) : ℝ :=
  Real.log (16 * (t : ℝ) ^ 2 * (Pi.card : ℝ) / δ)

/-- The minimum probability of epoch `m` (Algorithm 1, line 1, p. 5):
`μ_m = min{1/(2K), √(ln(16 τ_m² |Π|/δ)/(K τ_m))}` for `m ≥ 1`.
Convention: `μ_0 := 1/(2K)` (the printed formula is `0/0` at `τ_0 = 0`; the paper's proofs of
Lemmas 12 and 14 use `μ_{m−1} = 1/(2K)` for every `m ≤ m₀`, including `m = 1`). -/
noncomputable def muM (Pi : Finset (X → Fin K)) (δ : ℝ) (τ : ℕ → ℕ) (m : ℕ) : ℝ :=
  if m = 0 then 1 / (2 * (K : ℝ))
  else min (1 / (2 * (K : ℝ))) (Real.sqrt (dT Pi δ (τ m) / ((K : ℝ) * (τ m : ℝ))))

/-- Index of the epoch containing round `t`, Eq. (10), p. 16: `m(t) = min{m : t ≤ τ_m}`. -/
noncomputable def epochOf (τ : ℕ → ℕ) (t : ℕ) : ℕ :=
  sInf {m : ℕ | t ≤ τ m}

end TamingMonster.Regret


