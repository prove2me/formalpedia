-- Prove2me | Definitions.Def_DiscServLine_SPT_Model
-- name    : DiscServLine_SPT_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:50.397673+00:00
-- url     : https://prove2.me/theorems/6f82102c-fc03-49bd-86c8-e1ac55ca6d06
-- title:
--   §3.2, §5 and Lemma A7 — SPT service line with homogeneous customers: demand measure, moments, SPT waiting time, queue length, profit (9), optimality, price (2), F of (A–35)
-- statement:
--   The model of Debo and Li's discretionary service line, specialised to **homogeneous customers** ($\Delta=0$) and the **non-preemptive shortest-processing-time (SPT)** discipline.
--
--   **Parameters.** Customers arrive as a Poisson process of rate $\Lambda$. Every customer has quality sensitivity $\bar\theta$ and values a service of duration $t$ at $V(t,\bar\theta)=\bar\theta t-bt^2$; waiting costs $c$ per unit of sojourn time (waiting plus service). The standing assumptions are
--   $$0<c<\bar\theta,\qquad 0<b,\qquad 0<\Lambda .$$
--
--   **Service lines.** A service line consists of a shortest and a longest duration $\underline t\le\bar t$ and a finite **demand measure** $\mu$ on $[\underline t,\bar t]\subseteq[0,\infty)$; for a demand schedule $\lambda(t)$ it is $\mu(dt)=\lambda(t)\,dt$, and point masses (single services) are allowed. $\underline t$ and $\bar t$ are the ends of the support of $\mu$: every interval $[\underline t,\underline t+\varepsilon)$ and $(\bar t-\varepsilon,\bar t]$ has positive demand. The moments are
--   $$\Lambda_k=\int \tau^k\,\mu(d\tau),\qquad k=0,1,2,$$
--   so $\Lambda_0$ is the throughput and $\Lambda_1$ the load. A service line is **feasible** if $\Lambda_1<1$ and $\Lambda_0\le\Lambda$.
--
--   **SPT waiting time and queue length.** With $L^-(t)=\int_{\tau<t}\tau\,\mu(d\tau)$ and $L^+(t)=\int_{\tau\le t}\tau\,\mu(d\tau)$,
--   $$W(t)=\frac{\Lambda_2/2}{(1-L^-(t))(1-L^+(t))},\qquad Q=\int W(t)\,\mu(dt).$$
--   For a demand density $L^-=L^+=\int_{\underline t}^t\tau\lambda(\tau)d\tau$, and $W$ is eq. (7) of the paper (Phipps and van Voorhis); $Q$ is the expected queue length.
--
--   **Profit, optimality, price.** The firm's profit is eq. (9),
--   $$\Pi=(\bar\theta\Lambda_1-b\Lambda_2)-c(\Lambda_1+Q),$$
--   a service line is **optimal** if it is feasible and no feasible line has a larger profit, and the price schedule is eq. (2) at $\Delta=0$:
--   $$P(t)=\bar\theta t-bt^2-c\,(t+W(t)).$$
--
--   **Closed forms.** With $\kappa=2b/(\Lambda c)$, the left-hand side of equation (A–35) is
--   $$F(\omega)=\tfrac12\ln\frac{\frac{b}{\Lambda c}+\frac1\omega+\frac{1}{\sqrt\omega}\sqrt{\frac1\omega+\kappa}}{\frac{b}{\Lambda c}+1+\sqrt{1+\kappa}}-\frac{\bar\theta/c-1}{\sqrt{\frac1\omega+\kappa}}+\sqrt{1+\kappa}-\sqrt{1+\kappa\omega},$$
--   and Lemma A7's closed forms are $\underline t(\omega)=\frac{c}{2b}\sqrt{1+\kappa}\,(\sqrt{1+\kappa}-\sqrt{1+\omega\kappa})$, $\bar t(\omega)=\frac{c}{2b}(\sqrt{1+\kappa}-\sqrt{1+\omega\kappa})/\sqrt{\omega/(1+\omega\kappa)}$ and $\Lambda_2(\omega)=2\frac{c}{4b}(\frac{\bar\theta}{c}-1)\sqrt\omega\,(\sqrt{(1+\kappa)/(1+\omega\kappa)}-1)$. Corollary 1's service line has $\underline t=(1-(1-\Lambda_1)^2)/(2\Lambda_0)$, $\bar t=\underline t/(1-\Lambda_1)$ and density $\lambda(t)=\underline t/t^3$.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** The firm's mechanism-design problem is replaced by its reduced form (9) (the paper's Proposition 1 at $\Delta=0$), and $\Delta$ is not a parameter: with $\Delta=0$ every customer has type $\bar\theta$. Demand schedules are finite measures rather than densities, so that the collapsed line $\underline t=\bar t$ (an M/D/1 queue, p. 10) is a feasible design; at an atom $W$ is Cobham's non-preemptive priority wait with customers of equal duration served first-come first-served, which reduces to eq. (7) for densities and to $\Lambda_2/(2(1-\Lambda_1))$ for a single service. The paper's third condition of $\mathcal L$, $\Lambda_1^2\le\Lambda_2\Lambda_0$, is automatic (Cauchy–Schwarz). $V$ is not capped at its maximum (eqs. (1), (2), (9) use $\bar\theta t-bt^2$ throughout). The hypotheses $0<b$ and $0<\Lambda$ are added; the paper uses them implicitly.
-- source:
--   Debo & Li, Design and Pricing of Discretionary Service Lines, SSRN working paper 3054741 (Oct. 17, 2017), pp. 6–9 (PDF 6–9), §3.1–§3.2, eqs. (1)–(2) and the set 𝓛; p. 16 (PDF 16), eq. (7) and the queue length; p. 18 (PDF 18), eq. (9); p. 42 (PDF 42), proof of Corollary 1; Supplementary Document, pp. 22–23 (PDF 69–70), Lemma A7 and (A–35)

import Mathlib

namespace DiscServLine.SPT

open MeasureTheory

/-- The parameters of the homogeneous-customer model (§3.1–§3.2, pp. 6–9, with ∆ = 0):
`θbar` = θ̄, the quality sensitivity of every customer (θ̲ = θ̄ since ∆ = 0); `b`, the curvature of the
service value V(t, θ) = θt − bt²; `c`, the waiting cost per unit of sojourn time; `Λ`, the arrival rate
of the Poisson stream of potential customers. -/
structure Params where
  θbar : ℝ
  b : ℝ
  c : ℝ
  Λ : ℝ

/-- Standing assumptions. §3.2, p. 9: 0 < c < θ̄. Added (implicit in the paper): 0 < b (V has an
interior maximum; "For any b > 0", p. 43) and 0 < Λ (a Poisson arrival rate). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.c ∧ P.c < P.θbar ∧ 0 < P.b ∧ 0 < P.Λ

/-- A service line: the shortest and longest service durations `lo` = t̲, `hi` = t̄, and the demand
measure `μ` (μ(dt) = λ(t)dt for a demand schedule with density λ; point masses are allowed). -/
structure Design where
  lo : ℝ
  hi : ℝ
  μ : Measure ℝ

/-- The moments Λk = ∫ τ^k λ(τ)dτ, k = 0, 1, 2 (p. 7). -/
noncomputable def Design.Λk (d : Design) (k : ℕ) : ℝ := ∫ t, t ^ k ∂d.μ

/-- The load of the service durations strictly shorter than `t`. -/
noncomputable def Design.loadBelow (d : Design) (t : ℝ) : ℝ := ∫ τ in Set.Iio t, τ ∂d.μ

/-- The load of the service durations at most `t`. -/
noncomputable def Design.loadUpTo (d : Design) (t : ℝ) : ℝ := ∫ τ in Set.Iic t, τ ∂d.μ

/-- The expected waiting time in queue under non-preemptive SPT, eq. (7), p. 16:
W(t) = (Λ2/2)/(1 − ∫_{t̲}^t τλ(τ)dτ)² for an atomless demand measure; at an atom it is Cobham's
non-preemptive priority wait, with customers of equal duration served FIFO. -/
noncomputable def Design.W (d : Design) (t : ℝ) : ℝ :=
  (d.Λk 2 / 2) / ((1 - d.loadBelow t) * (1 - d.loadUpTo t))

/-- The expected queue length ∫ λ(t)W(t)dt (p. 16). -/
noncomputable def Design.Q (d : Design) : ℝ := ∫ t, d.W t ∂d.μ

/-- An admissible service line: a finite demand measure living on [lo, hi] ⊆ [0, ∞) that charges
every neighbourhood of both ends (so lo and hi are the shortest and longest service actually
offered), with load Λ1 < 1 (the set 𝓛, p. 8). -/
def Admissible (d : Design) : Prop :=
  IsFiniteMeasure d.μ ∧ 0 ≤ d.lo ∧ d.lo ≤ d.hi ∧ d.μ (Set.Icc d.lo d.hi)ᶜ = 0 ∧
    (∀ ε > 0, 0 < d.μ (Set.Ico d.lo (d.lo + ε))) ∧
    (∀ ε > 0, 0 < d.μ (Set.Ioc (d.hi - ε) d.hi)) ∧ d.Λk 1 < 1

/-- A feasible service line: admissible, with throughput Λ0 at most the arrival rate Λ (p. 8). -/
def Feasible (P : Params) (d : Design) : Prop := Admissible d ∧ d.Λk 0 ≤ P.Λ

/-- The firm's profit, eq. (9), p. 18 (eq. (1) at ∆ = 0): (θ̄Λ1 − bΛ2) − c(Λ1 + Q). -/
noncomputable def profit (P : Params) (d : Design) : ℝ :=
  P.θbar * d.Λk 1 - P.b * d.Λk 2 - P.c * (d.Λk 1 + d.Q)

/-- An optimal service line: feasible and of maximal profit among feasible lines. -/
def IsOptimal (P : Params) (d : Design) : Prop :=
  Feasible P d ∧ ∀ d', Feasible P d' → profit P d' ≤ profit P d

/-- The price schedule, eq. (2), p. 8, at ∆ = 0 (θ(t) = θ̄, no information rent):
P(t) = V(t, θ̄) − c(t + W(t)). -/
noncomputable def price (P : Params) (d : Design) (t : ℝ) : ℝ :=
  (P.θbar * t - P.b * t ^ 2) - P.c * (t + d.W t)

/-- κ = 2b/(Λc). -/
noncomputable def κ (P : Params) : ℝ := 2 * P.b / (P.Λ * P.c)

/-- The left-hand side F(ω) of (A–35), Suppl. p. 22 (= F of the proof of Proposition 5, p. 43). -/
noncomputable def F35 (P : Params) (ω : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log
      ((P.b / (P.Λ * P.c) + 1 / ω + (1 / Real.sqrt ω) * Real.sqrt (1 / ω + κ P)) /
        (P.b / (P.Λ * P.c) + 1 + Real.sqrt (1 + κ P)))
    - (P.θbar / P.c - 1) / Real.sqrt (1 / ω + κ P)
    + (Real.sqrt (1 + κ P) - Real.sqrt (1 + κ P * ω))

/-- Lemma A7's t̲ (Suppl. p. 23). -/
noncomputable def tLoA7 (P : Params) (ω : ℝ) : ℝ :=
  P.c / (2 * P.b) * Real.sqrt (1 + κ P) * (Real.sqrt (1 + κ P) - Real.sqrt (1 + ω * κ P))

/-- Lemma A7's t̄ (Suppl. p. 23). -/
noncomputable def tHiA7 (P : Params) (ω : ℝ) : ℝ :=
  P.c / (2 * P.b) * (Real.sqrt (1 + κ P) - Real.sqrt (1 + ω * κ P)) /
    Real.sqrt (ω / (1 + ω * κ P))

/-- Lemma A7's Λ2 (Suppl. p. 23). -/
noncomputable def Λ2A7 (P : Params) (ω : ℝ) : ℝ :=
  2 * (P.c / (4 * P.b)) * (P.θbar / P.c - 1) * Real.sqrt ω *
    (Real.sqrt ((1 + κ P) / (1 + ω * κ P)) - 1)

/-- Corollary 1's t̲ (proof, p. 42): (1 − (1 − Λ1)²)/(2Λ0). -/
noncomputable def cor1Lo (Λ0 Λ1 : ℝ) : ℝ := (1 - (1 - Λ1) ^ 2) / (2 * Λ0)

/-- Corollary 1's demand measure (proof, p. 42): density λ(t) = t̲/t³ on [t̲, t̲/(1 − Λ1)]. -/
noncomputable def cor1Measure (Λ0 Λ1 : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc (cor1Lo Λ0 Λ1) (cor1Lo Λ0 Λ1 / (1 - Λ1)))).withDensity
    (fun t => ENNReal.ofReal (cor1Lo Λ0 Λ1 / t ^ 3))

/-- Corollary 1's queue-minimizing service line [t̲, t̄] with t̄ = t̲/(1 − Λ1) (proof, p. 42). -/
noncomputable def cor1Design (Λ0 Λ1 : ℝ) : Design where
  lo := cor1Lo Λ0 Λ1
  hi := cor1Lo Λ0 Λ1 / (1 - Λ1)
  μ := cor1Measure Λ0 Λ1

end DiscServLine.SPT


