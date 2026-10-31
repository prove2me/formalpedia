-- Prove2me | Definitions.Def_OrgAnalytics_Model
-- name    : OrgAnalytics_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:08:44.881011+00:00
-- url     : https://prove2.me/theorems/7b39718a-0b6d-40fd-b38b-4a43aa732d6c
-- title:
--   The designer–agent–principal game over status-quo experiments: $\alpha_H$ (1), $p^C_S$ (2), continuation equilibria, $V_k$ (9), $U$, optimal designs, (17), (20), (A.9), the dual audit
-- statement:
--   This module defines the game of Alonso and Câmara's *Organizing Data Analytics*, restricted to status-quo experiments, together with the organization's design problem.
--
--   **Parameters** (§2, pp. 8–9). The prior is $\mu=\Pr[\theta=1]$ on a binary state, the principal's payoff is $q_H$ for keeping the status quo $d_S$ and $\theta$ for approving $d_H$, and the designer and the agent gain $\Delta>0$ from $d_H$. Throughout, $0<\mu<q_H<1$.
--
--   **Constants.**
--
--   1. $\alpha_H=\dfrac{\mu(1-q_H)}{(1-\mu)q_H}$, the type-I error of the commitment experiment, eq. (1).
--   2. $p^C_S=\dfrac{q_H-\mu}{q_H}$, eq. (2).
--   3. $\underline\alpha(\lambda)=\dfrac{2\lambda-1}{\lambda}\alpha_H-\dfrac{\mu(1-\lambda)}{(1-\mu)\lambda}$, eq. (17), and $p(\lambda)=2p^C_S-1+\dfrac{1-p^C_S}{\lambda}$, p. 47.
--   4. $\lambda^*=\dfrac1{2-q_H}$, eq. (19), $U^*=q_H+\dfrac{\mu(1-q_H)}{2-q_H}$ (proof of Proposition 7, p. 48), and $r^*=\dfrac{q_H-\mu}{q_H(1-\mu)}$, Proposition 7(iv).
--
--   **Designs.** A task allocation $k$ is integration $I$ or separation $S$. A cost distribution is a probability measure $F$ on $\mathbb R$ with no mass below $0$; write $F_<(g)=F((-\infty,g))$ and $F_\le(g)=F((-\infty,g])$. A design $(\lambda,F)$ is admissible if $\lambda\in[0,1]$ and $F$ is a cost distribution.
--
--   **Outcomes.** An outcome is $(\alpha,t,\tau,\sigma)$: the status-quo experiment $\pi_S(\alpha)$ has $\Pr[s=H\mid\theta=1]=1$ and $\Pr[s=H\mid\theta=0]=\alpha$; $t$ is the probability that the agent tampers after $s=S$; $\tau$ and $\sigma$ are the probabilities of approval after an unaudited $m=H$ and an audited $s=H$. With gain $g=(1-\lambda)\tau\Delta$ and report rate $a=\alpha+(1-\alpha)t$, the outcome is a **continuation equilibrium** if all four components lie in $[0,1]$, and
--
--   1. $F_<(g)\le t\le F_\le(g)$;
--   2. $\sigma=1$ if $\mu/(\mu+(1-\mu)\alpha)>q_H$, and $\sigma=0$ if it is $<q_H$;
--   3. $\tau=1$ if $\mu/(\mu+(1-\mu)a)>q_H$, and $\tau=0$ if it is $<q_H$.
--
--   **Payoffs.** The approval probability is $A=\lambda\sigma(\mu+(1-\mu)\alpha)+(1-\lambda)\tau(\mu+(1-\mu)a)$. The expected tampering cost is
--   $$\mathrm{ETC}=(1-\mu)(1-\alpha)\Big(\int_{c<g}c\,dF+(t-F_<(g))\,g\Big).$$
--   The designer gets $V_S=\Delta A$ under separation and $V_I=\Delta A-\mathrm{ETC}$ under integration, and the principal gets $U=q_H(1-A)+\mu(\lambda\sigma+(1-\lambda)\tau)$, her expected utility.
--
--   **Optimality.** An outcome is designer-optimal if it maximizes $V_k$ over all continuation equilibria of all status-quo experiments. A tuple $(k,\lambda,F,o)$ is an optimal design if the design is admissible, $o$ is designer-optimal, and $U$ at $o$ is at least $U$ at every designer-optimal outcome of every admissible design.
--
--   **Policies.** Assumption 1 is $1-F_\le((1-\lambda)\Delta)>0$, eq. (3). The two-point policy (A.9) puts mass $(p(\lambda)-p^C_S)/p(\lambda)$ on $0$ and $p^C_S/p(\lambda)$ on $(1-\lambda)\Delta$. The policy $F^*_{opt}$ of (20) puts mass $\alpha_H$ on $0$ and $1-\alpha_H$ on $(1-q_H)\Delta/(2-q_H)$.
--
--   **Dual audit** (Proposition 7(iv)). Tampering is costless, and an internal audit unseen by the principal rectifies a tampered report with probability $r$. In an outcome $(\alpha,\hat t,\tau,\sigma)$, $\hat t$ is the attempt probability and $(1-r)\hat t$ the effective tampering probability. It is a continuation equilibrium if $\hat t=1$ whenever $(1-r)(1-\lambda)\tau\Delta>0$ and conditions 2–3 hold for the effective report rate. The designer maximizes $\Delta A$.
--
--   This is the model every statement of the mission refers to. The designer's choice and the principal's value are argmaxes over equilibrium outcomes, not closed forms.
--
--   **Formalization Note** Identifiers `lam`, `mu`, `qH` stand for $\lambda,\mu,q_H$. Three printed conventions are corrected and recorded in the docstrings: (1) prints the denominator $q_H(1-q_H)$ for the odds $q_H/(1-q_H)$; (20) omits $\Delta$ from the cut-off; and the continuation equilibrium is not unique for a distribution with atoms, so it is defined with ties. Assumption 1 is not part of `Admissible`, because $F^*_{opt}$ violates it. The integral is a Bochner integral of the identity over a set on which it is bounded $F$-almost everywhere, so its value is the intended one for every cost distribution and $g\ge0$.
-- source:
--   Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024), doi:10.1287/mnsc.2023.00207, §2 pp.8–12 (PDF 10–14), §3 pp.13–16 (PDF 15–18), eqs. (1), (2), (3), (4), (6), (7), (9), (17), (19), (20), Proposition 7(iv) p.26 (PDF 28), proof of Proposition 6 pp.46–48 (PDF 48–50), eq. (A.9) p.48 (PDF 50)

import Mathlib

open MeasureTheory

namespace OrgAnalytics

/-- The **parameters** of the designer–agent–principal game: the common prior `mu = Pr[θ = 1]`, the
principal's approval threshold `qH`, and the gain `Δ = v_H − v_S` of the designer and the agent
from the decision `d_H`.
Alonso–Câmara, Organizing Data Analytics, Management Science 70(5) (2024),
doi:10.1287/mnsc.2023.00207, §2, pp.8–9 (PDF 10–11).

**Formalization Note** `mu`, `qH` stand for `µ`, `q_H`. The paper's assumptions are `0 < q_H < 1`,
`µ < q_H` (p.9) and `0 = v_S < v_H` (p.8), so `Δ > 0`. The paper writes only "common prior µ";
`0 < mu` is an explicit reading: at `µ = 0` the state `θ = 1` never occurs, `α_H = 0` and every
audit intensity gives the principal `q_H`, so Proposition 7(i) fails. -/
structure Params where
  /-- The common prior `µ = Pr[θ = 1]`. -/
  mu : ℝ
  /-- The principal's approval threshold `q_H`. -/
  qH : ℝ
  /-- The gain `Δ = v_H − v_S` from inducing `d_H`. -/
  Δ : ℝ
  mu_pos : 0 < mu
  mu_lt_qH : mu < qH
  qH_lt_one : qH < 1
  Δ_pos : 0 < Δ

/-- The **task allocation** `k`: integration `I` (the same person designs and analyses, so the
designer bears the tampering cost) or separation `S` (he does not).
Alonso–Câmara, Management Science 70(5) (2024), §2, p.11 (PDF 13). -/
inductive TaskAlloc
  | I
  | S
  deriving DecidableEq

/-- A **cost distribution** (tampering prevention policy): a probability measure on `ℝ` with no
mass below `0`. Alonso–Câmara, Management Science 70(5) (2024), §2, pp.9–10 (PDF 11–12): "the
principal can specify any distribution of tampering costs F".

**Formalization Note** Atoms are allowed, and no density is assumed: the optimal policy (20) is
atomic. Assumption 1 of p.13 is not part of this class; see `Params.AssumptionOne`. -/
structure IsCostDist (F : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure F
  nonneg : F (Set.Iio 0) = 0

/-- A design `(lam, F)` is **admissible** if `lam ∈ [0, 1]` and `F` is a cost distribution;
the task allocation is free.
Alonso–Câmara, Management Science 70(5) (2024), §2, p.10 (PDF 12). -/
def Admissible (lam : ℝ) (F : Measure ℝ) : Prop := lam ∈ Set.Icc (0 : ℝ) 1 ∧ IsCostDist F

/-- `F_<(g)`: the mass of costs strictly below `g`. Real-valued; `F` is a probability measure in
every use, so `toReal` is applied to a finite value. -/
noncomputable def massLT (F : Measure ℝ) (g : ℝ) : ℝ := (F (Set.Iio g)).toReal

/-- `F_≤(g)`: the mass of costs at most `g`, i.e. the distribution function `F(g)` of the paper. -/
noncomputable def massLE (F : Measure ℝ) (g : ℝ) : ℝ := (F (Set.Iic g)).toReal

/-- An **outcome** `(α, t, τ, σ)` of the status-quo problem:
* `α`: the type-I error of the status-quo experiment `π_S(α)`, which has `Pr[s = H | θ = 1] = 1`
  and `Pr[s = H | θ = 0] = α` (definition (4), p.14, PDF 16);
* `t`: the probability that the agent, after `s = S`, tampers and reports `H`;
* `τ`: the probability that the principal approves after an unaudited `m = H`;
* `σ`: the probability that she approves after an audited `s = H`.

**Formalization Note** The other parts of the strategies are the paper's (7) and footnote 18,
p.14: after `s = H` the agent reports `H`, and the principal keeps `d_S` after an audited `s = S`
and after an unaudited `m = S`. -/
@[ext]
structure Outcome where
  /-- The type-I error of the status-quo experiment. -/
  α : ℝ
  /-- The tampering probability after `s = S`. -/
  t : ℝ
  /-- The approval probability after an unaudited `m = H`. -/
  τ : ℝ
  /-- The approval probability after an audited `s = H`. -/
  σ : ℝ

/-- `Pr[m = H | θ = 0] = α + (1 − α) t`: a low state reports `H` if the experiment says so, or
if the agent tampers. -/
def Outcome.reportRate (o : Outcome) : ℝ := o.α + (1 - o.α) * o.t

namespace Params

variable (P : Params)

/-- The type-I error of the commitment experiment: `α_H = µ(1 − q_H)/((1 − µ) q_H)`, the value of
`α` at which `Pr[θ = 1 | s = H] = q_H` with `β = 0`.
Alonso–Câmara, Management Science 70(5) (2024), eq. (1), p.11 (PDF 13).

**Formalization Note** The display (1) prints the denominator as `q_H(1 − q_H)`, a product. That
is a misprint for the odds `q_H/(1 − q_H)`: the sentence before (1) fixes the posterior at `q_H`,
which solves to this value, (2) needs it, and at `µ = 1/4`, `q_H = 3/8` the printed form gives
`64/45 > 1`, not a probability. Denominators are positive by `mu < qH < 1`. -/
noncomputable def alphaH : ℝ := P.mu * (1 - P.qH) / ((1 - P.mu) * P.qH)

/-- The status-quo probability of the commitment experiment:
`p^C_S = (q_H − µ)/q_H`.
Alonso–Câmara, Management Science 70(5) (2024), eq. (2), p.12 (PDF 14). -/
noncomputable def pCS : ℝ := (P.qH - P.mu) / P.qH

/-- The lower bound on the type-I error:
`α(λ) = ((2λ − 1)/λ) α_H − µ(1 − λ)/((1 − µ) λ)`.
Alonso–Câmara, Management Science 70(5) (2024), eq. (17), p.24 (PDF 26).

**Formalization Note** Used only at `lam > 0`, so the division by `lam` is genuine. -/
noncomputable def alphaLower (lam : ℝ) : ℝ :=
  (2 * lam - 1) / lam * P.alphaH - P.mu * (1 - lam) / ((1 - P.mu) * lam)

/-- `p(λ) = 2 p^C_S − 1 + (1 − p^C_S)/λ`, the largest probability of `s = S` compatible with
audit intensity `λ`.
Alonso–Câmara, Management Science 70(5) (2024), proof of Proposition 6, p.47 (PDF 49).

**Formalization Note** Used only at `lam ≥ 1/(2 − qH)`, where it is positive. -/
noncomputable def pLower (lam : ℝ) : ℝ := 2 * P.pCS - 1 + (1 - P.pCS) / lam

/-- The optimal audit intensity `λ*_opt = 1/(2 − q_H)`.
Alonso–Câmara, Management Science 70(5) (2024), eq. (19), p.26 (PDF 28). -/
noncomputable def lamStar : ℝ := 1 / (2 - P.qH)

/-- The principal's optimal value `U* = q_H + µ(1 − q_H)/(2 − q_H)`.
Alonso–Câmara, Management Science 70(5) (2024), proof of Proposition 7, p.48 (PDF 50): the value
`q_H + (q − q_H)µ/(2q − q_H)` of the display there at `q = 1`. -/
noncomputable def UStar : ℝ := P.qH + P.mu * (1 - P.qH) / (2 - P.qH)

/-- The internal audit's success probability `(q_H − µ)/(q_H(1 − µ))`.
Alonso–Câmara, Management Science 70(5) (2024), Proposition 7(iv), p.26 (PDF 28). -/
noncomputable def rStar : ℝ := (P.qH - P.mu) / (P.qH * (1 - P.mu))

/-- The posterior `Pr[θ = 1 | event]` of an event that has probability `1` in state `θ = 1` and
probability `x` in state `θ = 0`: `µ/(µ + (1 − µ) x)`. The denominator is positive for `x ∈ [0, 1]`
because `0 < µ < 1`. -/
noncomputable def posterior (x : ℝ) : ℝ := P.mu / (P.mu + (1 - P.mu) * x)

/-- The agent's gain from tampering, `g = (1 − λ) τ Δ`: it pays only when the audit is
inconclusive and the principal then approves.
Alonso–Câmara, Management Science 70(5) (2024), §3.1, p.13 (PDF 15), and (6), p.14 (PDF 16). -/
noncomputable def gain (lam : ℝ) (o : Outcome) : ℝ := (1 - lam) * o.τ * P.Δ

/-- `IsContEq lam F o`: `o` is a **continuation equilibrium** of the communication subgame after
the status-quo experiment `π_S(o.α)`, under audit intensity `lam` and cost distribution `F`. All
four components are probabilities, and with `g = (1 − λ) τ Δ` and `a = α + (1 − α) t`:
1. the agent tampers when `c < g`, does not when `c > g`, and may mix when `c = g`, that is
   `F_<(g) ≤ t ≤ F_≤(g)`;
2. after an audited `s = H` the principal approves if the posterior exceeds `q_H` and keeps the
   status quo if it falls short, and is free to mix at equality;
3. the same after an unaudited `m = H`, whose posterior is computed from `a`.

Alonso–Câmara, Management Science 70(5) (2024), §3.1–3.2, pp.13–14 (PDF 15–16), eqs. (6)–(7).

**Formalization Note** The paper calls the continuation equilibrium "unique" and gives it by (6).
For a distribution with atoms that is not so, and (6) may have no solution; this predicate is the
equilibrium conditions themselves, ties included, and the designer selects among them
(`IsDesignerOpt`). `α` ranges over `[0, 1]`, more than the set `A` of (5). -/
structure IsContEq (lam : ℝ) (F : Measure ℝ) (o : Outcome) : Prop where
  α_mem : o.α ∈ Set.Icc (0 : ℝ) 1
  t_mem : o.t ∈ Set.Icc (0 : ℝ) 1
  τ_mem : o.τ ∈ Set.Icc (0 : ℝ) 1
  σ_mem : o.σ ∈ Set.Icc (0 : ℝ) 1
  agent_lo : massLT F (P.gain lam o) ≤ o.t
  agent_hi : o.t ≤ massLE F (P.gain lam o)
  audited_approve : P.qH < P.posterior o.α → o.σ = 1
  audited_reject : P.posterior o.α < P.qH → o.σ = 0
  unaudited_approve : P.qH < P.posterior o.reportRate → o.τ = 1
  unaudited_reject : P.posterior o.reportRate < P.qH → o.τ = 0

/-- The probability of approval:
`A = λ σ (µ + (1 − µ) α) + (1 − λ) τ (µ + (1 − µ) a)`, summing over an audited `s = H` and an
unaudited `m = H`, the only events followed by `d_H` ((7), p.14). -/
def approvalProb (lam : ℝ) (o : Outcome) : ℝ :=
  lam * o.σ * (P.mu + (1 - P.mu) * o.α) +
    (1 - lam) * o.τ * (P.mu + (1 - P.mu) * o.reportRate)

/-- The **expected tampering cost**: tampering happens only after `s = S`, of probability
`(1 − µ)(1 − α)`, and costs `∫_{c < g} c dF` plus the mixing mass `(t − F_<(g)) g` at an atom
`c = g`.
Alonso–Câmara, Management Science 70(5) (2024), the last term of (9), p.16 (PDF 18).

**Formalization Note** For a cost distribution `F` and `g ≥ 0`, the identity is integrable on
`Set.Iio g`: `F` is finite and the identity is bounded on `[0, g)`, which carries the mass of
`Set.Iio g`. So the Bochner integral has its intended value, and no integrability hypothesis is
needed. -/
noncomputable def tamperingCost (lam : ℝ) (F : Measure ℝ) (o : Outcome) : ℝ :=
  (1 - P.mu) * (1 - o.α) *
    ((∫ c in Set.Iio (P.gain lam o), c ∂F) + (o.t - massLT F (P.gain lam o)) * P.gain lam o)

/-- The **designer's payoff**: `V_S = Δ A` under separation and `V_I = Δ A − ETC` under
integration, the designer bearing the tampering cost only under integration.
Alonso–Câmara, Management Science 70(5) (2024), §2, p.11 (PDF 13), and (9), p.16 (PDF 18). -/
noncomputable def designerPayoff (k : TaskAlloc) (lam : ℝ) (F : Measure ℝ) (o : Outcome) : ℝ :=
  match k with
  | TaskAlloc.S => P.Δ * P.approvalProb lam o
  | TaskAlloc.I => P.Δ * P.approvalProb lam o - P.tamperingCost lam F o

/-- The **principal's expected utility** `E[u(d, θ)]`, with `u = q_H` for `d_S` and `u = θ` for
`d_H`: `U = q_H (1 − A) + µ (λ σ + (1 − λ) τ)`, the second term being `Pr[d_H, θ = 1]`.
Alonso–Câmara, Management Science 70(5) (2024), §2, p.8 (PDF 10).

**Formalization Note** This is the primitive utility. The closed forms (13)–(14) are theorems
(`OrgAnalytics.eq_14_principal_utility`), not this definition. -/
def principalUtility (lam : ℝ) (o : Outcome) : ℝ :=
  P.qH * (1 - P.approvalProb lam o) + P.mu * (lam * o.σ + (1 - lam) * o.τ)

/-- `IsDesignerOpt k lam F o`: `o` is a **designer-optimal** outcome, a continuation equilibrium
maximizing the designer's payoff over all continuation equilibria of all status-quo experiments.
Alonso–Câmara, Management Science 70(5) (2024), (8), p.15 (PDF 17).

**Formalization Note** The designer picks the experiment and the continuation together
(sender-preferred selection, as in Kamenica–Gentzkow, whom the paper follows on p.11). -/
def IsDesignerOpt (k : TaskAlloc) (lam : ℝ) (F : Measure ℝ) (o : Outcome) : Prop :=
  P.IsContEq lam F o ∧ ∀ o', P.IsContEq lam F o' →
    P.designerPayoff k lam F o' ≤ P.designerPayoff k lam F o

/-- `IsOptimalDesign k lam F o`: the design `(k, lam, F)` is admissible, `o` is designer-optimal
for it, and no designer-optimal outcome of any admissible design gives the principal more.
Alonso–Câmara, Management Science 70(5) (2024), §5.3, Proposition 7, p.26 (PDF 28).

**Formalization Note** Quantifying over pairs of a design and a designer-optimal outcome breaks the
designer's ties in the principal's favour. At the optimum the designer is indifferent between
`α = 0` and `α = α_H`; with ties against her the principal's supremum would not be attained. -/
def IsOptimalDesign (k : TaskAlloc) (lam : ℝ) (F : Measure ℝ) (o : Outcome) : Prop :=
  Admissible lam F ∧ P.IsDesignerOpt k lam F o ∧
    ∀ k' lam' F' o', Admissible lam' F' → P.IsDesignerOpt k' lam' F' o' →
      P.principalUtility lam' o' ≤ P.principalUtility lam o

/-- **Assumption 1**: `F̄((1 − λ) Δ) > 0`, costs that exceed the largest possible gain occur with
positive probability.
Alonso–Câmara, Management Science 70(5) (2024), Assumption 1, eq. (3), p.13 (PDF 15).

**Formalization Note** The paper imposes it "throughout", yet its `F*_opt` of (20) violates it at
`λ*_opt`. It is therefore not part of `Admissible`; the existence claims that can carry it do. -/
def AssumptionOne (lam : ℝ) (F : Measure ℝ) : Prop := 0 < 1 - massLE F ((1 - lam) * P.Δ)

/-- The two-point cost distribution of (A.9): mass `(p(λ) − p^C_S)/p(λ)` at cost `0` and mass
`p^C_S/p(λ)` at cost `(1 − λ) Δ`.
Alonso–Câmara, Management Science 70(5) (2024), proof of Proposition 6, eq. (A.9), p.48 (PDF 50).

**Formalization Note** Used only at `lam ≥ 1/(2 − qH)`, where `p(λ) > 0`. -/
noncomputable def FA9 (lam : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((P.pLower lam - P.pCS) / P.pLower lam) • Measure.dirac 0 +
    ENNReal.ofReal (P.pCS / P.pLower lam) • Measure.dirac ((1 - lam) * P.Δ)

/-- The optimal prevention policy `F*_opt` of (20): mass `α_H` at cost `0` and mass `1 − α_H` at
cost `(1 − q_H) Δ/(2 − q_H)`. So its distribution function is `α_H` on
`[0, (1 − q_H) Δ/(2 − q_H))` and `1` above.
Alonso–Câmara, Management Science 70(5) (2024), eq. (20), p.26 (PDF 28), and proof of
Proposition 7, p.48 (PDF 50).

**Formalization Note** (20) prints the cut-off `(1 − q_H)/(2 − q_H)`, without `Δ`; the proof on
p.48 has `c̃ = (1 − λ_opt)Δ = (1 − q_H)Δ/(2 − q_H)`, and the printed form is right only for
`Δ = 1`. -/
noncomputable def Fopt : Measure ℝ :=
  ENNReal.ofReal P.alphaH • Measure.dirac 0 +
    ENNReal.ofReal (1 - P.alphaH) • Measure.dirac ((1 - P.qH) * P.Δ / (2 - P.qH))

end Params

/-- In the dual audit, the outcome in terms of the tampering that survives the internal audit.
A component `o.t` read as the attempt probability `t̂` becomes `(1 − r) t̂`.
Alonso–Câmara, Management Science 70(5) (2024), Proposition 7(iv), pp.26–27 (PDF 28–29). -/
def Outcome.effective (r : ℝ) (o : Outcome) : Outcome :=
  { o with t := (1 - r) * o.t }

namespace Params

variable (P : Params)

/-- `IsDualContEq lam r o`: a continuation equilibrium of the **dual internal–external audit**.
Tampering is costless; the internal audit, unseen by the principal, catches and rectifies a
tampered report with probability `r`; the external audit is conclusive with probability `lam`.
Here `o.t` is the attempt probability `t̂`, and the effective tampering probability is
`(1 − r) t̂`. The agent attempts for sure whenever the gain `(1 − r)(1 − λ) τ Δ` is positive and
is free when it is `0`; the principal's conditions are those of `IsContEq`, for the effective
report rate.
Alonso–Câmara, Management Science 70(5) (2024), Proposition 7(iv), pp.26–27 (PDF 28–29).

**Formalization Note** A rectified report is `m = S`, followed by `d_S` as in (7). The principal
sees neither the internal audit nor its result. -/
structure IsDualContEq (lam r : ℝ) (o : Outcome) : Prop where
  α_mem : o.α ∈ Set.Icc (0 : ℝ) 1
  t_mem : o.t ∈ Set.Icc (0 : ℝ) 1
  τ_mem : o.τ ∈ Set.Icc (0 : ℝ) 1
  σ_mem : o.σ ∈ Set.Icc (0 : ℝ) 1
  agent : 0 < (1 - r) * P.gain lam o → o.t = 1
  audited_approve : P.qH < P.posterior o.α → o.σ = 1
  audited_reject : P.posterior o.α < P.qH → o.σ = 0
  unaudited_approve : P.qH < P.posterior (o.effective r).reportRate → o.τ = 1
  unaudited_reject : P.posterior (o.effective r).reportRate < P.qH → o.τ = 0

/-- `IsDualDesignerOpt lam r o`: `o` maximizes the designer's payoff `Δ A` over the continuation
equilibria of the dual audit. Tampering costs nothing, so the payoff is the same for both task
allocations. -/
def IsDualDesignerOpt (lam r : ℝ) (o : Outcome) : Prop :=
  P.IsDualContEq lam r o ∧ ∀ o', P.IsDualContEq lam r o' →
    P.Δ * P.approvalProb lam (o'.effective r) ≤ P.Δ * P.approvalProb lam (o.effective r)

end Params

end OrgAnalytics


