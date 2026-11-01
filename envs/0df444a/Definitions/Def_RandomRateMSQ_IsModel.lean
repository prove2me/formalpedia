-- Prove2me | Definitions.Def_RandomRateMSQ_IsModel
-- name    : RandomRateMSQ_IsModel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:26:32.099145+00:00
-- url     : https://prove2.me/theorems/c0257240-8e68-436c-a129-a17baff7b33c
-- title:
--   The model of Büke–Qin: laws and independence of the primitives, system equations, non-anticipating routing
-- statement:
--   The $n$-th system satisfies the model with interarrival law $F_u$, rate law $F$, arrival rate $\lambda_n$ and abandonment rate $\gamma$ under a filtration $(\mathcal G_t)$ when:
--
--   1. the interarrival times are i.i.d. with law $F_u$; the rates $\tilde\mu^n_k$ are i.i.d. with law $F$; the gaps of $S^n$ and of $N^n$ are i.i.d. exponential(1); the marks $U^n_i$ are i.i.d. uniform(0,1);
--   2. the five blocks $(\tilde\mu^n,X^n(0),I^n(0))$, $(u_i)$, $S^n$, $(U_i)$, $N^n$ are mutually independent (the joint law of the first block is arbitrary);
--   3. almost every path satisfies the system equations;
--   4. the routing is non-anticipating: $\tilde\mu^n,X^n(0),I^n(0)$ are $\mathcal G_0$-measurable, $X^n,I^n_k,R^n_k$ are adapted, and for every $t$ (a) the potential completions after $t$ (increments of $S^n$ after the clock $(\sum_j\tilde\mu^n_j)t$, with their marks) are independent of $\mathcal G_t$, (b) the abandonment clock $r\mapsto N^n(\Lambda(t)+r)-N^n(\Lambda(t))$, $\Lambda(t)=\gamma\int_0^t(X^n-n)^+$, is independent of $\mathcal G_t$ and is again a unit Poisson process, and (c) the interarrival times after the one in progress at $t$ are independent of $\mathcal G_t$.
--
--   `IsModelSeq` asks this for every $n$, together with the standing assumptions on the data, $\gamma\ge0$ and $\lambda_n>0$.
--
--   This is the class of systems—arbitrary non-idling, non-anticipating, non-preemptive routing—for which the paper's results are stated.
--
--   **Formalization Note** Non-anticipation is a reading of the paper's one-line description; it permits routing rules that use the past and independent randomization. The martingale property of the service and abandonment processes is a consequence and is not assumed. All systems live on one probability space; only their laws matter.
-- source:
--   Büke and Qin, Many-Server Queues with Random Service Rates in the Halfin-Whitt Regime, arXiv:1905.04198v1, §3, pp.5–7 (primitives, independence, non-anticipating policies, the filtration Fⁿ on p.7)

import Mathlib
import Definitions.Def_RandomRateMSQ_System

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace RandomRateMSQ

/-- The uniform(0,1) law on `ℝ`. -/
noncomputable def uniformLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

namespace System

variable {Ω : Type*} {n : ℕ} (s : System Ω n)

/-- The potential completions after time `t`, as seen in the unit clock of `Sⁿ`: the increments
`r ↦ Sⁿ(c + r) − Sⁿ(c)` after `c = (Σⱼ µ̃ⁿⱼ) t`, together with the marks `Uⁿ_{Sⁿ_P(t)+1+j}`,
`j ≥ 0`, of the potential completions not yet occurred. -/
noncomputable def futurePotential (t : ℝ≥0) (ω : Ω) : (ℝ≥0 → ℕ) × (ℕ → ℝ) :=
  (fun r => s.unitCount ω (s.totalRate ω * t + r) - s.unitCount ω (s.totalRate ω * t),
    fun j => s.U (s.potential ω t + 1 + j) ω)

/-- The abandonment clock after time `t`: `r ↦ Nⁿ(Λ(t) + r) − Nⁿ(Λ(t))` with
`Λ(t) = γ ∫₀ᵗ (Xⁿ(s) − n)⁺ ds`. -/
noncomputable def futureAbandon (γ : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ≥0 → ℕ :=
  fun r => s.abandonClock ω (γ * s.cumOverflow ω t + r) - s.abandonClock ω (γ * s.cumOverflow ω t)

/-- The interarrival times `uⁿ_{Aⁿ(t)+2+j}`, `j ≥ 0`, of the arrivals after the one in progress at
time `t`. -/
noncomputable def futureGaps (lam : ℝ) (t : ℝ≥0) (ω : Ω) : ℕ → ℝ :=
  fun j => s.u (s.arrivals lam ω t + 2 + j) ω

end System

/-- The **`n`-th system satisfies the model** of arXiv:1905.04198v1, §3, pp.5–7, with interarrival
law `F_u`, rate law `F`, arrival rate `λₙ = lam`, abandonment rate `γ`, under the filtration `G`:

1. *Primitives.* `uⁿᵢ` i.i.d. with law `F_u`; `µ̃ⁿₖ` i.i.d. with law `F`; the gaps of `Sⁿ` and of
   `Nⁿ` i.i.d. exponential(1) (so `Sⁿ`, `Nⁿ` are unit-rate Poisson processes); `Uⁿᵢ` i.i.d.
   uniform(0,1) (pp.5–6).
2. *Independence.* The five blocks `(µ̃ⁿ, Xⁿ(0), Iⁿ(0))`, `(uⁿᵢ)`, `Sⁿ`, `(Uⁿᵢ)`, `Nⁿ` are mutually
   independent ("independent of other processes defined so far", p.6); the joint law of
   `(µ̃ⁿ, Xⁿ(0), Iⁿ(0))` is otherwise arbitrary.
3. *System equations.* Almost every path satisfies `System.SystemEqs` (pp.5–6).
4. *Non-anticipation* ("when the routing is done the server is chosen based on the information
   available so far", p.5). `G` is a filtration with `µ̃ⁿ, Xⁿ(0), Iⁿ(0)` `G₀`-measurable and
   `Xⁿ, Iⁿₖ, Rⁿₖ` adapted (so `G` contains the paper's `Fⁿ`, p.7, apart from the primitives'
   futures), and for every `t`:
   (a) the potential completions after `t` (`System.futurePotential`) are independent of `G_t`;
   (b) the abandonment clock after `t` (`System.futureAbandon`) is independent of `G_t` and is
       again a unit-rate Poisson process (has the law of `Nⁿ`);
   (c) the interarrival times after the one in progress at `t` (`System.futureGaps`) are
       independent of `G_t`.
   A routing rule may use the past of the system and independent randomization.

**Formalization Note.** Non-anticipation is a reading of the one-line description on p.5. The
martingale property of `Dⁿₖ − µ̃ⁿₖ ∫(1 − Iⁿₖ)` is a consequence (p.17) and is not assumed. -/
def IsModel {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (Fu : Measure ℝ)
    (F : Measure ℝ≥0) (lam γ : ℝ) {n : ℕ} (G : Filtration ℝ≥0 mΩ) (s : System Ω n) : Prop :=
  (∀ i, Measurable (s.u i) ∧ P.map (s.u i) = Fu) ∧ iIndepFun s.u P ∧
  (∀ k, Measurable (s.rate k) ∧ P.map (s.rate k) = F) ∧ iIndepFun s.rate P ∧
  (∀ i, Measurable (s.e i) ∧ P.map (s.e i) = expMeasure 1) ∧ iIndepFun s.e P ∧
  (∀ i, Measurable (s.U i) ∧ P.map (s.U i) = uniformLaw) ∧ iIndepFun s.U P ∧
  (∀ i, Measurable (s.b i) ∧ P.map (s.b i) = expMeasure 1) ∧ iIndepFun s.b P ∧
  iIndep ![MeasurableSpace.comap
      (fun ω => ((fun k => s.rate k ω), s.X ω 0, (fun k => s.I k ω 0))) inferInstance,
    MeasurableSpace.comap (fun ω i => s.u i ω) inferInstance,
    MeasurableSpace.comap (fun ω i => s.e i ω) inferInstance,
    MeasurableSpace.comap (fun ω i => s.U i ω) inferInstance,
    MeasurableSpace.comap (fun ω i => s.b i ω) inferInstance] P ∧
  (∀ᵐ ω ∂P, s.SystemEqs lam γ ω) ∧
  (∀ k, Measurable[G 0] (s.rate k)) ∧ Measurable[G 0] (fun ω => s.X ω 0) ∧
  (∀ k, Measurable[G 0] (fun ω => s.I k ω 0)) ∧
  (∀ t, Measurable[G t] (fun ω => s.X ω t) ∧
    ∀ k, Measurable[G t] (fun ω => s.I k ω t) ∧ Measurable[G t] (fun ω => s.R k ω t)) ∧
  (∀ t, Indep (MeasurableSpace.comap (s.futurePotential t) inferInstance) (G t) P) ∧
  (∀ t, Indep (MeasurableSpace.comap (s.futureAbandon γ t) inferInstance) (G t) P ∧
    IdentDistrib (s.futureAbandon γ t) (fun ω (r : ℝ≥0) => s.abandonClock ω r) P P) ∧
  (∀ t, Indep (MeasurableSpace.comap (s.futureGaps lam t) inferInstance) (G t) P)

/-- The **sequence of systems** `n = 0, 1, 2, …` satisfies the model: the data satisfy
`StandingData`, the abandonment rate is `γ ≥ 0`, every arrival rate `λₙ` is positive, and the
`n`-th system satisfies `IsModel` with filtration `G n` (arXiv:1905.04198v1, §3, pp.5–7).

**Formalization Note.** All systems live on one probability space `(Ω, P)`; only the law of each
system enters the results, and systems given on separate spaces can be placed on their product.
`γ = 0` (no abandonment) is allowed. -/
def IsModelSeq {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (Fu : Measure ℝ)
    (F : Measure ℝ≥0) (lam : ℕ → ℝ) (γ : ℝ) (G : ℕ → Filtration ℝ≥0 mΩ)
    (sys : ∀ n, System Ω n) : Prop :=
  StandingData Fu F ∧ 0 ≤ γ ∧ (∀ n, 0 < lam n) ∧ ∀ n, IsModel P Fu F (lam n) γ (G n) (sys n)

end RandomRateMSQ


