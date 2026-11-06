-- Prove2me | Definitions.Def_SemiBanditSOO_Algorithm
-- name    : SemiBanditSOO_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:58.714554+00:00
-- url     : https://prove2.me/theorems/4dc2140a-ff6e-467a-8333-2dce3fbce3e5
-- title:
--   Algorithm 1 (optimistic DP), Assumption 3.1, the regret $R_T$ and the good events $G_t$
-- statement:
--   **Algorithm 1** (input $\delta\in(0,1)$; $\Lambda=\log(80n(T+1)^3/\delta)$). In each round $t=1,\dots,T$ a vector $X^t\sim D$ is drawn independently of the past. The algorithm sets $\mathcal C_{i,t}=\mathcal C_{N_{i,t}}(\widehat D_{i,N_{i,t}})$ for every coordinate $i$, where $N_{i,t}$ is the number of rounds before $t$ in which coordinate $i$ was revealed and $\widehat D_{i,N_{i,t}}$ is the empirical distribution of its revealed values; it evaluates the optimistic DP with these sets, walks from the root choosing children by (3.5), and finally adds the values revealed in round $t$ (the semi-bandit feedback $X^t_{\mathrm{obs}(\ell^t)}$) to the samples. With $\sigma^t$ the resulting policy of round $t$, the **cumulative expected regret** is
--   $$R_T=\sum_{t=1}^T\bigl(\mathrm{OPT}(D)-\mathbb E[f(\sigma^t,X^t)]\bigr),$$
--   and $\mathrm{Reg}_t=\mathrm{OPT}(D)-f(\sigma^t\mid D)$. The **good event** $G_t$ is $\{D_i\in\mathcal C_{i,t}\ \forall i\}$, and $I_{i,t}$ indicates that coordinate $i$ is revealed on an edge in round $t$. The cumulative gaps and conditional variances of the good rounds are $\Delta=\sum_t\mathbb E[\mathbf 1_{G_t}\sum_h d_{t,h}]$ and $W=\sum_t\mathbb E[\mathbf 1_{G_t}\sum_h w_{t,h}]$, and $\widetilde w_{i,t}$ is $w_{t,h}$ at the stage $h$ revealing coordinate $i$.
--
--   **Assumption 3.1.** There are $s_1,\dots,s_n\in\mathbb Z_{>0}\cup\{\infty\}$ such that, for any nonempty sets $\mathcal P_1,\dots,\mathcal P_n$ of distributions on the domains, with $\bar g$ defined by (3.3)–(3.4) with $\mathcal P_i$ in place of $\mathcal C_{i,t}$, for every edge $(u,v)$ revealing coordinate $i$ and all observations with $v\in\mathcal A_u(x_{\mathrm{obs}(u)})$, the function $z\mapsto\bar g_v(z,x_{\mathrm{obs}(u)})$ has level-set complexity at most $s_i$.
--
--   Finally, $S=\sum_{i=1}^n\min\{s_i,k_i\}$, with $k_i$ the number of support points of $D_i$, and the paper's measurability assumption (p.10) is that the optimistic values are measurable in the samples and the observations.
--
--   **Formalization Note.** Algorithm 1 is deterministic, so its run is a function of the round vectors $\omega=(X^1,\dots,X^T)$ under the product measure; rounds are numbered $0,\dots,T-1$. Assumption 3.1 is required only for families whose optimistic DP is measurable, a weaker hypothesis than the paper's (the paper applies it only to the confidence sets, which are of this kind). The measurability assumption is stated along the algorithm's own history: for every round $t<T$, $\bar g^t_u$ and $\bar h^t_{(u,v)}$ are jointly measurable in $\omega$ and the observations. $\mathbb E[\mathbf 1_{G_t}\mathrm{Reg}_t]$, $\Delta$ and $W$ are lower Lebesgue integrals.
-- source:
--   Harada, Kawase, Sumita, Beyond Monotonicity: Stochastic Online Optimization under Semi-Bandit Feedback, arXiv:2611.02739v1, Algorithm 1, p.10; Assumption 3.1, pp.10–11; R_T, p.7; Theorem 3.2, p.11 (S); proof of Theorem 3.2, pp.24–25 (G_t, I_{i,t})

import Mathlib
import Definitions.Def_SemiBanditSOO_Model
import Definitions.Def_SemiBanditSOO_LevelSet
import Definitions.Def_SemiBanditSOO_ConfidenceSet
import Definitions.Def_SemiBanditSOO_OptimisticDP

open MeasureTheory

namespace SemiBanditSOO

/-- `S = Σ_{i=1}^n min{s_i, k_i}` (Theorem 3.2, p.11), with `k_i` the number of support points of
`D_i`; `s̄_i = min{s_i, k_i}` (proof of Theorem 3.2, p.25). An element of `ℕ∞`. -/
noncomputable def totalCpx {n : ℕ} {dom : Fin n → Set ℝ} (s : Fin n → ℕ∞)
    (D : ∀ i, ProbabilityMeasure (dom i)) : ℕ∞ :=
  ∑ i, min (s i) (supportCount (D i : Measure (dom i)))

/-- The confidence-set family `𝒞_{i} = 𝒞_{N_i}(D̂_{i,N_i})` built from the samples `L i` of each
coordinate (Algorithm 1, line 2, p.10). -/
noncomputable def confFamily {n : ℕ} {dom : Fin n → Set ℝ} (Λ : ℝ) (L : ∀ i, List (dom i)) : ∀ i, Set (ProbabilityMeasure (dom i)) :=
  fun i => confSet Λ (L i)

/-- The i.i.d. round vectors `X^1, …, X^T ∼ D` (§2.1, p.7). -/
noncomputable def roundsMeasure {n : ℕ} {dom : Fin n → Set ℝ} (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) :
    Measure (Fin T → Obs dom) :=
  Measure.pi fun _ : Fin T => prodDist D

namespace Problem

variable {n : ℕ} {dom : Fin n → Set ℝ} {V : Type} (Pb : Problem n dom V)

/-- **Assumption 3.1** (pp.10–11). Harada, Kawase, Sumita, *Beyond Monotonicity: Stochastic Online
Optimization under Semi-Bandit Feedback*, arXiv:2611.02739v1, Assumption 3.1, pp.10–11: for any
nonempty sets `𝒫_1, …, 𝒫_n` of distributions on the domains, with `ḡ` defined by (3.3)–(3.4) with
`𝒫_i` in place of `𝒞_{i,t}`, for every edge `(u, v)` revealing coordinate `i` and all observations
`x_obs(u)` with `v ∈ 𝒜_u(x_obs(u))`, the function `z ↦ ḡ_v(z, x_obs(u))` has level-set complexity
at most `s_i`.

**Formalization Note.** The families range over those whose optimistic DP is measurable
(`MeasurableDP`), so that every expectation in (3.4) is a genuine integral and never Lean's junk
value `0` for a non-measurable integrand. This is a weaker hypothesis than the paper's (fewer
families to check); the paper only applies the assumption to the confidence sets of Algorithm 1,
whose DP is measurable by the paper's measurability assumption (p.10). -/
def Assumption31 (s : Fin n → ℕ∞) : Prop :=
  ∀ P : ∀ i, Set (ProbabilityMeasure (dom i)), (∀ i, (P i).Nonempty) → Pb.MeasurableDP P →
    ∀ u, ∀ v ∈ Pb.children u, ∀ i, Pb.edgeCoord u v = some i →
      ∀ x : Obs dom, v ∈ Pb.feasible u x →
        LevelSetCpxLE (s i) (fun z : dom i => Pb.optVal P v (Function.update x i z))

variable [LinearOrder V]

/-- The leaf reached in a round whose samples are `L`, on the realization `x` (Algorithm 1,
lines 4–7, p.10). -/
noncomputable def roundLeaf (Λ : ℝ) (L : ∀ i, List (dom i)) (x : Obs dom) : V :=
  Pb.leafOf (Pb.greedy (confFamily Λ L)) x

/-- **The samples of Algorithm 1** (p.10). For the round vectors `ω = (X^1, …, X^T)` and a round
index `t` (0-based), `samplesAt Λ T ω t i` is the list `Z_{i,1}, …, Z_{i,N_{i,t}}` of the values of
coordinate `i` revealed in the rounds before round `t`, in order. In each round the algorithm runs
the choice rule (3.5) for the confidence sets built from the current samples and then adds the
values revealed in that round, i.e. the coordinates in `obs(ℓ^t)` (line 8 and the semi-bandit
feedback `X^t_{obs(ℓ^t)}`, p.7). No samples are added after round `T`.

**Formalization Note.** Algorithm 1 is deterministic given its input `δ` (through `Λ`), so the
whole run is a function of the `T` round vectors. Rounds are numbered `0, …, T − 1`. -/
noncomputable def samplesAt (Λ : ℝ) (T : ℕ) (ω : Fin T → Obs dom) : ℕ → ∀ i, List (dom i)
  | 0 => fun _ => []
  | t + 1 => fun i =>
    if h : t < T then
      samplesAt Λ T ω t i ++
        (if i ∈ Pb.obs (Pb.roundLeaf Λ (samplesAt Λ T ω t) (ω ⟨t, h⟩)) then [ω ⟨t, h⟩ i] else [])
    else samplesAt Λ T ω t i

/-- The policy `σ^t` of Algorithm 1 in round `t` (0-based), with `Λ = Lam n T δ`: the choice rule
(3.5) for the confidence sets `𝒞_{i,t}` of the samples before round `t`. -/
noncomputable def roundPolicy (T : ℕ) (δ : ℝ) (ω : Fin T → Obs dom) (t : ℕ) : V → Obs dom → V :=
  Pb.greedy (confFamily (Lam n T δ) (Pb.samplesAt (Lam n T δ) T ω t))

/-- **The cumulative expected regret of Algorithm 1** (§2.1, p.7):
`R_T = Σ_{t=1}^T (OPT(D) − 𝔼[f(σ^t, X^t)])`, where `σ^t` is the policy of Algorithm 1 with input
`δ` in round `t` and the expectation is over the i.i.d. round vectors. -/
noncomputable def regret (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ) : ℝ :=
  ∑ t : Fin T, (Pb.OPT D -
    ∫ ω, Pb.payoff (Pb.roundPolicy T δ ω t) (ω t) ∂(roundsMeasure D T))

/-- `Reg_t = OPT(D) − f(σ^t | D)` (p.7), as a function of the history `ω` (it depends on `ω` only
through the rounds before `t`). -/
noncomputable def roundRegret (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ)
    (ω : Fin T → Obs dom) (t : ℕ) : ℝ :=
  Pb.OPT D - Pb.value D (Pb.roundPolicy T δ ω t)

/-- The good event `G_t` (proof of Theorem 3.2, p.24): `D_i ∈ 𝒞_{i,t}` for every `i`. -/
def goodEvent (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ) (t : ℕ) :
    Set (Fin T → Obs dom) :=
  {ω | ∀ i, D i ∈ confSet (Lam n T δ) (Pb.samplesAt (Lam n T δ) T ω t i)}

/-- `𝔼[1_{G_t} Reg_t]` (5.8), p.24.

**Formalization Note.** A lower Lebesgue integral of `ofReal`, so that no measurability of `G_t`
needs to be proved for the expression to have its intended value. -/
noncomputable def goodRegret (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ) (t : ℕ) :
    ENNReal :=
  ∫⁻ ω, (Pb.goodEvent D T δ t).indicator
    (fun ω => ENNReal.ofReal (Pb.roundRegret D T δ ω t)) ω ∂(roundsMeasure D T)

/-- `I_{i,t}`: coordinate `i` is revealed on an edge in round `t` (proof of Theorem 3.2, p.25),
i.e. `i ∈ obs(ℓ^t) \ obs(r)`. -/
def revealedOnEdge (T : ℕ) (δ : ℝ) (ω : Fin T → Obs dom) (t : Fin T) (i : Fin n) : Prop :=
  i ∈ Pb.obs (Pb.leafOf (Pb.roundPolicy T δ ω t) (ω t)) ∧ i ∉ Pb.obs Pb.root

/-- The confidence-set family `𝒞_{i,t}` of round `t` (0-based) on the history `ω`, with
`Λ = Lam n T δ` (Algorithm 1, line 2, p.10). -/
noncomputable def roundFamily (T : ℕ) (δ : ℝ) (ω : Fin T → Obs dom) (t : ℕ) :
    ∀ i, Set (ProbabilityMeasure (dom i)) :=
  confFamily (Lam n T δ) (Pb.samplesAt (Lam n T δ) T ω t)

/-- `Δ = Σ_{t=1}^T 𝔼[1_{G_t} Σ_h d_{t,h}]`, the cumulative gaps in good rounds (proof of
Theorem 3.2, p.25).

**Formalization Note.** `Σ_h d_{t,h}` is the sum of the stage gaps along the path of `σ^t` on `X^t`
(`pathSum`, the paper's explicit expressions, p.25); on `G_t` it is nonnegative. As for `goodRegret`,
the expectation is a lower Lebesgue integral of `ofReal`, over the round vectors. -/
noncomputable def goodGap (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ) : ENNReal :=
  ∑ t : Fin T, ∫⁻ ω, (Pb.goodEvent D T δ t).indicator
    (fun ω => ENNReal.ofReal (Pb.pathSum (Pb.roundPolicy T δ ω t)
      (Pb.stageGap D (Pb.roundFamily T δ ω t)) (ω t))) ω ∂(roundsMeasure D T)

/-- `W = Σ_{t=1}^T 𝔼[1_{G_t} Σ_h w_{t,h}]`, the cumulative conditional variances in good rounds
(proof of Theorem 3.2, p.25), with the same conventions as `goodGap`. -/
noncomputable def goodVar (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ) : ENNReal :=
  ∑ t : Fin T, ∫⁻ ω, (Pb.goodEvent D T δ t).indicator
    (fun ω => ENNReal.ofReal (Pb.pathSum (Pb.roundPolicy T δ ω t)
      (Pb.stageVar D (Pb.roundFamily T δ ω t)) (ω t))) ω ∂(roundsMeasure D T)

open Classical in
/-- `w̃_{i,t}` (proof of Theorem 3.2, p.25): the conditional variance `w_{t,h}` of the stage `h` at
which coordinate `i` is revealed on an edge in round `t`, and `0` if there is no such stage. A
coordinate is revealed at most once per round, so the sum along the path has at most one nonzero
term. -/
noncomputable def revealVar (D : ∀ i, ProbabilityMeasure (dom i)) (T : ℕ) (δ : ℝ)
    (ω : Fin T → Obs dom) (t : Fin T) (i : Fin n) : ℝ :=
  Pb.pathSum (Pb.roundPolicy T δ ω t)
    (fun u v x => if Pb.edgeCoord u v = some i then
      Pb.stageVar D (Pb.roundFamily T δ ω t) u v x else 0) (ω t)

open Classical in
/-- The left-hand side of (5.15), p.26: `𝔼[Σ_{t,i} 1_{G_t} I_{i,t} √(s̄_i w̃_{i,t}/(N_{i,t} + 1))]`,
with `s̄_i = min{s_i, k_i}` and `N_{i,t}` the length of the sample list of coordinate `i` before
round `t`. A lower Lebesgue integral, as for `goodRegret`. -/
noncomputable def goodRootSum (D : ∀ i, ProbabilityMeasure (dom i)) (s : Fin n → ℕ∞) (T : ℕ)
    (δ : ℝ) : ENNReal :=
  ∫⁻ ω, ∑ t : Fin T, ∑ i, (Pb.goodEvent D T δ t).indicator
    (fun ω => if Pb.revealedOnEdge T δ ω t i then
      ENNReal.ofReal (Real.sqrt
        (((min (s i) (supportCount (D i : Measure (dom i)))).toNat : ℝ) *
          Pb.revealVar D T δ ω t i /
          ((Pb.samplesAt (Lam n T δ) T ω t i).length + 1)))
      else 0) ω ∂(roundsMeasure D T)

/-- **The standing measurability assumption of Algorithm 1** (p.10: "for infinite domains, we
assume that the optimistic values are measurable in the samples and observations"): for every
round `t < T`, the optimistic values `ḡ^t_u` and `h̄^t_(u,v)` (on edges) are jointly measurable
functions of the history `ω` (through the samples) and of the observations.

**Formalization Note.** Stated along the algorithm's own samples, as functions of the round
vectors. The paper's assumption (measurability in the sample values and the observations) implies
it, because the samples are measurable functions of the history; for finite domains it holds
automatically (p.10). -/
def StandingMeasurable (T : ℕ) (δ : ℝ) : Prop :=
  ∀ t < T, ∀ u : V,
    Measurable (fun p : (Fin T → Obs dom) × Obs dom =>
      Pb.optVal (confFamily (Lam n T δ) (Pb.samplesAt (Lam n T δ) T p.1 t)) u p.2) ∧
    ∀ v ∈ Pb.children u, Measurable (fun p : (Fin T → Obs dom) × Obs dom =>
      Pb.edgeVal (confFamily (Lam n T δ) (Pb.samplesAt (Lam n T δ) T p.1 t)) u v p.2)

end Problem

end SemiBanditSOO


