-- Prove2me | Definitions.Def_KurtzProtter91_Integrals_Semimartingale
-- name    : KurtzProtter91_Integrals_Semimartingale
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:00:50.13993+00:00
-- url     : https://prove2.me/theorems/c070b2d2-567b-4d46-bbd4-47ee62d4b50f
-- title:
--   Pp. 1036–1039 — the stochastic integral (1.7), semimartingales, the bracket, condition C2.2(i), and ⇒ in the Skorohod topology
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\{\mathcal F_t\}_{t\ge0}$. Processes are maps $[0,\infty)\times\Omega\to E$.
--
--   1. **Stochastic integral** (1.7), p. 1036. For a $k\times m$-matrix-valued $X$ and an $\mathbb R^m$-valued $Y$, a process $Z$ is $\int X\,dY=\int X(s-)\,dY(s)$ if $Z$ has cadlag paths and, for every $t$ and every sequence of partitions $\{t_i\}$ of $[0,t]$ whose mesh tends to zero,
--   $$\sum_i X(t_i)\big(Y(t_{i+1})-Y(t_i)\big)\longrightarrow Z(t)\qquad\text{in probability.}$$
--   2. **Finite variation.** $A$ has finite variation on bounded time intervals if for every $t$, $T_t(A)=\sup\sum_i|A(t_{i+1})-A(t_i)|<\infty$ a.s., the supremum over partitions of $[0,t]$.
--   3. **Semimartingale** (p. 1039). A cadlag, $\{\mathcal F_t\}$-adapted, $\mathbb R^m$-valued $Y$ is an $\{\mathcal F_t\}$-semimartingale if $Y=M+A$ with each component of $M$ an $\{\mathcal F_t\}$-local martingale (cadlag paths) and $A$ of finite variation on bounded time intervals.
--   4. **Bracket.** $[M]=\sum_j[M_j]$, where $[M_j](t)$ is the limit in probability of the sums of squared increments of $M_j$ over the dyadic partitions of $[0,t]$; $[M]$ is taken with cadlag nondecreasing paths, and $[M](0)=0$.
--   5. **Condition C2.2(i)** (p. 1039). For processes $V_n$ on $(\Omega_n,\mathcal F^n,P_n)$ (in Theorem 2.2, $V_n=Y^\delta_n=Y_n-J_\delta(Y_n)$): there are decompositions $V_n=M_n+A_n$ into an $\{\mathcal F^n_t\}$-local martingale and a finite-variation process such that for each $\alpha>0$ there are $\{\mathcal F^n_t\}$-stopping times $\tau^\alpha_n$ with
--   $$P_n\{\tau^\alpha_n\le\alpha\}\le 1/\alpha\quad\text{and}\quad \sup_n E\Big[[M_n]_{t\wedge\tau^\alpha_n}+T_{t\wedge\tau^\alpha_n}(A_n)\Big]<\infty\ \text{ for every } t\ge0.$$
--   6. **Convergence in distribution in the Skorohod topology**, $V_n\Rightarrow V$ in $D_E[0,\infty)$, for processes on possibly different probability spaces: there is a probability space carrying path-valued random variables $W_n$, $W$ such that $W_n$ has the law of the path of $V_n$, $W$ has the law of the path of $V$, and $W_n(\omega)\to W(\omega)$ in the Skorohod topology for almost every $\omega$.
--
--   These are the probabilistic objects of Theorem 2.2 and of the estimate (2.7).
--
--   **Formalization Note** Local martingales are the published `EthierKurtz.IsSourceLocalMartingale` (a localizing sequence whose stopped processes are martingales), applied componentwise. The paper asks for *uniformly integrable* stopped martingales; the two notions agree, since replacing $\tau_k$ by $\tau_k\wedge k$ makes every stopped martingale uniformly integrable. The bracket uses the published `EthierKurtz.HasCrossVariation`, whose convention is $[M](0)=0$; Protter's convention $[M](0)=M(0)^2$ differs by $M(0)^2$, and since C2.2(i) asks only for *some* decomposition, moving $M(0)$ into $A$ (which leaves $T_t(A)$ unchanged) shows the two readings of C2.2(i) agree. The free $t$ in C2.2(i) is read as "for every $t\ge0$" (as C4.1 on p. 1049 states explicitly), with the stopping times chosen before $t$; $t\wedge\tau$ is $t$ when $\tau=\infty$; expectations of the nonnegative quantities are lower Lebesgue integrals in $[0,\infty]$. $T_t(A)$ is computed with the sup norm; finiteness and the bound in C2.2(i) do not depend on the norm on $\mathbb R^m$. The stochastic integral is unique up to indistinguishability because of the cadlag requirement. Convergence in distribution is stated in coupling (Skorohod-representation) form for Polish $E$ with its Borel σ-algebra; laws are taken on the product σ-algebra of `ℝ≥0 → E`, which restricted to $D_E[0,\infty)$ is the Borel σ-algebra of the Skorohod topology (Ethier–Kurtz, Prop. 3.7.1), so the coupling form is equivalent to weak convergence of the laws. Measurability of the path maps is part of "same law" (`IdentDistrib`).
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1036 ((1.7), ⇒), p. 1039 (semimartingales, Theorem 2.2, C2.2(i)), p. 1040 (Remark 2.3)

import Mathlib
import Definitions.Def_EthierKurtz_IsSourceLocalMartingale
import Definitions.Def_EthierKurtz_HasCrossVariation
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

/-- The stochastic integral (1.7), p. 1036: `Z = ∫X dY = ∫X(s −) dY(s)` if `Z` has cadlag paths
and, for every `t` and every sequence of partitions of `[0, t]` with mesh tending to zero, the
left-point Riemann sums `∑_i X(t_i)(Y(t_{i+1}) − Y(t_i))` converge in `P`-probability to `Z(t)`. -/
def HasStochIntegral {Ω : Type*} [MeasurableSpace Ω] {k m : ℕ} (P : Measure Ω)
    (X : ℝ≥0 → Ω → Fin k → Fin m → ℝ) (Y : ℝ≥0 → Ω → Fin m → ℝ) (Z : ℝ≥0 → Ω → Fin k → ℝ) :
    Prop :=
  (∀ ω, IsCadlag fun t => Z t ω) ∧
    ∀ (t : ℝ≥0) (ps : ℕ → Partition t), Tendsto (fun n => (ps n).mesh) atTop (𝓝 0) →
      TendstoInMeasure P
        (fun n ω => riemannSum (ps n) (fun s => X s ω) (fun s => Y s ω)) atTop (Z t)

/-- `A` has sample paths of finite variation on bounded time intervals: for every `t`,
`T_t(A) = sup ∑ |A(t_{i+1}) − A(t_i)| < ∞` a.s. (supremum over partitions of `[0, t]`). -/
def HasFiniteVariation {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (P : Measure Ω)
    (A : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  ∀ t : ℝ≥0, ∀ᵐ ω ∂P, eVariationOn (fun s => A s ω) (Set.Icc 0 t) ≠ ⊤

/-- `Y = M + A` is a decomposition of `Y` into an `{𝓕_t}`-local martingale `M` (each component a
local martingale, cadlag paths) and a process `A` whose paths have finite variation on bounded
intervals. -/
def IsSemimartingaleDecomp {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (𝓕 : Filtration ℝ≥0 ‹_›)
    (P : Measure Ω) (Y M A : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  (∀ t ω, Y t ω = M t ω + A t ω) ∧
    (∀ j, EthierKurtz.IsSourceLocalMartingale P 𝓕 fun t ω => M t ω j) ∧
    (∀ ω, IsCadlag fun t => M t ω) ∧ HasFiniteVariation P A

/-- An `ℝ^m`-valued `{𝓕_t}`-semimartingale (p. 1039): a cadlag, `{𝓕_t}`-adapted process that
decomposes as `Y = M + A` with `M` an `{𝓕_t}`-local martingale and `A` of finite variation on
bounded time intervals (componentwise). -/
def IsSemimartingale {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (𝓕 : Filtration ℝ≥0 ‹_›)
    (P : Measure Ω) (Y : ℝ≥0 → Ω → Fin m → ℝ) : Prop :=
  (∀ ω, IsCadlag fun t => Y t ω) ∧ Adapted 𝓕 Y ∧
    ∃ M A : ℝ≥0 → Ω → Fin m → ℝ, IsSemimartingaleDecomp 𝓕 P Y M A

/-- `Q = [M] = ∑_j [M_j]` is the quadratic variation of the `ℝ^m`-valued `M`: `Q` has cadlag,
nondecreasing paths and `Q = ∑_j Q_j` with each `Q_j(t)` the limit in probability of the sums of
squared increments of `M_j` over the dyadic partitions of `[0, t]` (so `Q(0) = 0`). -/
def HasBracket {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (P : Measure Ω)
    (M : ℝ≥0 → Ω → Fin m → ℝ) (Q : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, IsCadlag fun t => Q t ω) ∧ (∀ ω, Monotone fun t => Q t ω) ∧
    ∃ Qj : Fin m → ℝ≥0 → Ω → ℝ,
      (∀ j, EthierKurtz.HasCrossVariation P (fun t ω => M t ω j) (fun t ω => M t ω j) (Qj j)) ∧
        ∀ t ω, Q t ω = ∑ j, Qj j t ω

/-- `t ∧ τ` for a deterministic `t` and a `[0, ∞]`-valued time `τ` (equal to `t` when `τ = ∞`). -/
def minTop (t : ℝ≥0) (τ : WithTop ℝ≥0) : ℝ≥0 :=
  min t (τ.untopD t)

/-- **Condition C2.2(i)** for a sequence `V_n` (`V_n = Y_n^δ` in Theorem 2.2), p. 1039: there are
decompositions `V_n = M_n + A_n` into an `{𝓕^n_t}`-local martingale and a finite-variation
process, with brackets `[M_n]`, such that for each `α > 0` there are `{𝓕^n_t}`-stopping times
`τ_n^α` with `P_n{τ_n^α ≤ α} ≤ 1/α` and, for every `t ≥ 0`,
`sup_n E[[M_n]_{t∧τ_n^α} + T_{t∧τ_n^α}(A_n)] < ∞`. -/
def SatisfiesC22i {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {m : ℕ}
    (P : ∀ n, Measure (Ω n)) (𝓕 : ∀ n, Filtration ℝ≥0 (‹∀ n, MeasurableSpace (Ω n)› n))
    (V : ∀ n, ℝ≥0 → Ω n → Fin m → ℝ) : Prop :=
  ∃ (M A : ∀ n, ℝ≥0 → Ω n → Fin m → ℝ) (Q : ∀ n, ℝ≥0 → Ω n → ℝ),
    (∀ n, IsSemimartingaleDecomp (𝓕 n) (P n) (V n) (M n) (A n)) ∧
    (∀ n, HasBracket (P n) (M n) (Q n)) ∧
    ∀ α : ℝ≥0, 0 < α → ∃ τ : ∀ n, Ω n → WithTop ℝ≥0,
      (∀ n, IsStoppingTime (𝓕 n) (τ n)) ∧
      (∀ n, P n {ω | τ n ω ≤ (α : WithTop ℝ≥0)} ≤ (α : ℝ≥0∞)⁻¹) ∧
      ∀ t : ℝ≥0, (⨆ n, ∫⁻ ω, (ENNReal.ofReal (Q n (minTop t (τ n ω)) ω) +
          eVariationOn (fun s => A n s ω) (Set.Icc 0 (minTop t (τ n ω)))) ∂(P n)) < ⊤

/-- **Convergence in distribution in the Skorohod topology**, `V_n ⇒ V` in `D_E[0, ∞)`, in
coupling (Skorohod-representation) form: there is a probability space carrying path-valued random
variables `W_n`, `W` with `W_n` distributed as the path of `V_n` (under `P_n`), `W` distributed as
the path of `V` (under `P'`), and `W_n(ω) → W(ω)` in the Skorohod topology for a.e. `ω`. Laws are
taken on the product σ-algebra of `[0, ∞) → E`. -/
def SkorohodConvInDist {E : Type*} [MetricSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (V : ∀ n, ℝ≥0 → Ω n → E) {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (V' : ℝ≥0 → Ω' → E) : Prop :=
  ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (P'' : Measure Ω'') (W : ℕ → Ω'' → ℝ≥0 → E)
      (W' : Ω'' → ℝ≥0 → E),
    IsProbabilityMeasure P'' ∧
    (∀ n, IdentDistrib (W n) (fun ω t => V n t ω) P'' (P n)) ∧
    IdentDistrib W' (fun ω t => V' t ω) P'' P' ∧
    ∀ᵐ ω ∂P'', SkorohodTendsto (fun n => W n ω) (W' ω)

end KurtzProtter91.Integrals


