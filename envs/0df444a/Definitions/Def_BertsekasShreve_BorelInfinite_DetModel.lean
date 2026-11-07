-- Prove2me | Definitions.Def_BertsekasShreve_BorelInfinite_DetModel
-- name    : BertsekasShreve_BorelInfinite_DetModel
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-11-07T05:38:35.525644+00:00
-- url     : https://prove2.me/theorems/2d6696d5-e1d1-407a-9bbf-2381e04d1d7e
-- title:
--   The deterministic model (DM) on $P(S)$: $\bar U$, $\bar f$, $\bar g$, policies, $\bar J_{\bar\pi}$, $\bar J^*$ and $\bar T$ (Defs 9.4–9.8)
-- statement:
--   Let (SM) $=(S,C,U,W,p,f,\alpha,g)$ be the infinite horizon stochastic optimal control model of Definitions 8.1 and 9.1, with $\Gamma=\{(x,u)\mid u\in U(x)\}$ and transition kernel $t(dx'\mid x,u)$. The corresponding **infinite horizon deterministic optimal control model** (DM) of Definition 9.4 has state space $P(S)$, control space $P(SC)$, and
--
--   1. control constraint $\bar U(p)=\{q\in P(SC)\mid q(\Gamma)=1,\ \text{the marginal of } q \text{ on } S \text{ is } p\}$ (Eq. (6));
--   2. system function $\bar f(q)(\underline S)=\int_{SC} t(\underline S\mid x,u)\,q(d(x,u))$ (Eq. (7));
--   3. one-stage cost $\bar g(q)=\int_{SC} g(x,u)\,q(d(x,u))$ (Eq. (8)), the extended integral with $\infty-\infty=\infty$.
--
--   A policy (Definition 9.5) is a sequence $\bar\pi=(\bar\mu_0,\bar\mu_1,\dots)$ of maps $\bar\mu_k:P(S)\to P(SC)$ with $\bar\mu_k(p)\in\bar U(p)$, with no measurability requirement. From $p_0$ it generates $q_k=\bar\mu_k(p_k)$ and $p_{k+1}=\bar f(q_k)$ (Eqs. (10)–(11)), and its cost is (Definition 9.6, Eq. (9))
--   $$\bar J_{\bar\pi}(p_0)=\sum_{k=0}^\infty \alpha^k\,\bar g(q_k),\qquad \bar J^*(p_0)=\inf_{\bar\pi\in\bar\Pi}\bar J_{\bar\pi}(p_0).$$
--   The operator of Definition 9.8 is
--   $$\bar T(\bar J)(p)=\inf_{q\in\bar U(p)}\big\{\bar g(q)+\alpha\,\bar J[\bar f(q)]\big\}.$$
--
--   (DM) is the deterministic model through which Bertsekas and Shreve transfer the abstract results of Chapters 4–5 to the Borel model (SM).
--
--   **Formalization Note** Probability measures are represented as `Measure S` / `Measure (S × C)`; $\bar U(p)$ requires `q` to be a probability measure, and DM policies are maps on all of `Measure S` whose constraint is imposed at probability measures (the states of (DM)). $q(\Gamma)$ is the outer-measure value. $\bar f(q)$ is `q.bind t`. As for the (SM) cost `Policy.cost`, $\bar J_{\bar\pi}$ is computed as $\sum_k\alpha^k\int g^+dq_k-\sum_k\alpha^k\int g^-dq_k$ with $\infty-\infty=\infty$, which equals the series (9) under each of (P), (N), (D).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 216–218, Definitions 9.4–9.8, Eqs. (6)–(11) of Chapter 9

import Mathlib
import Definitions.Def_BertsekasShreve_BorelInfinite_ExtArith
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_BertsekasShreve_BorelInfinite_Model

namespace BertsekasShreve.BorelInfinite

open MeasureTheory ProbabilityTheory

namespace Model

variable {S C W : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [TopologicalSpace C] [MeasurableSpace C] [MeasurableSpace W]

/-- **Definition 9.4**, Eq. (6) (p. 216). The control constraint of the deterministic model (DM):
for `p ∈ P(S)`, `Ū(p) = {q ∈ P(SC) | q(Γ) = 1 and the marginal of q on S is p}`. (`q(Γ)` is the
outer-measure value, which for the analytic, hence universally measurable, set `Γ` is the
completion measure.) -/
def Ubar (M : Model S C W) (p : Measure S) : Set (Measure (S × C)) :=
  {q | IsProbabilityMeasure q ∧ q M.Γ = 1 ∧ q.map Prod.fst = p}

/-- **Definition 9.4**, Eq. (7) (p. 216). The system function of (DM):
`f̄(q)(S̲) = ∫_{SC} t(S̲ | x, u) q(d(x, u))` for Borel `S̲ ⊆ S`, i.e. the composition of `q`
with the transition kernel `t`. -/
noncomputable def fbar (M : Model S C W) (q : Measure (S × C)) : Measure S :=
  q.bind M.t

/-- **Definition 9.4**, Eq. (8) (p. 216). The one-stage cost of (DM):
`ḡ(q) = ∫_{SC} g(x, u) q(d(x, u))`, the extended integral `∫ g⁺ dq − ∫ g⁻ dq` (`∞ − ∞ = ∞`). -/
noncomputable def gbar (M : Model S C W) (q : Measure (S × C)) : EReal :=
  DupacovaWets.Consistency.expect q (fun z => M.g z.1 z.2)

/-- **Definition 9.5** (p. 217). A policy for (DM) is a sequence of mappings
`π̄ = (μ̄₀, μ̄₁, …)`, `μ̄_k : P(S) → P(SC)`, with `μ̄_k(p) ∈ Ū(p)` for every `p ∈ P(S)`; no
measurability is required. (The maps are stored on all of `Measure S`; the constraint is imposed
on the probability measures, which are the states of (DM).) The set of policies is `Π̄`. -/
structure DPolicy (M : Model S C W) where
  /-- the map `μ̄_k` -/
  μ : ℕ → Measure S → Measure (S × C)
  admissible : ∀ k (p : Measure S), IsProbabilityMeasure p → μ k p ∈ M.Ubar p

namespace DPolicy

variable {M : Model S C W}

/-- Eqs. (10)–(11) (p. 217): the states `p_k` generated from `p₀` by `π̄`:
`p_{k+1} = f̄(q_k)` with `q_k = μ̄_k(p_k)`. -/
noncomputable def state (π : M.DPolicy) (p₀ : Measure S) : ℕ → Measure S
  | 0 => p₀
  | k + 1 => M.fbar (π.μ k (state π p₀ k))

/-- Eq. (10) (p. 217): the controls `q_k = μ̄_k(p_k)`. -/
noncomputable def ctrl (π : M.DPolicy) (p₀ : Measure S) (k : ℕ) : Measure (S × C) :=
  π.μ k (π.state p₀ k)

/-- **Definition 9.6**, Eq. (9) (p. 217): the cost `J̄_π̄(p₀) = Σ_{k=0}^∞ α^k ḡ(q_k)`.
As for (SM) (Definition 9.3, `Policy.cost`), it is computed as
`Σ_k α^k ∫ g⁺ dq_k − Σ_k α^k ∫ g⁻ dq_k` with `∞ − ∞ = ∞`; under each of (P), (N), (D) this is
the sum of the series `Σ α^k ḡ(q_k)` of Eq. (9). -/
noncomputable def cost (π : M.DPolicy) (p₀ : Measure S) : EReal :=
  bsub (∑' k : ℕ, ENNReal.ofReal (M.α ^ k) *
          ∫⁻ z, (M.g z.1 z.2).toENNReal ∂(π.ctrl p₀ k))
       (∑' k : ℕ, ENNReal.ofReal (M.α ^ k) *
          ∫⁻ z, (-(M.g z.1 z.2)).toENNReal ∂(π.ctrl p₀ k))

end DPolicy

/-- **Definition 9.6** (p. 217): the optimal cost of (DM), `J̄*(p₀) = inf_{π̄ ∈ Π̄} J̄_π̄(p₀)`. -/
noncomputable def Jbarstar (M : Model S C W) (p : Measure S) : EReal :=
  ⨅ π : M.DPolicy, π.cost p

/-- **Definition 9.8** (p. 218): the operator `T̄` of (DM),
`T̄(J̄)(p) = inf_{q ∈ Ū(p)} {ḡ(q) + α J̄[f̄(q)]}` (with `∞ − ∞ = ∞`). -/
noncomputable def Tbar (M : Model S C W) (J : Measure S → EReal) (p : Measure S) : EReal :=
  ⨅ q ∈ M.Ubar p, BertsekasShreve.FiniteHorizon.badd (M.gbar q) ((M.α : EReal) * J (M.fbar q))

end Model

end BertsekasShreve.BorelInfinite


