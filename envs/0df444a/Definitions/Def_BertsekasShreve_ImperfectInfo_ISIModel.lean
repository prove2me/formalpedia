-- Prove2me | Definitions.Def_BertsekasShreve_ImperfectInfo_ISIModel
-- name    : BertsekasShreve_ImperfectInfo_ISIModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:55:14.64132+00:00
-- url     : https://prove2.me/theorems/f2f04af4-fb98-4619-91b7-228e068d5729
-- title:
--   Definitions 10.3–10.5 — the imperfect state information model (ISI), its policies, costs, and optimality notions
-- statement:
--   **The model (Definition 10.3).** The imperfect state information model (ISI) consists of
--
--   1. a nonempty Borel **state space** $S$, a nonempty Borel **control space** $C$ and a nonempty Borel **observation space** $Z$;
--   2. a **discount factor** $\alpha>0$ and a lower semianalytic **one-stage cost** $g:SC\to R^*$, defined on all of $SC$;
--   3. a Borel-measurable **state transition kernel** $t(dx'\mid x,u)$ on $S$ given $SC$;
--   4. a Borel-measurable **initial observation kernel** $s_0(dz\mid x)$ on $Z$ given $S$ and a Borel-measurable **observation kernel** $s(dz\mid u,x)$ on $Z$ given $CS$;
--   5. a positive integer **horizon** $N$;
--   6. **control constraints** $U_k$, $k=0,\dots,N-1$: with the $k$-th **information vectors** $I_k=Z_0C_0\cdots C_{k-1}Z_k$ (eq. (14)), $U_k$ maps $I_k$ to nonempty subsets of $C$ and
--   $$\Gamma_k=\{(i_k,u)\mid i_k\in I_k,\ u\in U_k(i_k)\}\tag{15}$$
--   is analytic.
--
--   The state moves by $x_{k+1}\sim t(\cdot\mid x_k,u_k)$, the observation $z_{k+1}\sim s(\cdot\mid u_k,x_{k+1})$ is appended to the information vector, $z_0\sim s_0(\cdot\mid x_0)$, and $x_0$ has a given initial distribution $p\in P(S)$.
--
--   **Policies (Definition 10.4).** A policy is $\pi=(\mu_0,\dots,\mu_{N-1})$, each $\mu_k(du_k\mid p;i_k)$ a universally measurable stochastic kernel on $C$ given $P(S)I_k$ with $\mu_k(U_k(i_k)\mid p;i_k)=1$ for all $(p;i_k)$; $\Pi$ is the set of policies. For $p\in P(S)$ and $\pi\in\Pi$, $P_k(\pi,p)$ is the probability measure on the history space $H_k=SZC\cdots SZC$ determined by (16).
--
--   **Costs (Definition 10.5).** The cost of $\pi$ at $p$ and the optimal cost are
--   $$J_{N,\pi}(p)=\int_{H_{N-1}}\Big[\sum_{k=0}^{N-1}\alpha^k g(x_k,u_k)\Big]\,dP_{N-1}(\pi,p),\qquad J^*_N(p)=\inf_{\pi\in\Pi}J_{N,\pi}(p).$$
--   Assumption $(F^+)$ requires $\int_{H_{N-1}}[\sum_{k}\alpha^k g^-(x_k,u_k)]\,dP_{N-1}(\pi,p)<\infty$ for all $\pi\in\Pi$, $p\in P(S)$; assumption $(F^-)$ is the same with $g^+$.
--
--   **Optimality (Definition 8.3, as adapted in Definition 10.5).** $\pi$ is optimal at $p$ if $J_{N,\pi}(p)=J^*_N(p)$; for $\varepsilon>0$ it is $\varepsilon$-optimal at $p$ if $J_{N,\pi}(p)\le J^*_N(p)+\varepsilon$ when $J^*_N(p)>-\infty$ and $J_{N,\pi}(p)\le-1/\varepsilon$ when $J^*_N(p)=-\infty$. It is optimal ($\varepsilon$-optimal) if this holds at every $p$.
--
--   This is the model whose reduction to a perfect state information model is the subject of Section 10.2.
--
--   **Formalization Note** Only finite horizons $N$ are covered. The families $U_k$ and the policy kernels are indexed by all $k\in\mathbb N$, but only $k<N$ is constrained or used. $H_k$ is stored as the tuple $((x_j,z_j))_{j\le k}$ together with $(u_j)_{j\le k}$, and the process is run with the combined kernel $(x,z),u\mapsto$ law of $(x',z')$, $x'\sim t(\cdot\mid x,u)$, $z'\sim s(\cdot\mid u,x')$. $P(S)$ carries Mathlib's weak topology and Giry $\sigma$-algebra (its Borel $\sigma$-algebra, Proposition 7.25). The measure of the analytic set $U_k(i_k)$ is its outer (= completion) measure. A policy is a predicate on the family of kernels, so that optimality statements include membership in $\Pi$. Costs use the book's convention $\infty-\infty=+\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 248–250, Definitions 10.3, 10.4, 10.5, Eqs. (14)–(17) of Chapter 10, Assumptions (F+), (F−); pp. 188–189, Definition 8.1; p. 191, Definition 8.3

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_Foundations

namespace BertsekasShreve.ImperfectInfo

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The `k`-th information vectors `I_k = Z₀C₀⋯C_{k−1}Z_k` (eq. (14) of Chapter 10):
an element is `((z₀, …, z_k), (u₀, …, u_{k−1}))`. -/
abbrev Info (Z C : Type) (k : ℕ) := (Fin (k + 1) → Z) × (Fin k → C)

variable {S C Z : Type}
  [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
  [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- The set `Γ_k = {(i_k, u) | i_k ∈ I_k, u ∈ U_k(i_k)}` (eq. (15) of Chapter 10). -/
def GammaSet (U : (k : ℕ) → Info Z C k → Set C) (k : ℕ) : Set (Info Z C k × C) :=
  {q | q.2 ∈ U k q.1}

/-- Definition 10.3 (p. 248): the imperfect state information model (ISI)
`(S, C, (U₀, …, U_{N−1}), Z, α, g, t, s₀, s, N)`, with a finite horizon `N`.
`S`, `C`, `Z` carry their Borel σ-algebras (the instances `BorelSpace`). The control
constraints are given for every `k : ℕ`; only `k < N` matters and only those are constrained. -/
structure ISIModel (S C Z : Type)
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] where
  /-- horizon `N`, a positive integer -/
  N : ℕ
  N_pos : 0 < N
  /-- discount factor `α`, a positive real number (Definition 8.1) -/
  α : ℝ
  α_pos : 0 < α
  /-- one-stage cost `g : SC → R*`, defined on all of `SC` -/
  g : S × C → EReal
  /-- state transition kernel `t(dx' | x, u)` on `S` given `SC` -/
  t : Kernel (S × C) S
  /-- initial observation kernel `s₀(dz | x)` on `Z` given `S` -/
  s0 : Kernel S Z
  /-- observation kernel `s(dz | u, x)` on `Z` given `CS` -/
  s : Kernel (C × S) Z
  /-- control constraints `U_k : I_k → 2^C` -/
  U : (k : ℕ) → Info Z C k → Set C
  borel_S : IsBorelSpace S
  borel_C : IsBorelSpace C
  borel_Z : IsBorelSpace Z
  nonempty_S : Nonempty S
  nonempty_C : Nonempty C
  nonempty_Z : Nonempty Z
  g_lsa : LowerSemianalyticOn g Set.univ
  t_markov : IsMarkovKernel t
  s0_markov : IsMarkovKernel s0
  s_markov : IsMarkovKernel s
  U_nonempty : ∀ k < N, ∀ i : Info Z C k, (U k i).Nonempty
  Gamma_analytic : ∀ k < N, MeasureTheory.AnalyticSet (GammaSet U k)

namespace ISIModel

variable (M : ISIModel S C Z)

/-- The ISI process: the stage-`k` "state" is the pair `(x_k, z_k)`; `x_{k+1} ∼ t(·|x_k, u_k)`
and then `z_{k+1} ∼ s(·|u_k, x_{k+1})`. -/
noncomputable def stepKernel : Kernel ((S × Z) × C) (S × Z) :=
  (M.t.comap (fun a : (S × Z) × C => (a.1.1, a.2)) (by fun_prop)) ⊗ₖ
    (M.s.comap (fun b : ((S × Z) × C) × S => (b.1.2, b.2)) (by fun_prop))

/-- The information vector `i_k = (z₀, u₀, …, u_{k−1}, z_k)` contained in the
observation part `(x₀, z₀, u₀, …, x_k, z_k)` of a history. -/
def infoOf {k : ℕ} (o : Obs (fun _ => S × Z) C k) : Info Z C k :=
  (fun m => (o.1 m).2, o.2)

/-- Definition 10.4 (p. 249): `π = (μ₀, μ₁, …)` is a policy for (ISI) if each
`μ_k(du | p; i_k)` is a universally measurable stochastic kernel on `C` given `P(S) I_k` and
`μ_k(U_k(i_k) | p; i_k) = 1` for all `(p; i_k)` and `k < N`. (The measure of the analytic,
hence universally measurable, set `U_k(i_k)` is its completion/outer measure.) -/
def IsPolicy (π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C) :
    Prop :=
  (∀ k, UnivMeasurable (π k)) ∧
    ∀ k < M.N, ∀ (p : ProbabilityMeasure S) (i : Info Z C k), (π k (p, i) : Measure C) (M.U k i) = 1

/-- The probability measures `P_k(π, p)` on `H_k = SZC⋯SZC` (eq. (16), p. 249), with
`H_k` written as `((x_j, z_j)_{j ≤ k}, (u_j)_{j ≤ k})`. -/
noncomputable def law (π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C)
    (p : ProbabilityMeasure S) (k : ℕ) : Measure (Hist (fun _ => S × Z) C k) :=
  histLaw (X := fun _ => S × Z) ((p : Measure S) ⊗ₘ M.s0) (fun _ => M.stepKernel)
    (fun n o => (π n (p, infoOf o) : Measure C)) k

/-- The `N`-stage cost `J_{N,π}(p) = ∫_{H_{N−1}} [∑_{k=0}^{N−1} α^k g(x_k, u_k)] dP_{N−1}(π, p)`
(eq. (17), p. 249), with the book's extended integral and `∞ − ∞ = ∞`. -/
noncomputable def cost (π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C)
    (p : ProbabilityMeasure S) : EReal :=
  extIntegral (M.law π p (M.N - 1)) fun h =>
    BertsekasShreve.BorelFinite.bsum (List.ofFn fun k : Fin (M.N - 1 + 1) =>
      ((M.α ^ (k : ℕ) : ℝ) : EReal) * M.g ((h.1 k).1, h.2 k))

/-- The optimal cost `J*_N(p) = inf_{π ∈ Π} J_{N,π}(p)` (p. 250). -/
noncomputable def optCost (p : ProbabilityMeasure S) : EReal :=
  ⨅ π : {π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C // M.IsPolicy π},
    M.cost π.1 p

/-- Assumption (F⁺) (p. 249): `∫_{H_{N−1}} [∑ α^k g⁻(x_k, u_k)] dP_{N−1}(π, p) < ∞`
for every `π ∈ Π` and `p ∈ P(S)`. -/
def Fplus : Prop :=
  ∀ π, M.IsPolicy π → ∀ p : ProbabilityMeasure S,
    ∫⁻ h, (∑ k : Fin (M.N - 1 + 1), ENNReal.ofReal (M.α ^ (k : ℕ)) * negPart (M.g ((h.1 k).1, h.2 k)))
      ∂(M.law π p (M.N - 1)) < ∞

/-- Assumption (F⁻) (p. 250): `∫_{H_{N−1}} [∑ α^k g⁺(x_k, u_k)] dP_{N−1}(π, p) < ∞`
for every `π ∈ Π` and `p ∈ P(S)`. -/
def Fminus : Prop :=
  ∀ π, M.IsPolicy π → ∀ p : ProbabilityMeasure S,
    ∫⁻ h, (∑ k : Fin (M.N - 1 + 1), ENNReal.ofReal (M.α ^ (k : ℕ)) * posPart (M.g ((h.1 k).1, h.2 k)))
      ∂(M.law π p (M.N - 1)) < ∞

/-- `π` is optimal at `p` (Definition 10.5 with Definition 8.3): `π ∈ Π` and
`J_{N,π}(p) = J*_N(p)`. -/
def IsOptimalAt (π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C)
    (p : ProbabilityMeasure S) : Prop :=
  M.IsPolicy π ∧ M.cost π p = M.optCost p

/-- `π` is optimal: optimal at every `p ∈ P(S)`. -/
def IsOptimal (π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C) : Prop :=
  ∀ p, M.IsOptimalAt π p

/-- `π` is `ε`-optimal at `p` (Definition 10.5 with Definition 8.3): `π ∈ Π` and
`J_{N,π}(p) ≤ J*_N(p) + ε` if `J*_N(p) > −∞`, `J_{N,π}(p) ≤ −1/ε` if `J*_N(p) = −∞`. -/
def IsEpsOptimalAt (π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C)
    (p : ProbabilityMeasure S) (ε : ℝ) : Prop :=
  M.IsPolicy π ∧
    (⊥ < M.optCost p → M.cost π p ≤ M.optCost p + (ε : EReal)) ∧
    (M.optCost p = ⊥ → M.cost π p ≤ ((-1 / ε : ℝ) : EReal))

/-- `π` is `ε`-optimal: `ε`-optimal at every `p ∈ P(S)`. -/
def IsEpsOptimal (π : (k : ℕ) → ProbabilityMeasure S × Info Z C k → ProbabilityMeasure C)
    (ε : ℝ) : Prop :=
  ∀ p, M.IsEpsOptimalAt π p ε

end ISIModel

end BertsekasShreve.ImperfectInfo


