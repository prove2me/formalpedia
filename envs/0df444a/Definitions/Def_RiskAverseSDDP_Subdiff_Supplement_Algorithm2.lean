-- Prove2me | Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_Algorithm2
-- name    : RiskAverseSDDP_Subdiff_Supplement_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:30:26.618222+00:00
-- url     : https://prove2.me/theorems/50cff4fb-577e-4785-9adf-befdf389802b
-- title:
--   Algorithm 2 and (5.37)–(5.42), pp. 15–17 — runs of the sampling-based decomposition algorithm with feasibility cuts
-- statement:
--   This file formalizes Algorithm 2 (pp. 16–17), the sampling-based decomposition method for the linear program (5.35)–(5.36) when relatively complete recourse is not assumed. Nodes of the scenario tree, sampled nodes $n^k_t$ and the sets $\mathcal S_n$ are those of Algorithm 1: a node of stage $s+1$ is a sequence $(j_2,\dots,j_{s+1})$ of realization indices.
--
--   **Feasibility problem (5.37).** At stage $t$, for the current node $n=n^k_{t-1}$ with history $x^k_{[n]}$, a child $m$ with realization $\xi_m$, and the feasibility cuts $\langle\tilde\beta^\ell_{t+1},x_{1:t}\rangle\le\tilde\theta^\ell_{t+1}$ ($\ell=1,\dots,K_t$) known so far, let $\tilde{\mathfrak Q}_t(x^k_{[n]},\xi_m)$ be the optimal value of
--   $$\min_{x_t,y_1,y_2\ge0}\ e^\top(y_1+y_2)\quad\text{s.t.}\quad A_{t,m}x_t+y_1-y_2=b_m-\sum_{\tau=0}^{t-1}A_{\tau,m}x^k_\tau,\qquad \langle\tilde\beta^\ell_{t+1},[x^k_{[n]};x_t]\rangle\le\tilde\theta^\ell_{t+1}\ \ (\ell\le K_t).$$
--   A positive value means that the history $x^k_{[n]}$ has no feasible continuation at $m$. The **feasibility cut** (5.39)–(5.40) is $\langle\tilde\beta,x_{1:t-1}\rangle\le\tilde\theta$, where $\tilde\beta$ is a subgradient of $\tilde{\mathfrak Q}_t(\cdot,\xi_m)$ at $x^k_{[n]}$ and $\tilde\theta=-\tilde{\mathfrak Q}_t(x^k_{[n]},\xi_m)+\tilde\beta^\top x^k_{[n]}$.
--
--   **Problem (5.41).** For the approximation $\mathcal Q^{k-1}_{t+1}$ given by the optimality cuts, the problem minimizes $\Psi_m^\top[x^k_{[n]};x_t]+\mathcal Q^{k-1}_{t+1}([x^k_{[n]};x_t])$ over $x_t\in X_t(x^k_{0:t-1},\xi_m)$ subject to the feasibility cuts of stage $t+1$. Its optimal value, as a function of the state, is $\mathfrak Q^{k-1}_t(\cdot,\xi_m)$.
--
--   **Iteration $k$.** It is executed while $\mathrm{Out}=0$. Initially $\mathcal Q^0_t\equiv-\infty$ for $t=2,\dots,T$, $\mathcal Q^k_{T+1}\equiv0$, and there are no feasibility cuts.
--
--   1. *Forward pass.* It starts at $t=1$. At stage $t$, with $n=n^k_{t-1}$, problem (5.37) is solved for the children of $n$. If some child has a positive value, then: if $t=1$, $\mathrm{Out}=1$ and the problem is reported infeasible; otherwise the feasibility cut is added (so $K_{t-1}$ increases by one) and the pass returns to stage $t-1$. If no child has a positive value, $x^k_{n^k_t}$ is an optimal solution of (5.41) and the pass moves to stage $t+1$. The pass ends when $t=T+1$ or $\mathrm{Out}=1$. At every visit of a node, all of its children are examined again.
--   2. *Backward pass* (if $\mathrm{Out}=0$). For $t=2,\dots,T$ and $n=n^k_{t-1}$: at every non-sampled child $m$, $x^k_m$ is an optimal solution of (5.41). With $Z_m=\mathfrak Q^{k-1}_t(x^k_{[n]},\xi_m)$, a vector $p_k\in\mathcal P_t$ attains $\rho_t(Z)$, and each slope $\pi_{k,m}$ is a subgradient of $\mathfrak Q^{k-1}_t(\cdot,\xi_m)$ at $x^k_{[n]}$. Then (5.42) holds:
--   $$\theta^k_t=\sum_m p_{k,m}\Phi_mZ_m,\qquad \beta^k_t=\sum_m p_{k,m}\Phi_m\pi_{k,m},\qquad \mathcal Q^k_t(x_{1:t-1})=\max_{0\le\ell\le k}\big(\theta^\ell_t+\langle\beta^\ell_t,x_{1:t-1}-x^\ell_{[n^\ell_{t-1}]}\rangle\big).$$
--
--   A **run** for given choice rules and sampled indices records these quantities. Every choice (each optimal solution, each $p_k$, each slope, the order in which children are examined) is the value of a fixed deterministic rule applied to the data computed so far. The forward pass of each executed iteration is a finite sequence of steps. The run **reports infeasibility** if $\mathrm{Out}=1$ at the end of some iteration $k\ge1$. The set $\tilde{\mathcal S}_n=\mathcal S_{P(n)}$ of Remark 4.2 collects the iterations whose sampled scenario passes through the parent of $n$; these are the iterations at which $x^k_n$ is computed.
--
--   **Formalization Note** The slopes $\tilde\beta$ and $\pi_{k,m}$ are modelled as *any* subgradients (extended-real subdifferential `ESubdiff`) of the corresponding optimal-value functions at the trial point. The paper states that its multiplier formulas (p. 15 for $s$, p. 17 for $\pi_{k,m}$) give such subgradients; in the linear case this follows from LP duality. The run equations are written for iteration $k+1$ in terms of `Qm k` $=\mathcal Q^k$ and `FC k` (the feasibility cuts at the end of iteration $k$), so no truncated subtraction $k-1$ occurs. `FwdState` is a forward-pass state $(t,$ sampled-path decisions, cut lists$)$. `F s` holds the cuts on $x_{1:s+1}$, i.e. the cuts $\tilde\beta^\ell_{s+2}$ counted by $K_{s+1}$. The equation of (5.37) is written as $\sum_{\tau=0}^{t}A_{t,\tau,m}x_\tau+y_1-y_2=b_m$, which is the same constraint.
--
--   **Startup boundary convention.** The run explicitly initializes `Out` to zero, all initial slopes to zero, nonterminal initial intercepts to $-\infty$, and terminal intercepts and slopes to zero. When the continuation approximation is identically $-\infty$, an optimal decision means any feasible minimizer of the extended-real objective. It does not assert that a finite epigraph variable attains $-\infty$. This resolves the startup boundary of (5.41), consistently with the initialization on p. 16; at finite continuation values the ordinary epigraph interpretation applies.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, pp. 15–17, (5.37)–(5.42) and Algorithm 2; p. 14, Remark 4.2 (the sets S̃_n)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Definitions.Def_RiskAverseSDDP_Subdiff_Supplement_LinModel

namespace RiskAverseSDDP.Subdiff.Supplement

open RiskAverseSDDP.Convergence

/-- A list of feasibility cuts on the history `x_{1:s+1}`: a pair `(β̃, θ̃)` stands for the
inequality `⟨β̃, x_{1:s+1}⟩ ≤ θ̃` of (5.39). These are the cuts `β̃^ℓ_{s+2}`, `ℓ = 1, …, K_{s+1}`,
that enter the stage-`(s + 1)` problems (5.37) and (5.41). -/
abbrev CutList (n s : ℕ) : Type := List (Hist n (s + 1) × EReal)

/-- The history `z` satisfies every cut of the list `C`. -/
def SatCuts {n s : ℕ} (C : CutList n s) (z : Hist n (s + 1)) : Prop :=
  ∀ c ∈ C, ((inner ℝ c.1 z : ℝ) : EReal) ≤ c.2

namespace LinModel

variable {T n M q : ℕ} (L : LinModel T n M q)

/-- The optimal value `𝔔̃_{s+1}(x_{1:s}, ξ_{s+1,j})` of the feasibility problem (5.37), p. 15, at
stage `t = s + 1`, for the realization `j` of the child, the feasibility cuts `C` on `x_{1:s+1}`
and the state `x = x_{1:s}`:
`min eᵀ(y₁ + y₂)` over `x_{s+1}, y₁, y₂ ≥ 0` with
`Σ_{τ=0}^{s+1} A_{s+1,τ,j} x_τ + y₁ − y₂ = b_{s+1,j}` and `⟨β̃, [x_{1:s}; x_{s+1}]⟩ ≤ θ̃` for every
cut of `C`; an infimum in `ℝ ∪ {±∞}` (`+∞` if the cut constraints admit no `x_{s+1} ≥ 0`). -/
noncomputable def feasVal (s : ℕ) (j : Fin M) (C : CutList n s) (x : Hist n s) : EReal :=
  ⨅ (y : EuclideanSpace ℝ (Fin n)) (y₁ : EuclideanSpace ℝ (Fin q)) (y₂ : EuclideanSpace ℝ (Fin q))
    (_ : (∀ i, 0 ≤ y i) ∧ (∀ i, 0 ≤ y₁ i) ∧ (∀ i, 0 ≤ y₂ i) ∧
      (∑ τ : Fin (s + 2), L.A (s + 1) j τ
          (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) L.x0 (fun i => (x.snoc y) i) τ)) +
        y₁ - y₂ = L.b (s + 1) j ∧
      SatCuts C (x.snoc y)),
    ((∑ i, (y₁ i + y₂ i) : ℝ) : EReal)

/-- The feasible set of problem (5.41) at stage `s + 1`: the decisions
`x_{s+1} ∈ X_{s+1}(x_{0:s}, ξ_{s+1,j})` (`x_{s+1} ≥ 0`, `Σ_τ A_{s+1,τ,j} x_τ = b_{s+1,j}`) whose
history `[x_{1:s}; x_{s+1}]` satisfies the feasibility cuts `C`. -/
def feasC (s : ℕ) (j : Fin M) (C : CutList n s) (x : Hist n s) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | y ∈ L.toModel.feas s j x ∧ SatCuts C (x.snoc y)}

/-- The optimal value of problem (5.41), p. 16, at stage `s + 1` for the realization `j`, the
cost-to-go approximation `V` (`= 𝒬^{k-1}_{s+2}`, whose epigraph is described by the optimality
cuts `z ≥ θ^ℓ_{s+2} + ⟨β^ℓ_{s+2}, · − x^ℓ⟩`), the feasibility cuts `C` and the state `x = x_{1:s}`:
`inf {Ψ_{s+1,j}ᵀ[x; x_{s+1}] + V([x; x_{s+1}]) : x_{s+1} ∈ feasC}` in `ℝ ∪ {±∞}`. As a function
of `x` this is `𝔔^{k-1}_{s+1}(·, ξ_{s+1,j})` of Algorithm 2. -/
noncomputable def cutVal (s : ℕ) (j : Fin M) (V : Hist n (s + 1) → EReal) (C : CutList n s)
    (x : Hist n s) : EReal :=
  ⨅ y ∈ L.feasC s j C x, (L.toModel.f (s + 1) j (x.snoc y) + V (x.snoc y))

/-- `y` minimizes the extended-real objective of (5.41) over its feasible decisions.
When `V ≡ -∞` at startup, every feasible decision minimizes this objective. This implements
the paper's initialization by `𝒬⁰ ≡ -∞` without requiring an unattainable finite epigraph
variable `z`; at finite values it is the usual epigraph minimizer. -/
def IsCutOpt (s : ℕ) (j : Fin M) (V : Hist n (s + 1) → EReal) (C : CutList n s) (x : Hist n s)
    (y : EuclideanSpace ℝ (Fin n)) : Prop :=
  y ∈ L.feasC s j C x ∧
    ∀ z ∈ L.feasC s j C x,
      L.toModel.f (s + 1) j (x.snoc y) + V (x.snoc y) ≤ L.toModel.f (s + 1) j (x.snoc z) + V (x.snoc z)

end LinModel

/-- The state of the forward pass of Algorithm 2 between two of its steps:
* `t` the current stage (the node `n = n^k_{t-1}` is the sampled node whose children are checked);
* `xs` the decisions on the sampled scenario computed so far, `xs s = x^k_{n^k_{s+1}}`
  (only `s < t - 1` is meaningful);
* `F s` the feasibility cuts on `x_{1:s+1}` currently known (counted by `K_{s+1}`). -/
structure FwdState (n : ℕ) where
  t : ℕ
  xs : ℕ → EuclideanSpace ℝ (Fin n)
  F : (s : ℕ) → CutList n s

/-- The history `(xs 0, …, xs (s - 1)) ∈ ℝ^{ns}` of the first `s` decisions on the sampled path. -/
def pref {n : ℕ} (xs : ℕ → EuclideanSpace ℝ (Fin n)) (s : ℕ) : Hist n s :=
  WithLp.toLp 2 (fun i : Fin s => xs i.val)

/-- The choices Algorithm 2 (pp. 16–17) makes, as deterministic functions of the data computed so
far:
* `xRule s j x V C` the optimal solution `x_{s+1}` of (5.41) chosen at stage `s + 1` for the
  realization `j`, the state `x = x_{1:s}`, the approximation `V = 𝒬^{k-1}_{s+2}` and the
  feasibility cuts `C`;
* `pRule t Z` the vector `p_k ∈ 𝒫_t` chosen to attain `ρ_t(Z)`;
* `πRule s j x V C` the slope `π_{k,m}` for the child with realization `j` of the sampled node of
  stage `s + 1`, whose history is `x = x_{1:s+1}`;
* `cRule s x C` the child (realization index) of the current node at stage `s + 1` with state
  `x = x_{1:s}` for which a positive value of (5.37) is reported (the order in which the
  nonvisited children are examined);
* `fcRule s j x C` the slope `β̃ = s` of the feasibility cut (5.40) built from (5.37) at the child
  `j` of stage `s + 1` and the state `x = x_{1:s}`. -/
structure Rules (n M : ℕ) where
  xRule : (s : ℕ) → Fin M → Hist n s → (Hist n (s + 1) → EReal) → CutList n s →
    EuclideanSpace ℝ (Fin n)
  pRule : ℕ → (Fin M → EReal) → (Fin M → ℝ)
  πRule : (s : ℕ) → Fin M → Hist n (s + 1) → (Hist n (s + 2) → EReal) → CutList n (s + 1) →
    Hist n (s + 1)
  cRule : (s : ℕ) → Hist n s → CutList n s → Fin M
  fcRule : (s : ℕ) → Fin M → Hist n s → CutList n s → Hist n s

/-- The quantities generated by Algorithm 2, with the paper's iteration index `k ≥ 1`. Nodes are
as in Algorithm 1: a node of stage `s + 1` is `ν ∈ (Fin M)^s`.
* `x k s ν` the decision `x^k_ν` (computed only for the sampled nodes and their children);
* `θ k s`, `β k s` the optimality-cut coefficients `θ^k_{s+2}`, `β^k_{s+2}`;
* `π k s j` the slope `π_{k,m}` for the child `m` (realization `j`) of the sampled node `n^k_{s+1}`;
* `Qm k h` the approximation `𝒬^k_{h+1}`;
* `FC k s` the feasibility cuts on `x_{1:s+1}` at the end of iteration `k` (`FC 0` the initial,
  empty lists);
* `len k`, `fwd k i` the forward pass of iteration `k` as the finite sequence of its states
  `fwd k 0, …, fwd k (len k)`;
* `out k` the flag `Out` at the end of iteration `k` (`true`: the problem is reported infeasible). -/
structure RunData (n M : ℕ) where
  x : ℕ → (s : ℕ) → (Fin s → Fin M) → EuclideanSpace ℝ (Fin n)
  θ : ℕ → ℕ → EReal
  β : ℕ → (s : ℕ) → Hist n (s + 1)
  π : ℕ → (s : ℕ) → Fin M → Hist n (s + 1)
  Qm : ℕ → (h : ℕ) → Hist n h → EReal
  FC : ℕ → (s : ℕ) → CutList n s
  len : ℕ → ℕ
  fwd : ℕ → ℕ → FwdState n
  out : ℕ → Bool

namespace RunData

variable {n M : ℕ} (r : RunData n M)

/-- The decision history `x^k_{[ν]} = (x^k_{n_1}, …, x^k_ν) ∈ ℝ^{n(s+1)}` of the node `ν` of
stage `s + 1`. -/
def hist (k : ℕ) : (s : ℕ) → (Fin s → Fin M) → Hist n (s + 1)
  | 0, ν => (Hist.empty n).snoc (r.x k 0 ν)
  | s + 1, ν => (hist k s (Fin.init ν)).snoc (r.x k (s + 1) ν)

/-- Algorithm 2 terminates reporting that the problem is infeasible: `Out = 1` at the end of some
iteration `k ≥ 1`. -/
def ReportsInfeasible : Prop :=
  ∃ k, 1 ≤ k ∧ r.out k = true

end RunData

/-- `𝒮̃_ν = 𝒮_{P(ν)}` (Remark 4.2, p. 14): the iterations `k ≥ 1` whose sampled scenario passes
through the parent of the node `ν` of stage `s + 1`, i.e. those at which `x^k_ν` is computed. The
parent of the first-stage node is the root, through which every scenario passes. -/
def tildeIterSet {M : ℕ} (ys : ℕ → ℕ → Fin M) : (s : ℕ) → (Fin s → Fin M) → Set ℕ
  | 0, _ => {k | 1 ≤ k}
  | s + 1, ν => iterSet ys s (Fin.init ν)

namespace LinModel

variable {T n M q : ℕ}

/-- One step of the forward pass of iteration `k` of Algorithm 2 (p. 16), from the state `st` to
the state `st'`, with the approximations `V h = 𝒬^{k-1}_{h+1}` and the sampled realization indices
`ys`. At stage `t = s + 1 ≤ T`, with `n = n^k_s` and state `x = x^k_{[n]}`, the problems (5.37) of
all children of `n` are examined (all children again at every visit of `n`):
* if none has a positive optimal value, the decision at the sampled child `m = n^k_{s+1}` is the
  rule's optimal solution of (5.41) and the pass moves to stage `t + 1`;
* if one has (and `t ≥ 2`), the rule's child `m` has a positive value, the feasibility cut
  (5.39)–(5.40) `⟨β̃, x_{1:t-1}⟩ ≤ θ̃` with `β̃` a subgradient of `𝔔̃_t(·, ξ_m)` at `x^k_{[n]}` and
  `θ̃ = −𝔔̃_t(x^k_{[n]}, ξ_m) + ⟨β̃, x^k_{[n]}⟩` is added (`K_{t-1}` increases by one), and the pass
  moves back to stage `t − 1`.
(At `t = 1` a positive value ends the pass with `Out = 1`; see `InfeasEnd`.) -/
def FStep [NeZero M] (L : LinModel T n M q) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (k : ℕ)
    (V : (h : ℕ) → Hist n h → EReal) (st st' : FwdState n) : Prop :=
  (∃ s, st.t = s + 1 ∧ s < T ∧
    (∀ j ∈ Model.Rlz (M := M) (s + 1), L.feasVal s j (st.F s) (pref st.xs s) ≤ 0) ∧
    L.IsCutOpt s (nodeRlz s (sampNode ys k s)) (V (s + 1)) (st.F s) (pref st.xs s)
      (R.xRule s (nodeRlz s (sampNode ys k s)) (pref st.xs s) (V (s + 1)) (st.F s)) ∧
    st' = ⟨s + 2,
      Function.update st.xs s
        (R.xRule s (nodeRlz s (sampNode ys k s)) (pref st.xs s) (V (s + 1)) (st.F s)),
      st.F⟩) ∨
  (∃ s, st.t = s + 2 ∧ s + 1 < T ∧
    (∃ j ∈ Model.Rlz (M := M) (s + 2), 0 < L.feasVal (s + 1) j (st.F (s + 1)) (pref st.xs (s + 1))) ∧
    0 < L.feasVal (s + 1) (R.cRule (s + 1) (pref st.xs (s + 1)) (st.F (s + 1))) (st.F (s + 1))
      (pref st.xs (s + 1)) ∧
    R.fcRule (s + 1) (R.cRule (s + 1) (pref st.xs (s + 1)) (st.F (s + 1))) (pref st.xs (s + 1))
        (st.F (s + 1)) ∈
      ESubdiff (fun z => L.feasVal (s + 1) (R.cRule (s + 1) (pref st.xs (s + 1)) (st.F (s + 1)))
        (st.F (s + 1)) z) (pref st.xs (s + 1)) ∧
    st' = ⟨s + 1, st.xs,
      Function.update st.F s (st.F s ++
        [(R.fcRule (s + 1) (R.cRule (s + 1) (pref st.xs (s + 1)) (st.F (s + 1)))
            (pref st.xs (s + 1)) (st.F (s + 1)),
          -L.feasVal (s + 1) (R.cRule (s + 1) (pref st.xs (s + 1)) (st.F (s + 1))) (st.F (s + 1))
              (pref st.xs (s + 1)) +
            ((inner ℝ (R.fcRule (s + 1) (R.cRule (s + 1) (pref st.xs (s + 1)) (st.F (s + 1)))
              (pref st.xs (s + 1)) (st.F (s + 1))) (pref st.xs (s + 1)) : ℝ) : EReal))])⟩)

/-- The forward pass ends reporting infeasibility: at stage `t = 1` the problem (5.37) of the
first-stage node `n_1` (the only child of the root, realization `0`) has a positive optimal value,
so `Out = 1`. -/
def InfeasEnd (L : LinModel T n M q) [NeZero M] (st : FwdState n) : Prop :=
  st.t = 1 ∧ 0 < L.feasVal 0 0 (st.F 0) (Hist.empty n)

/-- `r` is a run of Algorithm 2 (pp. 16–17) for the linear program `L`, the choice rules `R` and
the sampled realization indices `ys k t = ξ^k_t` (`k ≥ 1`, `t = 2, …, T`). Iteration `k + 1` is
executed when `Out = 0` after iterations `1, …, k`, and uses `Qm k = 𝒬^k` and the feasibility
cuts `FC k` available at its start:
* initialization: `Out = 0`, `θ^0_t = −∞` and `𝒬^0_t ≡ −∞` for `t = 2, …, T`,
  `θ^k_{T+1} = 0`, `β^k_{T+1} = 0`, `𝒬^k_{T+1} ≡ 0` for every `k`, `K_t = 0`;
* forward pass: a finite sequence of `FStep`s from stage `1` with the cuts `FC k`, ending either
  with `Out = 1` (`InfeasEnd`) or at stage `T + 1` with `Out = 0`; in the latter case the final
  cuts are `FC (k + 1)` and the final decisions on the sampled path are `x^{k+1}_{n^{k+1}_{s+1}}`;
* backward pass (only if `Out = 0`), for `t = s + 2 = 2, …, T` and `n = n^{k+1}_{s+1}` with
  `x^{k+1}_{[n]}`: at every non-sampled child `m` of `n` the decision `x^{k+1}_m` is the rule's
  optimal solution of (5.41); with `Z_m = 𝔔^k_t(x^{k+1}_{[n]}, ξ_m)` the optimal values of (5.41)
  (with `𝒬^k_{t+1}` and the cuts `FC (k + 1)`), `p_{k+1} ∈ 𝒫_t` attains `ρ_t(Z)`; each
  `π_{k+1,m}` is a subgradient of `𝔔^k_t(·, ξ_m)` at `x^{k+1}_{[n]}`; (5.42)
  `θ^{k+1}_t = Σ_m p_{k+1,m} Φ_m Z_m`, `β^{k+1}_t = Σ_m p_{k+1,m} Φ_m π_{k+1,m}`; and
  `𝒬^{k+1}_t = max(𝒬^k_t, θ^{k+1}_t + ⟨β^{k+1}_t, · − x^{k+1}_{[n]}⟩)`. -/
def IsRun [NeZero M] (L : LinModel T n M q) (R : Rules n M) (ys : ℕ → ℕ → Fin M)
    (r : RunData n M) : Prop :=
  r.out 0 = false ∧
  (∀ s, s + 2 ≤ T → r.θ 0 s = ⊥) ∧
  (∀ s, s + 1 ≤ T → r.β 0 s = 0) ∧
  (∀ k s, s + 1 = T → r.θ k s = 0 ∧ r.β k s = 0) ∧
  (∀ h, 1 ≤ h → h < T → r.Qm 0 h = fun _ => ⊥) ∧
  (∀ k, r.Qm k T = fun _ => 0) ∧
  (∀ s, r.FC 0 s = []) ∧
  ∀ k, (∀ k', 1 ≤ k' → k' ≤ k → r.out k' = false) →
    (r.fwd (k + 1) 0).t = 1 ∧ (r.fwd (k + 1) 0).F = r.FC k ∧
    (∀ i, i < r.len (k + 1) →
      L.FStep R ys (k + 1) (r.Qm k) (r.fwd (k + 1) i) (r.fwd (k + 1) (i + 1))) ∧
    ((r.out (k + 1) = true ∧ L.InfeasEnd (r.fwd (k + 1) (r.len (k + 1)))) ∨
     (r.out (k + 1) = false ∧ (r.fwd (k + 1) (r.len (k + 1))).t = T + 1 ∧
      r.FC (k + 1) = (r.fwd (k + 1) (r.len (k + 1))).F ∧
      (∀ s, s < T → r.x (k + 1) s (sampNode ys (k + 1) s) = (r.fwd (k + 1) (r.len (k + 1))).xs s) ∧
      ∀ s, s + 2 ≤ T →
        let ν := sampNode ys (k + 1) s
        let xt := r.hist (k + 1) s ν
        let V := r.Qm k (s + 2)
        let C := r.FC (k + 1) (s + 1)
        let Z : Fin M → EReal := fun j => L.cutVal (s + 1) j V C xt
        let pk := R.pRule (s + 2) Z
        (∀ j : Fin M, j ≠ ys (k + 1) (s + 2) →
          r.x (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j) = R.xRule (s + 1) j xt V C ∧
          L.IsCutOpt (s + 1) j V C xt (r.x (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j))) ∧
        pk ∈ L.Prisk (s + 2) ∧ L.toModel.wsum (s + 2) pk Z = L.toModel.rho (s + 2) Z ∧
        (∀ j, r.π (k + 1) s j = R.πRule s j xt V C ∧
          r.π (k + 1) s j ∈ ESubdiff (fun z => L.cutVal (s + 1) j V C z) xt) ∧
        r.θ (k + 1) s = L.toModel.wsum (s + 2) pk Z ∧
        r.β (k + 1) s = ∑ j, (pk j * L.Φ (s + 2) j) • r.π (k + 1) s j ∧
        r.Qm (k + 1) (s + 1) = fun y =>
          max (r.Qm k (s + 1) y)
            (r.θ (k + 1) s + ((inner ℝ (r.β (k + 1) s) (y - xt) : ℝ) : EReal))))

end LinModel

end RiskAverseSDDP.Subdiff.Supplement


