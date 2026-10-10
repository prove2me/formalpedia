-- Prove2me | Definitions.Def_RiskAverseSDDP_Convergence_Run
-- name    : RiskAverseSDDP_Convergence_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:47:43.023241+00:00
-- url     : https://prove2.me/theorems/671dd90d-163e-4be9-914b-17fefa99cfe3
-- title:
--   Algorithm 1, pp. 8–9 — runs of the risk-averse sampling-based decomposition algorithm under deterministic choice rules
-- statement:
--   This file formalizes Algorithm 1 (pp. 8–9).
--
--   **Scenario tree.** Under (H1) the realizations of $(\xi_2,\dots,\xi_T)$ form the product tree: a node of stage $t\ge1$ is the sequence $(j_2,\dots,j_t)$ of realization indices from the first-stage node $n_1$ (the empty sequence), its children append one index, and the transition probability to a child with last index $j$ is $\Phi_{t,j}$. At iteration $k$ the sampled indices $\xi^k_2,\dots,\xi^k_T$ determine the sampled nodes $n^k_1=n_1,n^k_2,\dots,n^k_T$, and $\mathcal S_n=\{k\ge1:\ n^k_{t-1}=n\}$ is the set of iterations whose sampled scenario passes through the node $n$ of stage $t-1$.
--
--   **Approximations.** For $t=2,\dots,T+1$ the algorithm keeps polyhedral functions
--   $$
--   \mathcal Q^k_t(x_{1:t-1})=\max_{0\le\ell\le k}\Big(\theta^\ell_t+\langle\beta^\ell_t,x_{1:t-1}-x^\ell_{[n^\ell_{t-1}]}\rangle\Big),
--   $$
--   with $\mathcal Q^0_t\equiv-\infty$ for $t\le T$ and $\mathcal Q^k_{T+1}\equiv0$; $\mathfrak Q^{k-1}_t(x_{1:t-1},\xi_{t,j})$ denotes the optimal value of (3.14), i.e. of the stage-$t$ problem with $\mathcal Q_{t+1}$ replaced by $\mathcal Q^{k-1}_{t+1}$.
--
--   **Iteration $k\ge1$.**
--   1. *Forward pass at every node.* For $t=1,\dots,T$, at every node $m$ of stage $t$ with parent $n$, $x^k_m$ is an optimal solution of (3.15): it minimizes $f_t(x^k_{[n]},x_t,\Psi_m)+\mathcal Q^{k-1}_{t+1}(x^k_{[n]},x_t)$ over $x_t\in X_t(x_0,x^k_{[n]},\xi_m)$. Here $x^k_{[m]}=(x^k_{[n]},x^k_m)$ is the decision history from $n_1$ to $m$, and the first-stage decision is $x^k_1=x^k_{n_1}$.
--   2. *Cuts at the sampled node.* For $t=2,\dots,T$ and $n=n^k_{t-1}$, with $Z_m=\mathfrak Q^{k-1}_t(x^k_{[n]},\xi_m)$ for the children $m$ of $n$: a vector $p^k\in\mathcal P_t$ attaining $\rho_t(Z)=\sup_{p\in\mathcal P_t}\sum_mp_m\Phi_mZ_m$ is chosen; for each child $m$ a subgradient $\pi_{k,m}$ of $\mathfrak Q^{k-1}_t(\cdot,\xi_m)$ at $x^k_{[n]}$ is chosen; and (3.16)
--   $$
--   \theta^k_t=\sum_mp_{k,m}\Phi_mZ_m,\qquad\beta^k_t=\sum_mp_{k,m}\Phi_m\pi_{k,m}.
--   $$
--
--   A **run** for given choice rules and sampled indices is a sequence of decisions, cut coefficients, slopes and approximations satisfying all of the above, where every choice (each minimizer, each $p^k$, each $\pi_{k,m}$) is the value of a fixed deterministic rule applied to the data computed so far. A run therefore depends on the samples only through the samples of the current and earlier iterations, as Algorithm 1 does.
--
--   **Formalization Note** The cut slope is modelled as *any* subgradient of $\mathfrak Q^{k-1}_t(\cdot,\xi_m)$ at $x^k_{[n]}$, which is the property the convergence proof uses ((3.19), via Lemma 2.1). The printed formula for $\pi_{k,m}$ on p. 9 adds a partial subgradient of $f_t(\cdot,x^k_m,\Psi_m)$ in $x_{1:t-1}$ and multipliers of (3.15); for nonsmooth $f_t$ this need not be a subgradient of $\mathfrak Q^{k-1}_t(\cdot,\xi_m)$ (e.g. $f(x,y)=|x-y|$ with zero cost-to-go), so it is not encoded. Indices: iteration $k$ keeps the paper's number ($k\ge1$; entries at $k=0$ other than the initial approximations are unused); `x k s ν` is the decision at the node $\nu\in(\mathrm{Fin}\,M)^s$ of stage $s+1$; `hist k s ν` is $x^k_{[\nu]}\in\mathbb R^{n(s+1)}$; `θ k s`, `β k s` are $\theta^k_{s+2}$, $\beta^k_{s+2}$; `π k s j` is $\pi_{k,m}$ for the child with index $j$ of the sampled node of stage $s+1$; `Qm k h` is $\mathcal Q^k_{h+1}$. The run equations are written for iteration $k+1$ in terms of `Qm k` $=\mathcal Q^k$, so that no truncated subtraction $k-1$ occurs. The weights $p_{k,m}\Phi_m$ are real; `EReal` multiplication has $0\cdot(\pm\infty)=0$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, pp. 7–9, scenario tree notation, (3.14)–(3.16), Algorithm 1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model

namespace RiskAverseSDDP.Convergence

/-- The choices Algorithm 1 (pp. 8–9) makes, as deterministic functions of the data computed so
far. Stage indices: `xRule s` acts at stage `s + 1`, `pRule t` at stage `t`, `πRule s` at stage
`s + 2`.
* `xRule s j x V` is the decision `x_{s+1}` chosen in problem (3.15) at a node with realization
  index `j`, parent decision history `x = x_{1:s}` and current cost-to-go approximation
  `V = 𝒬^{k-1}_{s+2}`;
* `pRule t Z` is the vector `p^k ∈ 𝒫_t` chosen to attain `ρ_t(Z)` for
  `Z = (𝔔^{k-1}_t(x^k_{[n]}, ξ_m))_m`;
* `πRule s j x V` is the cut slope `π_{k,m}` for the child `m` with realization index `j` of the
  sampled node, whose decision history is `x = x_{1:s+1}`, when the approximation of
  `𝒬_{s+3}` is `V = 𝒬^{k-1}_{s+3}`. -/
structure Rules (n M : ℕ) where
  xRule : (s : ℕ) → Fin M → Hist n s → (Hist n (s + 1) → EReal) → EuclideanSpace ℝ (Fin n)
  pRule : ℕ → (Fin M → EReal) → (Fin M → ℝ)
  πRule : (s : ℕ) → Fin M → Hist n (s + 1) → (Hist n (s + 2) → EReal) → Hist n (s + 1)

/-- The quantities generated by Algorithm 1, with the paper's iteration index `k ≥ 1` (entries
at `k = 0` other than the initial approximations are never read). A node of stage `s + 1` is
the history `ν = (j_2, …, j_{s+1}) ∈ (Fin M)^s` of realization indices from the first-stage node
`n_1` (the empty history) to it; its children are `ν` extended by one index.
* `x k s ν` the decision `x^k_ν ∈ ℝⁿ` at the node `ν` of stage `s + 1`;
* `θ k s`, `β k s` the cut coefficients `θ^k_{s+2} ∈ ℝ ∪ {±∞}`, `β^k_{s+2} ∈ ℝ^{n(s+1)}`;
* `π k s j` the slope `π_{k,m}` for the child `m` (realization index `j`) of the sampled node
  `n^k_{s+1}`;
* `Qm k h` the approximation `𝒬^k_{h+1}` of the recourse function `𝒬_{h+1}`
  (`h = 1, …, T`), a function of `x_{1:h}`. -/
structure RunData (n M : ℕ) where
  x : ℕ → (s : ℕ) → (Fin s → Fin M) → EuclideanSpace ℝ (Fin n)
  θ : ℕ → ℕ → EReal
  β : ℕ → (s : ℕ) → Hist n (s + 1)
  π : ℕ → (s : ℕ) → Fin M → Hist n (s + 1)
  Qm : ℕ → (h : ℕ) → Hist n h → EReal

namespace RunData

variable {n M : ℕ} (r : RunData n M)

/-- The decision history `x^k_{[ν]} = (x^k_{n_1}, …, x^k_ν) ∈ ℝ^{n(s+1)}` from the first-stage
node to the node `ν` of stage `s + 1` (p. 8). -/
def hist (k : ℕ) : (s : ℕ) → (Fin s → Fin M) → Hist n (s + 1)
  | 0, ν => (Hist.empty n).snoc (r.x k 0 ν)
  | s + 1, ν => (hist k s (Fin.init ν)).snoc (r.x k (s + 1) ν)

/-- The decision history `x^k_{[P(ν)]} ∈ ℝ^{ns}` of the parent of the node `ν` of stage `s + 1`
(the empty history at the first stage, where the parent is the root `n_0` holding `x_0`). -/
def phist (k : ℕ) : (s : ℕ) → (Fin s → Fin M) → Hist n s
  | 0, _ => Hist.empty n
  | s + 1, ν => r.hist k s (Fin.init ν)

end RunData

/-- The realization index of the node `ν` of stage `s + 1`: its last entry, and `0` for the
first-stage node (stage 1 is deterministic and uses the data of realization `0`). -/
def nodeRlz {M : ℕ} [NeZero M] : (s : ℕ) → (Fin s → Fin M) → Fin M
  | 0, _ => 0
  | s + 1, ν => ν (Fin.last s)

/-- The node `n^k_{s+1}` of stage `s + 1` on the scenario sampled at iteration `k`, for the
sampled realization indices `ys k t = ξ^k_t` (`t = 2, …, T`). -/
def sampNode {M : ℕ} (ys : ℕ → ℕ → Fin M) (k s : ℕ) : Fin s → Fin M :=
  fun i => ys k (i.val + 2)

/-- `𝒮_ν = {k ≥ 1 : n^k_{s+1} = ν}`, the iterations whose sampled scenario passes through the
node `ν` of stage `s + 1` (proof of Theorem 4.1, p. 12). -/
def iterSet {M : ℕ} (ys : ℕ → ℕ → Fin M) (s : ℕ) (ν : Fin s → Fin M) : Set ℕ :=
  {k | 1 ≤ k ∧ sampNode ys k s = ν}

namespace Model

variable {T n M q p : ℕ}

/-- `r` is a run of Algorithm 1 (pp. 8–9) for the problem `D`, the choice rules `R` and the
sampled realization indices `ys k t = ξ^k_t` (`k ≥ 1`, `t = 2, …, T`). Iteration `k + 1` uses
the approximations `Qm k = 𝒬^k` available at its start:
* initialization: `𝒬^0_t ≡ -∞` for `t = 2, …, T`, and `𝒬^k_{T+1} ≡ 0` for every `k`;
* forward pass, at every node `ν` of every stage `s + 1 ≤ T`: `x^{k+1}_ν` is the rule's choice,
  it is feasible, `x^{k+1}_ν ∈ X_{s+1}(x_0, x^{k+1}_{[P(ν)]}, ξ_ν)`, and it minimizes
  `f_{s+1}(x^{k+1}_{[P(ν)]}, ·, Ψ_ν) + 𝒬^k_{s+2}(x^{k+1}_{[P(ν)]}, ·)` over that set (3.15);
* cuts, at stage `t = s + 2 ≤ T` only, at the sampled node `n = n^{k+1}_{s+1}` with trial
  point `x^{k+1}_{[n]}`: with `Z_j = 𝔔^k_{s+2}(x^{k+1}_{[n]}, ξ_{s+2,j})` (the optimal value of
  (3.14) with `𝒬^k_{s+3}`), the rule's `p^{k+1} ∈ 𝒫_{s+2}` attains `ρ_{s+2}(Z)`; every
  `π_{k+1,m}` is the rule's choice and is a subgradient of `𝔔^k_{s+2}(·, ξ_m)` at
  `x^{k+1}_{[n]}`; `θ^{k+1}_{s+2} = Σ_m p_{k+1,m} Φ_m Z_m`, `β^{k+1}_{s+2} = Σ_m p_{k+1,m} Φ_m π_{k+1,m}`
  (3.16); and `𝒬^{k+1}_{s+2}(y) = max(𝒬^k_{s+2}(y), θ^{k+1}_{s+2} + ⟨β^{k+1}_{s+2}, y − x^{k+1}_{[n]}⟩)`,
  i.e. `𝒬^k_t(y) = max_{0 ≤ ℓ ≤ k}(θ^ℓ_t + ⟨β^ℓ_t, y − x^ℓ_{[n^ℓ_{t-1}]}⟩)` with `θ^0_t = -∞`. -/
def IsRun [NeZero M] (D : Model T n M q p) (R : Rules n M) (ys : ℕ → ℕ → Fin M)
    (r : RunData n M) : Prop :=
  (∀ h, 1 ≤ h → h < T → r.Qm 0 h = fun _ => ⊥) ∧
  (∀ k, r.Qm k T = fun _ => 0) ∧
  (∀ k s (ν : Fin s → Fin M), s < T →
    r.x (k + 1) s ν = R.xRule s (nodeRlz s ν) (r.phist (k + 1) s ν) (r.Qm k (s + 1)) ∧
    r.x (k + 1) s ν ∈ D.feas s (nodeRlz s ν) (r.phist (k + 1) s ν) ∧
    ∀ y ∈ D.feas s (nodeRlz s ν) (r.phist (k + 1) s ν),
      D.f (s + 1) (nodeRlz s ν) ((r.phist (k + 1) s ν).snoc (r.x (k + 1) s ν)) +
          r.Qm k (s + 1) ((r.phist (k + 1) s ν).snoc (r.x (k + 1) s ν)) ≤
        D.f (s + 1) (nodeRlz s ν) ((r.phist (k + 1) s ν).snoc y) +
          r.Qm k (s + 1) ((r.phist (k + 1) s ν).snoc y)) ∧
  (∀ k s, s + 2 ≤ T →
    let xt := r.hist (k + 1) s (sampNode ys (k + 1) s)
    let Z : Fin M → EReal := fun j => D.stageVal (s + 1) j (r.Qm k (s + 2)) xt
    let pk := R.pRule (s + 2) Z
    pk ∈ D.Prisk (s + 2) ∧ D.wsum (s + 2) pk Z = D.rho (s + 2) Z ∧
    (∀ j, r.π (k + 1) s j = R.πRule s j xt (r.Qm k (s + 2)) ∧
      r.π (k + 1) s j ∈ ESubdiff (D.stageVal (s + 1) j (r.Qm k (s + 2))) xt) ∧
    r.θ (k + 1) s = D.wsum (s + 2) pk Z ∧
    r.β (k + 1) s = ∑ j, (pk j * D.Φ (s + 2) j) • r.π (k + 1) s j ∧
    r.Qm (k + 1) (s + 1) = fun y =>
      max (r.Qm k (s + 1) y) (r.θ (k + 1) s + ((inner ℝ (r.β (k + 1) s) (y - xt) : ℝ) : EReal)))

end Model

end RiskAverseSDDP.Convergence


