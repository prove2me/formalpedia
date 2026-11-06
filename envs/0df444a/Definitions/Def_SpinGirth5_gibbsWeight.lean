-- Prove2me | Definitions.Def_SpinGirth5_gibbsWeight
-- name    : SpinGirth5_gibbsWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:42.536915+00:00
-- url     : https://prove2.me/theorems/0dc7e50a-9f76-4dbf-ad35-c1e29079edde
-- title:
--   Gibbs distribution $\mu_{G,A,\lambda}$, pinned marginals, and local $(\alpha,\varepsilon)$-spectral contraction (Condition 4)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $(A,\lambda)$ a multi-spin system on $q$ colours.
--
--   1. The **Gibbs distribution** is
--   $$\mu_{G,A,\lambda}(\sigma)=\frac1Z\prod_{uv\in E}A_{\sigma_u,\sigma_v}\prod_{v\in V}\lambda_{\sigma_v},\qquad Z=\sum_{\sigma\in[q]^V}\prod_{uv\in E}A_{\sigma_u,\sigma_v}\prod_{v\in V}\lambda_{\sigma_v},$$
--   each edge counted once.
--   2. The Gibbs weight of the deleted graph $G-v=G[V\setminus\{v\}]$ keeps the edges not incident to $v$ and the fields at $u\ne v$.
--   3. For a configuration $x$ and $\Lambda\subseteq V$, the **pinned marginal** at $i$ is the law of $X_i$ conditioned on $X_\Lambda=x_\Lambda$.
--   4. **Condition 4 (local $(\alpha,\varepsilon)$-spectral contraction).** Let $\varepsilon\in(0,1]$, $\alpha\ge 1$, $\Delta$ the maximum degree and $B=\mathbf 1\mathbf 1^{\top}-A$. For every vertex $v$ and every feasible pinning $\tau\in[q]^{V\setminus N[v]}$, with $\mu^{\tau}_{G,v}$ the marginal at $v$ of $\mu_G$ conditioned on $\tau$ and $\mu^{\tau}_{G-v,i}$ the marginal at $i$ of the Gibbs measure of $G-v$ conditioned on $\tau$:
--      - $\|B\mu^{\tau}_{G,v}\|_\infty\le\alpha/\Delta$ and $\|B\mu^{\tau}_{G-v,i}\|_\infty\le\alpha/\Delta$ for all $i\in N(v)$;
--      - $\displaystyle\Big\|\operatorname{diag}\Big(\sum_{i\in N(v)}\mu^{\tau}_{G-v,i}\Big)^{1/2}B\operatorname{diag}(\mu^{\tau}_{G,v})^{1/2}\Big\|_2^2\le\frac{1-\varepsilon}{\Delta}$, with $\|\cdot\|_2$ the spectral norm.
--
--   Condition 4 is the local criterion on the interaction matrix under which Theorem 5 gives a spectral gap of order $1/n$.
--
--   **Formalization Note** The edge factor is defined on unordered edges `Sym2 V` through the symmetry of $A$. The weight of $G-v$ is a function on all of $[q]^V$ that ignores $\sigma_v$, so its marginals at $i\ne v$ are those of the Gibbs measure of $G-v$. A feasible pinning on $V\setminus N[v]$ is represented by a configuration $x$ of positive Gibbs weight that extends it. The $\ell^\infty$ norm of the nonnegative vector $B\mu$ is its largest entry, and the spectral-norm bound is the quadratic-form bound $\|My\|_2^2\le c\|y\|_2^2$ for all $y\in\mathbb R^q$. $\Delta$ is `G.maxDegree`.
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, §1.1 and Condition 4, p.4; §2.1, pp.9–10; §5, p.19

import Mathlib
import Definitions.Def_SpinGirth5_Interaction
import Definitions.Def_SpinGirth5_heatBath

namespace SpinGirth5

open Finset Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

/-- The factor `A_{σ_u, σ_w}` of an (unordered) edge `uw` under the configuration `σ`; it is
well defined because `A` is symmetric. -/
def edgeFactor (S : Interaction q) (σ : V → Fin q) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun u w => S.A (σ u) (σ w), fun u w => S.symm (σ u) (σ w)⟩

/-- The unnormalized **Gibbs weight** `∏_{uv∈E} A_{σ_u,σ_v} · ∏_{v∈V} λ_{σ_v}`, each edge counted
once.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, §1.1, p.4, and §5, p.19: "µG(σ) ∝ ∏_{uv∈E} A_{σu,σv} ∏_{v∈V} λ_{σv},
∀σ ∈ [q]^V". -/
noncomputable def gibbsWeight (G : SimpleGraph V) [DecidableRel G.Adj] (S : Interaction q)
    (σ : V → Fin q) : ℝ :=
  (∏ e ∈ G.edgeFinset, edgeFactor S σ e) * ∏ v, S.lam (σ v)

/-- The partition function `Z = ∑_σ (Gibbs weight of σ)`. -/
noncomputable def partitionFn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Interaction q) : ℝ :=
  ∑ σ, gibbsWeight G S σ

/-- The **Gibbs distribution** `μ_{G,A,λ}(σ) = (Gibbs weight of σ)/Z` (Chen, Liu,
arXiv:2608.25491, §1.1, p.4).

**Formalization Note** It is a probability distribution when `Z > 0`; every statement using it
assumes `0 < partitionFn G S`. -/
noncomputable def gibbsDist (G : SimpleGraph V) [DecidableRel G.Adj] (S : Interaction q)
    (σ : V → Fin q) : ℝ :=
  gibbsWeight G S σ / partitionFn G S

/-- The Gibbs weight of the deleted graph `G − v = G[V ∖ {v}]` with the same `A, λ`: the edges of
`G` not incident to `v` and the fields at the vertices other than `v` (Chen, Liu,
arXiv:2608.25491, Condition 4, p.4: "We write G − v = G[V ∖ {v}] and let µ^τ_{G−v,i} denote the
marginal at i of the Gibbs measure on G − v with the same A, λ, conditioned on τ").

**Formalization Note** It is a function of `σ : V → [q]` that ignores `σ v`; the induced law on
`V → [q]` is the Gibbs measure of `G − v` times the uniform law of the dummy coordinate `v`, so
its marginals at vertices `i ≠ v` are those of the Gibbs measure on `G − v`. -/
noncomputable def gibbsWeightDel (G : SimpleGraph V) [DecidableRel G.Adj] (S : Interaction q)
    (v : V) (σ : V → Fin q) : ℝ :=
  (∏ e ∈ G.edgeFinset.filter (fun e => v ∉ e), edgeFactor S σ e) *
    ∏ u ∈ univ.erase v, S.lam (σ u)

/-- The marginal at `i` of the (unnormalized) weight `w`, conditioned on the pinning `x_Λ`:
`a ↦ (∑_{y_Λ = x_Λ, y_i = a} w(y)) / (∑_{y_Λ = x_Λ} w(y))`, the paper's `ν^τ_i` with `τ = x_Λ`
(Chen, Liu, arXiv:2608.25491, §2.1, pp.9–10). -/
noncomputable def pinnedMarginal (w : (V → Fin q) → ℝ) (Λ : Finset V) (x : V → Fin q) (i : V) :
    Fin q → ℝ :=
  fun a =>
    (∑ y ∈ univ.filter (fun y : V → Fin q => (∀ u ∈ Λ, y u = x u) ∧ y i = a), w y) /
      ∑ y ∈ univ.filter (fun y : V → Fin q => ∀ u ∈ Λ, y u = x u), w y

/-- **Local `(α, ε)`-spectral contraction** (Condition 4): for every `v` and every feasible pinning
`τ` on `V ∖ N[v]`, with `B = 11ᵀ − A`,
* `‖B μ^τ_{G,v}‖_∞ ≤ α/Δ` and `‖B μ^τ_{G−v,i}‖_∞ ≤ α/Δ` for every `i ∈ N(v)`;
* `‖diag(∑_{i∈N(v)} μ^τ_{G−v,i})^{1/2} B diag(μ^τ_{G,v})^{1/2}‖₂² ≤ (1 − ε)/Δ`.

Chen, Liu, arXiv:2608.25491, Condition 4, p.4.

**Formalization Note** `Δ = G.maxDegree`. A feasible pinning `τ` on `V ∖ N[v]` is the
restriction of a configuration `x` of positive Gibbs weight, and all such `x` are quantified.
`‖·‖_∞` of the nonnegative vector `Bμ` is its largest entry. The squared spectral norm bound
`‖M‖₂² ≤ c` is written as `‖M y‖₂² ≤ c ‖y‖₂²` for all `y ∈ ℝ^q`. The ranges `ε ∈ (0, 1]`,
`α ≥ 1` of the condition are part of the definition. -/
def LocalSpectralContraction (G : SimpleGraph V) [DecidableRel G.Adj] (S : Interaction q)
    (α ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 ∧ 1 ≤ α ∧
  ∀ (v : V) (x : V → Fin q), 0 < gibbsWeight G S x →
    (∀ c, (S.B *ᵥ pinnedMarginal (gibbsWeight G S) (closedNbhd G v)ᶜ x v) c ≤
        α / G.maxDegree) ∧
    (∀ i ∈ G.neighborFinset v, ∀ c,
        (S.B *ᵥ pinnedMarginal (gibbsWeightDel G S v) (closedNbhd G v)ᶜ x i) c ≤
          α / G.maxDegree) ∧
    ∀ y : Fin q → ℝ,
      ∑ a, (∑ i ∈ G.neighborFinset v,
          pinnedMarginal (gibbsWeightDel G S v) (closedNbhd G v)ᶜ x i a) *
        (∑ c, S.B a c *
          Real.sqrt (pinnedMarginal (gibbsWeight G S) (closedNbhd G v)ᶜ x v c) * y c) ^ 2 ≤
      (1 - ε) / G.maxDegree * ∑ c, y c ^ 2

end SpinGirth5


