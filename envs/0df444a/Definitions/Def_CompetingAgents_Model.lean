-- Prove2me | Definitions.Def_CompetingAgents_Model
-- name    : CompetingAgents_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:22:52.502049+00:00
-- url     : https://prove2.me/theorems/b908fc55-f79e-49d4-aa25-6ba263c4847b
-- title:
--   The strategic-response model: covariate set, finitely many agent types, noise level and capacity level
-- statement:
--   The model of §2 has the following data.
--
--   1. A convex, compact **covariate set** $\mathcal X\subset\mathbb R^d$.
--   2. Finitely many **agent types** $i\in\iota$ (Assumption 2: the $(Z,c)$-marginal of $F$ has finite support). Type $i$ has probability $w_i>0$, with $\sum_i w_i=1$, raw covariates $Z_i\in\mathcal X$, a cost function $c_i:\mathbb R^d\to\mathbb R$ and a strong-convexity modulus $\alpha_i$.
--   3. A **noise level** $\sigma>0$: an agent's report is perturbed by $\epsilon\sim N(0,\sigma^2 I_d)$, independent of the type.
--   4. A **capacity level** $q\in(0,1)$: the decision maker treats the $1-q$ fraction of agents scoring above the $q$-th quantile of the score distribution.
--
--   **Assumption 1** (p.7) requires each $c_i$ to be twice continuously differentiable, $\alpha_i$-strongly convex with $\alpha_i>0$, and minimized at the origin. Finally $\alpha_*=\inf_i\alpha_i$ (p.9) is the smallest modulus.
--
--   All the mission's statements are about this model.
--
--   **Formalization Note** The covariate space is `EuclideanSpace ℝ (Fin d)`. The outcomes $Y_i(0),Y_i(1)$ and the class $\mathcal C\subset L^2(\tilde{\mathcal X},dx)$ of cost functions (p.6) are not modelled: no statement of the mission involves them. The capacity level is named `lev` because $q$ is also the paper's name for the quantile map. Strong convexity uses Mathlib's `StrongConvexOn univ α`, whose modulus is the lower bound on the Hessian ($c(y)=\alpha\|y\|^2/2$ is $\alpha$-strongly convex). The type set is nonempty because the weights sum to $1$, so $\alpha_*$ is a minimum.
-- source:
--   Sahoo, Wager, Policy Learning with Competing Agents, arXiv:2204.01884v5, §2.1–2.2, pp.5–6; Assumption 1, p.7; Assumption 2, p.8; $\alpha_*$, p.9

import Mathlib

open scoped BigOperators

namespace CompetingAgents

/-- The covariate space `ℝ^d`, as the Euclidean space `EuclideanSpace ℝ (Fin d)` (Sahoo, Wager,
*Policy Learning with Competing Agents*, arXiv:2204.01884v5, §2.1, p.5). -/
abbrev Cov (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The data of the strategic-response model of Sahoo, Wager, *Policy Learning with Competing
Agents*, arXiv:2204.01884v5, §2.1–§2.2 and Assumption 2 (pp.5–6, 8).

* `X` is the convex, compact covariate set `𝒳 ⊆ ℝ^d` (p.6).
* Agents come in finitely many types `i : ι` (Assumption 2, p.8: the `(Z, c)`-marginal of `F` has
  finite support); type `i` has probability `w i > 0`, `∑ w i = 1`, raw covariates `Z i ∈ 𝒳`, cost
  function `c i : ℝ^d → ℝ` and strong-convexity modulus `α i` (Assumption 1, p.7).
* `σ > 0` is the noise level: `εᵢ ∼ N(0, σ² I_d)` independently of the type (p.6).
* `lev ∈ (0,1)` is the capacity level, written `q` on p.5: the decision maker treats the `1 − q`
  proportion of agents scoring above the `q`-th quantile.

**Formalization Note.** The paper's `F` is a law of `(Zᵢ, cᵢ, εᵢ, Yᵢ(0), Yᵢ(1))`. The outcomes
`Yᵢ(0), Yᵢ(1)` and the class `𝒞 ⊂ L²(𝒳̃, dx)` of cost functions (p.6) do not enter any statement of
this mission and are not modelled. Under Assumption 2 the `(Z, c)`-marginal is a finite weighted
family of types, which is what `ι`, `w`, `Z`, `c` encode; distinct types may share `(Z, c)`. The
capacity level is called `lev` because `q` is also the paper's name for the quantile map. -/
structure Model (d : ℕ) (ι : Type*) [Fintype ι] where
  /-- the covariate set `𝒳` -/
  X : Set (Cov d)
  convex_X : Convex ℝ X
  isCompact_X : IsCompact X
  /-- the probability of type `i` -/
  w : ι → ℝ
  w_pos : ∀ i, 0 < w i
  sum_w : ∑ i, w i = 1
  /-- raw covariates of type `i` -/
  Z : ι → Cov d
  Z_mem : ∀ i, Z i ∈ X
  /-- cost function of type `i` -/
  c : ι → Cov d → ℝ
  /-- strong-convexity modulus of `c i` -/
  α : ι → ℝ
  /-- noise standard deviation -/
  σ : ℝ
  σ_pos : 0 < σ
  /-- the capacity level `q ∈ (0,1)` -/
  lev : ℝ
  lev_pos : 0 < lev
  lev_lt_one : lev < 1

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Assumption 1 (Sahoo, Wager, arXiv:2204.01884v5, p.7), for every type: the cost function
`cᵢ : ℝ^d → ℝ` is twice continuously differentiable, `αᵢ`-strongly convex for `αᵢ > 0`, and
minimized at the origin.

**Formalization Note.** `StrongConvexOn univ m f` means
`f (a x + b y) ≤ a f x + b f y − a b (m/2) ‖x − y‖²`; for `C²` functions this is `∇²f ≥ m I`, the
paper's `αᵢ`-strong convexity (`c(y) = α‖y‖²/2` is `α`-strongly convex). -/
def Assumption1 (M : Model d ι) : Prop :=
  ∀ i, ContDiff ℝ 2 (M.c i) ∧ 0 < M.α i ∧ StrongConvexOn Set.univ (M.α i) (M.c i) ∧
    ∀ y, M.c i 0 ≤ M.c i y

/-- `α_* = inf_i αᵢ` (Sahoo, Wager, arXiv:2204.01884v5, p.9: `α_*(F) = inf_{i ∈ ℕ} αᵢ`), the smallest
strong-convexity modulus over the types.

**Formalization Note.** `ι` is finite and nonempty (`∑ w i = 1`), so this real infimum is a
minimum and never a junk value. -/
noncomputable def alphaStar (M : Model d ι) : ℝ :=
  ⨅ i, M.α i

end CompetingAgents


