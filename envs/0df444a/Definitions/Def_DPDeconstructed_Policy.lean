-- Prove2me | Definitions.Def_DPDeconstructed_Policy
-- name    : DPDeconstructed_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:17.280495+00:00
-- url     : https://prove2.me/theorems/51bcff7d-c844-4c46-81a2-789b0631b750
-- title:
--   Feasible policies, greedy policies, Assumptions 2.1–2.2, $v_\sigma$, $v^*$ and optimal policies
-- statement:
--   For a dynamic program $(\mathsf X,\mathsf A,\Gamma,\mathcal V,H)$:
--
--   1. A **feasible policy** is a map $\sigma:\mathsf X\to\mathsf A$ with $\sigma(x)\in\Gamma(x)$ for all $x$ that satisfies the regularity condition (4): for every $v\in\mathcal V$, the function $w(x)=H(x,\sigma(x),v)$ lies in $\mathcal V$ (so it is real-valued, and $T_\sigma$ maps $\mathcal V$ into itself). Their set is $\Sigma$. The **$\sigma$-value operator** is $T_\sigma v(x)=H(x,\sigma(x),v)$.
--   2. Given $v$, a feasible $\sigma$ is **$v$-greedy** if $H(x,\sigma(x),v)=\sup_{a\in\Gamma(x)}H(x,a,v)$ for all $x$ (5).
--   3. **Assumption 2.1** (for a set $\mathbb V$): $\mathbb V\subseteq\mathcal V$, $T$ maps $\mathbb V$ into itself, and a $v$-greedy policy exists for each $v\in\mathbb V$.
--   4. A **$\sigma$-value function** is $v\in\mathcal V$ with $v(x)=H(x,\sigma(x),v)$ for all $x$. **Assumption 2.2**: for each $\sigma\in\Sigma$ there is exactly one, denoted $v_\sigma$.
--   5. The **value function** is $v^*(x)=\sup_{\sigma\in\Sigma}v_\sigma(x)$ (24); $\sigma$ is **optimal** if $v_\sigma=v^*$; $\sigma$ is **$v^*$-greedy** if $v^*$ is a real element of $\mathcal V$ and $\sigma$ is $v^*$-greedy in the sense of (5).
--
--   These objects state optimality: Bellman's principle of optimality (25) is "$\sigma$ optimal $\iff$ $\sigma$ $v^*$-greedy".
--
--   **Formalization Note** $\Sigma$ is a subtype of $\mathsf X\to\mathsf A$. Since $\mathcal V\subseteq\mathbb R^{\mathsf X}$, a $\sigma$ with $H(x,\sigma(x),v)=-\infty$ for some $x$ and some $v\in\mathcal V$ is not feasible. "$T$ maps $\mathbb V$ into itself" means that for $v\in\mathbb V$ some $w\in\mathbb V$ equals $Tv$ as an extended-real function. $v_\sigma$ is the unique $\sigma$-value function when it exists, and the junk value $0$ otherwise (all theorems assume Assumption 2.2). $v^*$ is extended-real valued ($-\infty$ if $\Sigma=\varnothing$).
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §2.2, pp.5–6 (Σ, regularity (4), v-greedy (5), Assumption 2.1, σ-value function, Assumption 2.2), §2.5, p.11 (T_σ), §3.1, p.13 (v* (24), optimal policy, principle of optimality (25))

import Mathlib
import Definitions.Def_DPDeconstructed_DynProg

namespace DPDeconstructed

namespace DynProg

variable {X A : Type*} (D : DynProg X A)

/-- Feasible policies, Ma and Stachurski, *Dynamic Programming Deconstructed*,
arXiv:1811.01940v2, §2.2, p.5: `σ : X → A` is feasible if `σ(x) ∈ Γ(x)` for all `x ∈ X` and
the regularity condition (4) holds: `v ∈ 𝒱` and `w(x) = H(x, σ(x), v)` on `X` imply `w ∈ 𝒱`.

**Formalization Note** In (4), `w` is the function `x ↦ H(x, σ(x), v)`, valued in `ℝ ∪ {−∞}`,
and `w ∈ 𝒱 ⊆ ℝ^X`; so (4) says that this function is real-valued and lies in `𝒱`, i.e. that
`T_σ` maps `𝒱` into itself (p.11: "the operator `T_σ` from `𝒱` to itself"). It is stated as
`∃ w ∈ 𝒱` with the equation read in `EReal`: a `σ` with `H(x, σ(x), v) = −∞` for some `x` and
some `v ∈ 𝒱` is not feasible. -/
def IsFeasible (σ : X → A) : Prop :=
  (∀ x, σ x ∈ D.Γ x) ∧
    ∀ v ∈ D.𝒱, ∃ w ∈ D.𝒱, ∀ x, (w x : EReal) = D.H x (σ x) v

/-- The set `Σ` of feasible policies, arXiv:1811.01940v2, §2.2, p.5, as a subtype. -/
abbrev Policy : Type _ := {σ : X → A // D.IsFeasible σ}

/-- The `σ`-value operator, arXiv:1811.01940v2, §2.5, p.11 and display (20):
`T_σ v(x) = H(x, σ(x), v)` (valued in `EReal`). -/
noncomputable def Tσ (σ : D.Policy) (v : X → ℝ) (x : X) : EReal :=
  D.H x (σ.1 x) v

/-- `v`-greedy policies, arXiv:1811.01940v2, display (5), p.5: a feasible `σ` is `v`-greedy if
`H(x, σ(x), v) = sup_{a ∈ Γ(x)} H(x, a, v)` for all `x ∈ X`, i.e. `T_σ v = T v`.

**Formalization Note** The paper defines this for `v ∈ 𝒱`; the predicate is stated for any
`v : X → ℝ` and every use supplies `v ∈ 𝒱` separately. -/
def IsGreedy (v : X → ℝ) (σ : D.Policy) : Prop :=
  ∀ x, D.Tσ σ v x = D.T v x

/-- Assumption 2.1, arXiv:1811.01940v2, p.5, for a given subset `𝕍`: `𝕍 ⊆ 𝒱`, `T` maps
elements of `𝕍` into `𝕍`, and a `v`-greedy policy exists in `Σ` for each `v ∈ 𝕍`.

**Formalization Note** "`T v ∈ 𝕍`" is: some `w ∈ 𝕍` has `(w x : EReal) = T v x` for all `x`
(so `T v` is real-valued). The paper's "there exists a subset `𝕍`" is the existential over this
predicate; theorems that use a fixed `𝕍` take it with `Assumption21 𝕍` as hypotheses. -/
def Assumption21 (𝕍 : Set (X → ℝ)) : Prop :=
  𝕍 ⊆ D.𝒱 ∧ (∀ v ∈ 𝕍, ∃ w ∈ 𝕍, ∀ x, (w x : EReal) = D.T v x) ∧
    ∀ v ∈ 𝕍, ∃ σ : D.Policy, D.IsGreedy v σ

/-- `σ`-value functions, arXiv:1811.01940v2, §2.2, p.6: `v ∈ 𝒱` with
`v(x) = H(x, σ(x), v)` for all `x ∈ X`, i.e. a fixed point of `T_σ` in `𝒱`. -/
def IsSigmaValue (σ : D.Policy) (v : X → ℝ) : Prop :=
  v ∈ D.𝒱 ∧ ∀ x, (v x : EReal) = D.Tσ σ v x

/-- Assumption 2.2, arXiv:1811.01940v2, p.6: for each `σ ∈ Σ` there is exactly one
`σ`-value function in `𝒱`. -/
def Assumption22 : Prop :=
  ∀ σ : D.Policy, ∃! v, D.IsSigmaValue σ v

open Classical in
/-- The `σ`-value function `v_σ` of Assumption 2.2, arXiv:1811.01940v2, p.6: the unique
`σ`-value function in `𝒱`.

**Formalization Note** When there is no unique `σ`-value function (Assumption 2.2 fails for
`σ`) the value is the junk `0`; every statement of the mission assumes Assumption 2.2. -/
noncomputable def vσ (σ : D.Policy) : X → ℝ :=
  if h : ∃! v, D.IsSigmaValue σ v then h.exists.choose else 0

/-- The value function, arXiv:1811.01940v2, display (24), p.13:
`v*(x) = sup_{σ ∈ Σ} v_σ(x)`, an extended-real valued function (`⊥` if `Σ` is empty). -/
noncomputable def vstar (x : X) : EReal :=
  ⨆ σ : D.Policy, (D.vσ σ x : EReal)

/-- Optimal policies, arXiv:1811.01940v2, §3.1, p.13: a feasible `σ` is optimal if
`v_σ = v*` on `X`. -/
def IsOptimal (σ : D.Policy) : Prop :=
  ∀ x, (D.vσ σ x : EReal) = D.vstar x

/-- "`σ` is `v*`-greedy", as in Bellman's principle of optimality (25), arXiv:1811.01940v2,
p.13: `v*` is a real-valued element of `𝒱` and `σ` is `v*`-greedy.

**Formalization Note** `v`-greediness (5) is defined for `v ∈ 𝒱`, while `v*` is a priori
extended-real valued; "`σ` is `v*`-greedy" therefore includes that `v*` coincides with some
`w ∈ 𝒱`, and then means that `σ` is `w`-greedy. -/
def IsVStarGreedy (σ : D.Policy) : Prop :=
  ∃ w ∈ D.𝒱, (∀ x, (w x : EReal) = D.vstar x) ∧ D.IsGreedy w σ

end DynProg

end DPDeconstructed


