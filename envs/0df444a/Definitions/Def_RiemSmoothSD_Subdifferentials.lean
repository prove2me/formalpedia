-- Prove2me | Definitions.Def_RiemSmoothSD_Subdifferentials
-- name    : RiemSmoothSD_Subdifferentials
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:40.527745+00:00
-- url     : https://prove2.me/theorems/345e6717-3f0f-4149-bc7e-c4a9cb19ba73
-- title:
--   Riemannian subdifferentials $\hat\partial_{\mathcal R}f$, $\partial_{\mathcal R}f$, $G_{\tilde f,\mathcal R}$ and the stationarity notions (Definitions 3.1, 3.3, 3.4, 3.7, 3.9)
-- statement:
--   Let $\mathcal M\subseteq E$, $f:E\to\mathbb R$ and a smoothing function $\tilde f$ be given; $B_{x,\delta}=\{y:\|y-x\|\le\delta\}$ and $\operatorname{grad}h(x)=\mathrm{Proj}_{T_x\mathcal M}\nabla h(x)$.
--
--   1. **Riemannian Fréchet subdifferential** (3.1): for $x\in\mathcal M$,
--   $$
--   \hat\partial_{\mathcal R}f(x)=\{\operatorname{grad}h(x)\mid \exists\,\delta>0:\ h\in C^1(B_{x,\delta})\text{ and } f-h \text{ attains a local minimum at } x \text{ on } \mathcal M\}.
--   $$
--   2. **Riemannian limiting subdifferential** (3.2): $\partial_{\mathcal R}f(x)$ is the set of limits $\lim_\ell v_\ell$ with $v_\ell\in\hat\partial_{\mathcal R}f(x_\ell)$, $x_\ell\in\mathcal M$, $x_\ell\to x$ and $f(x_\ell)\to f(x)$.
--   3. **Limiting stationary point** (Definition 3.3): $x\in\mathcal M$ with $0\in\partial_{\mathcal R}f(x)$.
--   4. **Riemannian subdifferential associated with $\tilde f$** (3.9): for $x\in\mathcal M$,
--   $$
--   G_{\tilde f,\mathcal R}(x)=\{v: \operatorname{grad}\tilde f(z_k,\mu_k)\to v \text{ for some } z_k\in\mathcal M,\ z_k\to x,\ \mu_k\downarrow0\}.
--   $$
--   5. **Stationary point associated with $\tilde f$** (Definition 3.7): $x^*\in\mathcal M$ with
--   $$
--   \liminf_{x\to x^*,\ x\in\mathcal M,\ \mu\downarrow0}\|\operatorname{grad}\tilde f(x,\mu)\|=0 .
--   $$
--   6. **Riemannian gradient sub-consistency** (Definition 3.9): $\tilde f$ satisfies it at $x\in\mathcal M$ if $G_{\tilde f,\mathcal R}(x)\subseteq\partial_{\mathcal R}f(x)$ (3.16), and on $\mathcal M$ if (3.16) holds for every $x\in\mathcal M$.
--
--   These notions express first-order optimality of a nonsmooth, non-Lipschitz $f$ on a submanifold, and relate the gradients of the smoothing function to the limiting subdifferential of $f$.
--
--   **Formalization Note** "$h\in C^1(D)$" is read as $C^1$ on $D$, and $B_{x,\delta}$ is the closed ball. "$\mu_k\downarrow0$" is encoded as $\mu_k>0$, $\mu_k\to0$ (the same set, by passing to a subsequence). The liminf of item 5 is encoded as "0 is a cluster value of $(x,\mu)\mapsto\|\operatorname{grad}\tilde f(x,\mu)\|$ along $x\to x^*$ in $\mathcal M$, $\mu\downarrow0$", which for a nonnegative function is equivalent and avoids the junk value of a real liminf.
-- source:
--   Zhang, Chen & Ma, A Riemannian Smoothing Steepest Descent Method for Non-Lipschitz Optimization on Submanifolds, arXiv:2104.04199v1, Definition 3.1 (3.1)–(3.2), pp.5–6; Definition 3.3, Definition 3.4 (3.9), Definition 3.7 (3.10), p.7; Definition 3.9 (3.16), p.9

import Mathlib
import Definitions.Def_ZORiem_RGD_rgrad
set_option autoImplicit false
open Filter Topology

namespace RiemSmoothSD

open ZORiem.RGD

/-- **Riemannian Fréchet subdifferential** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Definition 3.1, (3.1), p.5): for `x ∈ M`,
`∂̂_R f(x) = {grad h(x) | ∃ δ > 0 such that h ∈ C¹(B_{x,δ}) and f − h attains a local minimum at x
on M}`.

**Formalization Note** `B_{x,δ}` is the closed ball (p.3), and "`h ∈ C¹(D)`" is read as
`ContDiffOn ℝ 1 h D`. `grad h(x) = rgrad M h x = Proj_{T_xM} ∇h(x)` (p.6); since `x` is an interior
point of the ball, `∇h(x)` is the Fréchet gradient. The local minimum is relative to `M`
(`IsLocalMinOn … M x`). The set is used only at points of `M`. -/
def frechetSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (f : E → ℝ) (x : E) : Set E :=
  {v | ∃ h : E → ℝ, ∃ δ : ℝ, 0 < δ ∧ ContDiffOn ℝ 1 h (Metric.closedBall x δ) ∧
    IsLocalMinOn (fun y => f y - h y) M x ∧ v = rgrad M h x}

/-- **Riemannian limiting subdifferential** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Definition 3.1, (3.2), p.6): `∂_R f(x) = {lim_{ℓ→∞} v_ℓ | v_ℓ ∈ ∂̂_R f(x_ℓ),
(x_ℓ, f(x_ℓ)) → (x, f(x))}`, with `x_ℓ ∈ M`.

**Formalization Note** Both `x_ℓ → x` and `f(x_ℓ) → f(x)` are required, and the `v_ℓ` converge
in `E`. -/
def limitingSubdiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (f : E → ℝ) (x : E) : Set E :=
  {v | ∃ y w : ℕ → E, (∀ ℓ, y ℓ ∈ M) ∧ (∀ ℓ, w ℓ ∈ frechetSubdiff M f (y ℓ)) ∧
    Tendsto y atTop (𝓝 x) ∧ Tendsto (fun ℓ => f (y ℓ)) atTop (𝓝 (f x)) ∧
    Tendsto w atTop (𝓝 v)}

/-- **Riemannian limiting stationary point** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Definition 3.3, p.7): `x ∈ M` is a limiting stationary point of (1.1) if `0 ∈ ∂_R f(x)`. -/
def IsLimitingStationary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (f : E → ℝ) (x : E) : Prop :=
  x ∈ M ∧ (0 : E) ∈ limitingSubdiff M f x

/-- **Riemannian subdifferential of `f` associated with `f̃`** (Zhang, Chen & Ma,
arXiv:2104.04199v1, Definition 3.4, (3.9), p.7): for `x ∈ M`,
`G_{f̃,R}(x) = {v ∈ ℝⁿ : grad f̃(z_k, μ_k) → v for some z_k ∈ M, z_k → x, μ_k ↓ 0}`.

**Formalization Note** `grad f̃(z, μ) = rgrad M (fun w => ftilde w μ) z`. "`μ_k ↓ 0`" is read as
`μ_k > 0` with `μ_k → 0`; requiring in addition that `μ_k` be decreasing gives the same set, by
passing to a subsequence along which `μ_k` strictly decreases. -/
def GfR {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Set E) (ftilde : E → ℝ → ℝ) (x : E) : Set E :=
  {v | ∃ z : ℕ → E, ∃ μs : ℕ → ℝ, (∀ k, z k ∈ M) ∧ Tendsto z atTop (𝓝 x) ∧
    (∀ k, 0 < μs k) ∧ Tendsto μs atTop (𝓝 0) ∧
    Tendsto (fun k => rgrad M (fun w => ftilde w (μs k)) (z k)) atTop (𝓝 v)}

/-- **Stationary point of `f` associated with `f̃` on `M`** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Definition 3.7, (3.10), p.7): `x* ∈ M` with
`liminf_{x → x*, x ∈ M, μ ↓ 0} ‖grad f̃(x, μ)‖ = 0`.

**Formalization Note** The liminf is taken along the filter `𝓝[M] x* ×ˢ 𝓝[>] 0` of pairs
`(x, μ)` with `x ∈ M`, `x → x*`, `μ > 0`, `μ → 0`. For a nonnegative function, "liminf = 0" is
exactly "`0` is a cluster value" (`MapClusterPt 0`), which is how it is encoded; this avoids the
junk value of `Filter.liminf` in `ℝ` for unbounded functions. -/
def IsStationaryAssoc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (ftilde : E → ℝ → ℝ) (x : E) : Prop :=
  x ∈ M ∧ MapClusterPt (0 : ℝ) (𝓝[M] x ×ˢ 𝓝[>] (0 : ℝ))
    (fun p : E × ℝ => ‖rgrad M (fun w => ftilde w p.2) p.1‖)

/-- **Riemannian gradient sub-consistency at `x`** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Definition 3.9, (3.16), p.9): for `x ∈ M`, `f̃` satisfies the Riemannian gradient sub-consistency
at `x` if `G_{f̃,R}(x) ⊆ ∂_R f(x)`. -/
def RiemGradSubConsistentAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (f : E → ℝ) (ftilde : E → ℝ → ℝ) (x : E) : Prop :=
  GfR M ftilde x ⊆ limitingSubdiff M f x

/-- **Riemannian gradient sub-consistency on `M`** (Zhang, Chen & Ma, arXiv:2104.04199v1,
Definition 3.9, p.9): (3.16) holds for every `x ∈ M`, i.e. `G_{f̃,R}(x) ⊆ ∂_R f(x)` for every
`x ∈ M`. -/
def RiemGradSubConsistent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (M : Set E) (f : E → ℝ) (ftilde : E → ℝ → ℝ) : Prop :=
  ∀ x ∈ M, RiemGradSubConsistentAt M f ftilde x

end RiemSmoothSD


