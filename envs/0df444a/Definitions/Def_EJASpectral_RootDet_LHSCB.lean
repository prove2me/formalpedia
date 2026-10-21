-- Prove2me | Definitions.Def_EJASpectral_RootDet_LHSCB
-- name    : EJASpectral_RootDet_LHSCB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:21.792257+00:00
-- url     : https://prove2.me/theorems/8b470861-fdf3-4140-aae2-db35805fc280
-- title:
--   §4.4, p. 12 — proper cone and ν-logarithmically homogeneous self-concordant barrier (38)–(39)
-- statement:
--   Let $W$ be a real normed space and $\mathcal K\subseteq W$.
--
--   1. $\mathcal K$ is a **proper cone** if it is closed, convex, closed under multiplication by nonnegative scalars, pointed ($x\in\mathcal K$ and $-x\in\mathcal K$ imply $x=0$) and solid (its interior is nonempty).
--   2. A function $\Gamma : W\to\mathbb R$ is a **$\nu$-logarithmically homogeneous self-concordant barrier** ($\nu$-LHSCB) for $\mathcal K$ if
--      * $\Gamma$ is $C^3$-smooth and convex on $\operatorname{int}(\mathcal K)$;
--      * $\Gamma(\tilde u_i)\to\infty$ along every sequence $\tilde u_i\in\operatorname{int}(\mathcal K)$ converging to a boundary point of $\mathcal K$;
--      * logarithmic homogeneity holds: $$\Gamma(\theta\tilde u) = \Gamma(\tilde u) - \nu\log\theta\qquad \tilde u\in\operatorname{int}(\mathcal K),\ \theta>0; \tag{38}$$
--      * self-concordance holds: $$\big|\nabla^3\Gamma(\tilde u)[\tilde p,\tilde p,\tilde p]\big| \le 2\big(\nabla^2\Gamma(\tilde u)[\tilde p,\tilde p]\big)^{3/2}\qquad \tilde u\in\operatorname{int}(\mathcal K),\ \tilde p\in W; \tag{39}$$
--      * $\nu\ge 1$.
--
--   These are the barrier functions of interior-point methods for conic optimization; the parameter $\nu$ governs the iteration bound $O(\sqrt\nu\log(1/\varepsilon))$.
--
--   **Formalization Note** Directional derivatives are iterated Fréchet derivatives on the diagonal, $\nabla^k\Gamma(\tilde u)[\tilde p,\dots,\tilde p]$ = `iteratedFDeriv ℝ k Γ ũ (fun _ => p̃)`. The paper prints (38) for $\tilde u\in\mathcal K$, $\theta\in\mathbb R$; since $\Gamma$ is defined only on $\operatorname{int}(\mathcal K)$ and $\log\theta$ needs $\theta>0$, the clause is stated for $\tilde u\in\operatorname{int}(\mathcal K)$ and $\theta>0$, as in Nesterov–Nemirovskii Definition 2.3.2. Convexity is part of Nesterov–Nemirovskii Definition 2.1.1, which (39) cites; it is stated explicitly. The barrier condition is a limit within $\operatorname{int}(\mathcal K)$ at every point of the topological frontier. Properness of $\mathcal K$ is a separate predicate, because the paper also applies "LHSCB" to the domain $\mathbb R\times\mathcal Q$, which is not pointed. $\Gamma$ is a total function whose values off $\operatorname{int}(\mathcal K)$ are never used.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 12, §4.4, (38)–(39); proper cone pp. 2, 5

import Mathlib

namespace EJASpectral.RootDet

open Filter Topology

/-! # Proper cones and logarithmically homogeneous self-concordant barriers (§4.4, p. 12)

Coey, Kapelevich & Vielma, arXiv:2103.04104v2, p. 2, p. 5 (proper cone) and p. 12, (38)–(39). -/

/-- A proper cone (pp. 2, 5): closed, convex, closed under nonnegative scaling, pointed
(`x, −x ∈ K ⇒ x = 0`) and solid (nonempty interior). -/
def IsProperCone {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (K : Set W) : Prop :=
  IsClosed K ∧ Convex ℝ K ∧ (∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K) ∧
    (∀ x : W, x ∈ K → -x ∈ K → x = 0) ∧ (interior K).Nonempty

/-- `Γ` is a `ν`-LHSCB for `K` ((38)–(39), p. 12; Nesterov–Nemirovskii Definitions 2.1.1 and
2.3.2): `Γ` is `C³` and convex on `int K`, `Γ → ∞` along interior sequences converging to any
boundary point of `K`, `Γ(θx) = Γ(x) − ν log θ` for `x ∈ int K`, `θ > 0` (38),
`|∇³Γ(x)[h,h,h]| ≤ 2 (∇²Γ(x)[h,h])^{3/2}` for `x ∈ int K` (39), and `ν ≥ 1`.
Properness of `K` is not part of this predicate (see `IsProperCone`). -/
def IsLHSCB {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (K : Set W) (Γ : W → ℝ)
    (ν : ℝ) : Prop :=
  ContDiffOn ℝ 3 Γ (interior K) ∧
  ConvexOn ℝ (interior K) Γ ∧
  (∀ x ∈ frontier K, Tendsto Γ (𝓝[interior K] x) atTop) ∧
  (∀ x ∈ interior K, ∀ θ : ℝ, 0 < θ → Γ (θ • x) = Γ x - ν * Real.log θ) ∧
  (∀ x ∈ interior K, ∀ h : W,
      |iteratedFDeriv ℝ 3 Γ x (fun _ => h)| ≤
        2 * (iteratedFDeriv ℝ 2 Γ x (fun _ => h)) ^ (3 / 2 : ℝ)) ∧
  1 ≤ ν

end EJASpectral.RootDet


