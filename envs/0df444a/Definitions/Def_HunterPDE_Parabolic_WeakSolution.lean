-- Prove2me | Definitions.Def_HunterPDE_Parabolic_WeakSolution
-- name    : HunterPDE_Parabolic_WeakSolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:17:32.432034+00:00
-- url     : https://prove2.me/theorems/5f017ba1-27da-48e5-9aaa-6f3d9c93b0c7
-- title:
--   Assumption 6.1, the form a(u,v;t) of (6.10), weak solutions (Definition 6.2) and Galerkin approximate solutions (Definition 6.4)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and $T > 0$. The operator $L u = -\sum_{i,j} \partial_i(a^{ij}\partial_j u) + \sum_j b^j \partial_j u + c u$ has coefficients $a^{ij}(x,t)$, $b^j(x,t)$, $c(x,t)$. **Assumption 6.1 (1)–(2)**: $a^{ij}, b^j, c \in L^\infty(\Omega \times (0,T))$, $a^{ij} = a^{ji}$, and for some $\theta > 0$
--   $$\sum_{i,j=1}^n a^{ij}(x,t)\,\xi_i\xi_j \ge \theta|\xi|^2 \quad \text{for } (x,t) \in \Omega\times(0,T),\ \xi \in \mathbb{R}^n. \tag{6.6}$$
--   The **bilinear form** (6.10) on $H^1_0(\Omega)$ is
--   $$a(u, v; t) = \sum_{i,j}\int_\Omega a^{ij}(x,t)\,\partial_i u\,\partial_j v\,dx + \sum_j \int_\Omega b^j(x,t)\,\partial_j u\,v\,dx + \int_\Omega c(x,t)\,u v\,dx.$$
--
--   Given $f : (0,T) \to H^{-1}(\Omega)$ and $g \in L^2(\Omega)$, a **weak solution** of $u_t + Lu = f$, $u = 0$ on $\partial\Omega$, $u(0) = g$ (Definition 6.2) is $u : [0,T] \to H^1_0(\Omega)$ such that (1) $u \in L^2(0,T;H^1_0(\Omega))$ and its distributional time derivative (6.14), taken in $H^{-1}(\Omega)$, satisfies $u_t \in L^2(0,T;H^{-1}(\Omega))$; (2) for every $v \in H^1_0(\Omega)$, $\langle u_t(t), v\rangle + a(u(t), v; t) = \langle f(t), v\rangle$ for a.e. $t$; (3) $u(0) = g$.
--
--   The **Galerkin basis** (6.15)–(6.16) is an orthonormal basis $\{w_k\}$ of $L^2(\Omega)$ of Dirichlet eigenfunctions, $w_k \in H^1_0(\Omega)$, $\int_\Omega Dw_k\cdot Dv\,dx = \lambda_k (w_k, v)_{L^2}$ for all $v \in H^1_0(\Omega)$; $E_N = \langle w_1, \dots, w_N\rangle$ and $P_N g = \sum_{k \le N} (g, w_k)_{L^2} w_k$ (6.17). An **approximate solution** (Definition 6.4) is $u_N : [0,T] \to E_N$ with $u_N, u_{Nt} \in L^2(0,T;E_N)$, $(u_{Nt}(t), v)_{L^2} + a(u_N(t), v; t) = \langle f(t), v\rangle$ for every $v \in E_N$ and a.e. $t \in (0,T)$, and $u_N(0) = P_N g$.
--
--   **Formalization Note.** `Coeffs.Assumption61 Ω T` holds the coefficient conditions; "$\Omega$ bounded open, $T > 0$" and $f \in L^2(0,T;H^{-1})$ are hypotheses of the theorems. $L^\infty$ membership, symmetry and (6.6) are almost everywhere on $\Omega\times(0,T)$ (the meaning for $L^\infty$ coefficients). `timeMeasure T` is Lebesgue measure on $(0,T)$. `IsWeakSolution Ω T P f g u ut` takes the derivative `ut` explicitly; the time derivative is compared with $u$ through `l2Embed` ($H^1_0 \hookrightarrow L^2 \hookrightarrow H^{-1}$). The initial condition (3) is read as on p. 180, through the continuous representative: there is a continuous $\tilde u : [0,T] \to L^2(\Omega)$ equal to $u(t)$ for a.e. $t \in (0,T)$ with $\tilde u(0) = g$. So $g \in L^2(\Omega)$, and a weak solution lies in $C([0,T];L^2(\Omega))$ by definition. `IsApproxSolution` is the same with $E_N$, derivative taken in $H^1_0$, and a continuous representative $\tilde u : [0,T] \to H^1_0(\Omega)$ with $\tilde u(0) = P_N g$. Basis indices are 0-based: `w k` is $w_{k+1}$, and $E_N$ is the span of `w 0, …, w (N-1)`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 178–183: Eq. (6.5), (6.6), (6.10), Assumption 6.1, Definition 6.2, (6.15)–(6.17), Definition 6.4

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv

namespace HunterPDE.Parabolic

open MeasureTheory

/-- The time-dependent coefficient functions of the second-order operator in divergence form
(Hunter (6.5), p. 178), `L u = −∑ᵢⱼ ∂ᵢ(aⁱʲ ∂ⱼu) + ∑ⱼ bʲ ∂ⱼu + c u`, with `aⁱʲ(x, t)`, `bʲ(x, t)`,
`c(x, t)`, `x ∈ ℝⁿ`, `t ∈ ℝ`; indices are 0-based (`Fin n`: Lean's `i` is the book's `i + 1`). -/
structure Coeffs (n : ℕ) where
  /-- The principal coefficients `aⁱʲ(x, t)`. -/
  a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ → ℝ
  /-- The first-order coefficients `bʲ(x, t)`. -/
  b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → ℝ
  /-- The zeroth-order coefficient `c(x, t)`. -/
  c : EuclideanSpace ℝ (Fin n) → ℝ → ℝ

/-- Lebesgue measure on the time interval `(0, T)`; `L^p(0, T; X)` membership and norms are taken
with respect to it. -/
noncomputable abbrev timeMeasure (T : ℝ) : Measure ℝ :=
  volume.restrict (Set.Ioo 0 T)

/-- Lebesgue measure on the space-time cylinder `Ω × (0, T)`. -/
noncomputable abbrev cylMeasure {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n) × ℝ) :=
  (volume.restrict Ω).prod (timeMeasure T)

/-- The coefficient conditions (1)–(2) of Assumption 6.1 (Hunter, p. 179), on the cylinder
`Ω × (0, T)`:
(1) `aⁱʲ, bʲ, c ∈ L^∞(Ω × (0, T))`;
(2) `aⁱʲ = aʲⁱ` (as elements of `L^∞`, i.e. almost everywhere) and the uniform ellipticity
condition (6.6) holds for some constant `θ > 0`:
`∑ᵢⱼ aⁱʲ(x, t) ξᵢ ξⱼ ≥ θ |ξ|²` for (almost) all `(x, t) ∈ Ω × (0, T)` and all `ξ ∈ ℝⁿ`.
The conditions "`Ω` bounded and open, `T > 0`" and (3) on `f, g` are separate hypotheses of each
theorem. -/
def Coeffs.Assumption61 {n : ℕ} (P : Coeffs n) (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) :
    Prop :=
  (∀ i j, MemLp (fun p : EuclideanSpace ℝ (Fin n) × ℝ => P.a i j p.1 p.2) ⊤ (cylMeasure Ω T)) ∧
  (∀ j, MemLp (fun p : EuclideanSpace ℝ (Fin n) × ℝ => P.b j p.1 p.2) ⊤ (cylMeasure Ω T)) ∧
  MemLp (fun p : EuclideanSpace ℝ (Fin n) × ℝ => P.c p.1 p.2) ⊤ (cylMeasure Ω T) ∧
  (∀ i j, ∀ᵐ p ∂(cylMeasure Ω T), P.a i j p.1 p.2 = P.a j i p.1 p.2) ∧
  ∃ θ : ℝ, 0 < θ ∧ ∀ᵐ p ∂(cylMeasure Ω T), ∀ ξ : Fin n → ℝ,
    θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j p.1 p.2 * ξ i * ξ j

/-- The time-dependent bilinear form (6.10) of `L` on `H¹₀(Ω)` (Hunter, p. 179):
`a(u, v; t) = ∑ᵢⱼ ∫_Ω aⁱʲ(x, t) ∂ᵢu ∂ⱼv dx + ∑ⱼ ∫_Ω bʲ(x, t) ∂ⱼu v dx + ∫_Ω c(x, t) u v dx`,
with `∂ᵢu` the weak partial derivatives of `u ∈ H¹₀(Ω)`. -/
noncomputable def form {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (P : Coeffs n) (t : ℝ)
    (u v : H10 n Ω) : ℝ :=
  ∫ x in Ω, ((∑ i, ∑ j, P.a i j x t * pd u i x * pd v j x) + (∑ j, P.b j x t * pd u j x * val v x)
    + P.c x t * val u x * val v x)

/-- Weak solution of the initial–boundary value problem (6.8) `u_t + L u = f` in `Ω × (0, T)`,
`u = 0` on `∂Ω`, `u(·, 0) = g` (Hunter, Definition 6.2, p. 180), with `f : (0, T) → H⁻¹(Ω)`,
`g ∈ L²(Ω)`. The function `u : [0, T] → H¹₀(Ω)` together with its weak time derivative
`ut = u_t : (0, T) → H⁻¹(Ω)` is a weak solution if
(1) `u ∈ L²(0, T; H¹₀(Ω))` and `u_t ∈ L²(0, T; H⁻¹(Ω))`, where `u_t` is the distributional time
derivative (6.14) of `u` regarded in `H⁻¹(Ω)` through `H¹₀ ↪ L² ↪ H⁻¹`;
(2) for every `v ∈ H¹₀(Ω)`, `⟨u_t(t), v⟩ + a(u(t), v; t) = ⟨f(t), v⟩` (6.13) for a.e. `t`;
(3) `u(0) = g`, read as on p. 180 through the continuous representative of `u` in
`C([0, T]; L²(Ω))` (Theorem 6.41): there is `ũ : [0, T] → L²(Ω)` continuous, equal to `u(t)`
(in `L²(Ω)`) for a.e. `t ∈ (0, T)`, with `ũ(0) = g`. -/
def IsWeakSolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) (P : Coeffs n)
    (f : ℝ → Hm1 n Ω) (g : Lp ℝ 2 (volume.restrict Ω)) (u : ℝ → H10 n Ω) (ut : ℝ → Hm1 n Ω) :
    Prop :=
  MemLp u 2 (timeMeasure T) ∧ MemLp ut 2 (timeMeasure T) ∧
  HasWeakTimeDeriv (l2Embed n Ω) T u ut ∧
  (∀ v : H10 n Ω, ∀ᵐ t ∂(timeMeasure T), ut t v + form P t (u t) v = f t v) ∧
  ∃ ũ : ℝ → Lp ℝ 2 (volume.restrict Ω), ContinuousOn ũ (Set.Icc 0 T) ∧
    (∀ᵐ t ∂(timeMeasure T), ũ t = toL2 (u t)) ∧ ũ 0 = g

/-- `w : ℕ → H¹₀(Ω)` with eigenvalues `eig k = λ_{k+1}` is the Galerkin basis of (6.15)–(6.16)
(Hunter, pp. 181–182): an orthonormal basis `{w_k}` of `L²(Ω)` consisting of eigenfunctions of the
Dirichlet Laplacian, `−Δ w_k = λ_k w_k`, `w_k ∈ H¹₀(Ω)`, the eigenvalue equation read weakly:
`∫_Ω Dw_k · Dv dx = λ_k (w_k, v)_{L²}` for all `v ∈ H¹₀(Ω)`. Orthonormality is
`(w_j, w_k)_{L²} = δ_{jk}`; being a basis means the span of the `w_k` is dense in `L²(Ω)`.
The index is 0-based: Lean's `w k` is the book's `w_{k+1}`. -/
def IsDirichletEigenbasis {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (w : ℕ → H10 n Ω)
    (eig : ℕ → ℝ) : Prop :=
  (∀ k (v : H10 n Ω), ∫ x in Ω, inner ℝ (grad (w k) x) (grad v x) = eig k * l2inner (w k) v) ∧
  (∀ j k, l2inner (w j) (w k) = if j = k then 1 else 0) ∧
  (Submodule.span ℝ (Set.range fun k => toL2 (w k))).topologicalClosure = ⊤

/-- The Galerkin space `E_N = ⟨w₁, …, w_N⟩ ⊂ H¹₀(Ω)` of (6.15): the span of the first `N` basis
functions (0-based: `w 0, …, w (N − 1)`). -/
noncomputable def galerkinSpace {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (w : ℕ → H10 n Ω)
    (N : ℕ) : Submodule ℝ (H10 n Ω) :=
  Submodule.span ℝ (w '' Set.Iio N)

/-- The orthogonal projection `P_N : L²(Ω) → E_N` of (6.17):
`P_N (∑_k c^k w_k) = ∑_{k ≤ N} c^k w_k`, `c^k = (g, w_k)_{L²}`, i.e.
`P_N g = ∑_{k < N} (w_k, g)_{L²} w_k` (0-based), as an element of `E_N ⊂ H¹₀(Ω)`. -/
noncomputable def galerkinProj {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (w : ℕ → H10 n Ω)
    (N : ℕ) (g : Lp ℝ 2 (volume.restrict Ω)) : H10 n Ω :=
  ∑ k ∈ Finset.range N, inner ℝ (toL2 (w k)) g • w k

/-- Galerkin approximate solution of (6.8) (Hunter, Definition 6.4, p. 183). The function
`uN : [0, T] → E_N` with weak time derivative `uNt = u_{Nt}` is an approximate solution if
(1) `uN ∈ L²(0, T; E_N)` and `u_{Nt} ∈ L²(0, T; E_N)` (both take values in `E_N`, the
derivative is the distributional one (6.14), and `L²` is taken in the `H¹₀` norm, equivalent on
the finite-dimensional `E_N` to any other);
(2) for every `v ∈ E_N`, `(u_{Nt}(t), v)_{L²} + a(uN(t), v; t) = ⟨f(t), v⟩` (6.18) for a.e.
`t ∈ (0, T)`;
(3) `uN(0) = P_N g`, read through the continuous representative `uN ∈ C([0, T]; E_N)` (p. 183):
there is a continuous `ũ : [0, T] → H¹₀(Ω)` equal to `uN` a.e. on `(0, T)` with `ũ(0) = P_N g`. -/
def IsApproxSolution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ) (P : Coeffs n)
    (w : ℕ → H10 n Ω) (N : ℕ) (f : ℝ → Hm1 n Ω) (g : Lp ℝ 2 (volume.restrict Ω))
    (uN uNt : ℝ → H10 n Ω) : Prop :=
  (∀ t ∈ Set.Icc 0 T, uN t ∈ galerkinSpace w N) ∧ (∀ t ∈ Set.Icc 0 T, uNt t ∈ galerkinSpace w N) ∧
  MemLp uN 2 (timeMeasure T) ∧ MemLp uNt 2 (timeMeasure T) ∧
  HasWeakTimeDeriv (ContinuousLinearMap.id ℝ (H10 n Ω)) T uN uNt ∧
  (∀ v ∈ galerkinSpace w N, ∀ᵐ t ∂(timeMeasure T), l2inner (uNt t) v + form P t (uN t) v = f t v) ∧
  ∃ ũ : ℝ → H10 n Ω, ContinuousOn ũ (Set.Icc 0 T) ∧ (∀ᵐ t ∂(timeMeasure T), ũ t = uN t) ∧
    ũ 0 = galerkinProj w N g

end HunterPDE.Parabolic


