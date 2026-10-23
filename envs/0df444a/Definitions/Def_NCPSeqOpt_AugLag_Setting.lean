-- Prove2me | Definitions.Def_NCPSeqOpt_AugLag_Setting
-- name    : NCPSeqOpt_AugLag_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:20.279895+00:00
-- url     : https://prove2.me/theorems/2bafa921-988d-4d64-9fa1-d6a126438eb4
-- title:
--   §1–§4, pp. 1–10 — projection Π_C, DG(x)*, AGP (Def. 3.2), CAKKT (Def. 3.3), L_ρ, Algorithm 1 run, (22), (23), generalized Łojasiewicz (28)
-- statement:
--   This file fixes the objects of the nonlinear conic programming problem
--   $$\min_{x\in\mathbb R^n} f(x)\quad\text{subject to}\quad G(x)\in\mathcal K, \qquad\text{(NCP)}$$
--   where $f:\mathbb R^n\to\mathbb R$ and $G:\mathbb R^n\to\mathbb E$ are continuously differentiable, $\mathbb E$ is a finite-dimensional real inner product space, and $\mathcal K\subseteq\mathbb E$ is a nonempty closed convex cone with polar $\mathcal K^\circ=\{w\in\mathbb E:\langle w,k\rangle\le 0\ \forall k\in\mathcal K\}$.
--
--   1. **Projection.** For $C\subseteq\mathbb E$ and $w\in\mathbb E$, $\Pi_C(w)$ is a point of $C$ nearest to $w$.
--   2. **Adjoint derivative.** $DG(x)^*:\mathbb E\to\mathbb R^n$ is the adjoint of the derivative $DG(x)$; $\nabla f(x)$ is the gradient of $f$.
--   3. **AGP (Definition 3.2).** A feasible point $\bar x$ ($G(\bar x)\in\mathcal K$) satisfies AGP if there are sequences $x^k\to\bar x$ and $\Lambda^k\in\mathcal K^\circ$ with
--   $$\nabla f(x^k)+DG(x^k)^*\Lambda^k\to 0 \quad(9),\qquad \langle\Lambda^k,\Pi_{\mathcal K}(G(x^k))\rangle\to 0\quad(11).$$
--   4. **CAKKT (Definition 3.3).** A feasible point $\bar x$ satisfies CAKKT if there are sequences $x^k\to\bar x$ and $\Lambda^k\in\mathcal K^\circ$ for which (9), (11) and
--   $$\langle\Lambda^k,\Pi_{\mathcal K^\circ}(G(x^k))\rangle\to 0\quad(18)$$
--   all hold for the same pair of sequences.
--   5. **Augmented Lagrangian.** For $\rho>0$,
--   $$L_\rho(x,\Lambda)=f(x)+\frac\rho2\Big[\big\|\Pi_{\mathcal K^\circ}\big(G(x)+\tfrac{\Lambda}{\rho}\big)\big\|^2-\big\|\tfrac{\Lambda}{\rho}\big\|^2\Big].$$
--   6. **Algorithm 1.** Given inputs $\varepsilon_k>0$ with $\varepsilon_k\to0$, a nonempty convex compact $\mathcal B\subset\mathcal K^\circ$, $\tau>1$, $\sigma\in(0,1)$, $\rho_0>0$, a run is a sequence $(x^k,\hat\Lambda^k,\rho_k)_{k\in\mathbb N}$ with $\hat\Lambda^k\in\mathcal B$ and
--      - Step 1, (21): $\|\nabla_x L_{\rho_k}(x^k,\hat\Lambda^k)\|\le\varepsilon_k$;
--      - Step 2, (22): $\Lambda^k=\rho_k\Pi_{\mathcal K^\circ}(G(x^k)+\hat\Lambda^k/\rho_k)$;
--      - Step 3, (23): $V^k=\hat\Lambda^k/\rho_k-\Pi_{\mathcal K^\circ}(G(x^k)+\hat\Lambda^k/\rho_k)$;
--      - Step 4: if $\|V^k\|\le\sigma\|V^{k-1}\|$ then $\rho_{k+1}=\rho_k$, otherwise $\rho_{k+1}\ge\tau\rho_k$ (any such choice), with the convention $\|V^{-1}\|=\infty$.
--   7. **Generalized Łojasiewicz inequality (28).** $\Psi$ satisfies it at $\bar x$ if there are $\delta>0$ and a function $\psi$, continuous on the open ball $B(\bar x,\delta)$, with $\psi(x)\to0$ as $x\to\bar x$ and
--   $$|\Psi(x)-\Psi(\bar x)|\le\psi(x)\,\|D\Psi(x)\|\quad\text{for every }x\in B(\bar x,\delta).$$
--   8. $\Psi(x)=\tfrac12\|\Pi_{\mathcal K^\circ}(G(x))\|^2$, the function of Theorem 4.2.
--
--   These are the objects about which Theorems 4.1 and 4.2 speak: the augmented Lagrangian method produces sequences whose feasible limit points are AGP points, and CAKKT points under (28).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The cone, polar cone and nearest-point predicate are the published `MoreauProx.Decomposition` definitions. `proj C w` is a nearest point chosen by `Classical.choice`, and `0` if none exists; for the nonempty closed convex sets $\mathcal K$, $\mathcal K^\circ$ in finite dimension a nearest point always exists and is unique, so the default is never used. Algorithm 1 is a predicate `IsALRun` on the produced sequences: every free choice of the page (the point $x^k$, $\hat\Lambda^{k+1}\in\mathcal B$, $\rho_{k+1}\ge\tau\rho_k$) stays free. Step 1 is stated through the gradient of $y\mapsto L_{\rho_k}(y,\hat\Lambda^k)$, not through the formula (20). The convention $\|V^{-1}\|=\infty$ is encoded as $\rho_1=\rho_0$; the initial point $x^{-1}$ plays no role and is omitted. $\|D\Psi(x)\|$ is the operator norm of the Fréchet derivative.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), (NCP) p. 1; §2.1 p. 3; (9) p. 5; Definition 3.2 (11) p. 6; Definition 3.3 (18) p. 7; L_ρ p. 8; Algorithm 1 (21)–(23) p. 9; (28) and Theorem 4.2's Ψ p. 10

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones

namespace NCPSeqOpt.AugLag

open MoreauProx.Decomposition
open scoped InnerProductSpace
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-- The orthogonal projection `Π_C(w)` (§2.1, p. 3): a nearest point of `C` to `w`, chosen
from `IsProj`. For a nonempty closed convex `C` in finite dimension it exists and is unique,
so the junk value `0` is never used for the cones `𝒦` and `𝒦°`. -/
noncomputable def proj (C : Set E) (w : E) : E := by
  classical exact if h : ∃ v, IsProj C w v then h.choose else 0

/-- The adjoint `DG(x)* : 𝔼 → ℝⁿ` of the derivative of `G` at `x` (§2.1, p. 3). -/
noncomputable def adjD (G : EuclideanSpace ℝ (Fin n) → E) (x : EuclideanSpace ℝ (Fin n)) :
    E →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.adjoint (fderiv ℝ G x)

/-- Definition 3.2 (AGP), p. 6: `x̄` is feasible and there are sequences `x^k → x̄` and
`Λ^k ∈ 𝒦°` with `∇f(x^k) + DG(x^k)*Λ^k → 0` (9) and `⟨Λ^k, Π_𝒦(G(x^k))⟩ → 0` (11). -/
def IsAGP (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  G xbar ∈ K ∧ ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (Λ : ℕ → E),
    (∀ k, Λ k ∈ polarCone K) ∧
    Tendsto x atTop (𝓝 xbar) ∧
    Tendsto (fun k => gradient f (x k) + adjD G (x k) (Λ k)) atTop (𝓝 0) ∧
    Tendsto (fun k => ⟪Λ k, proj K (G (x k))⟫_ℝ) atTop (𝓝 0)

/-- Definition 3.3 (CAKKT), p. 7: `x̄` is feasible and there are sequences `x^k → x̄` and
`Λ^k ∈ 𝒦°` satisfying (9), (11) and `⟨Λ^k, Π_𝒦°(G(x^k))⟩ → 0` (18), all on the same pair of
sequences. -/
def IsCAKKT (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  G xbar ∈ K ∧ ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (Λ : ℕ → E),
    (∀ k, Λ k ∈ polarCone K) ∧
    Tendsto x atTop (𝓝 xbar) ∧
    Tendsto (fun k => gradient f (x k) + adjD G (x k) (Λ k)) atTop (𝓝 0) ∧
    Tendsto (fun k => ⟪Λ k, proj K (G (x k))⟫_ℝ) atTop (𝓝 0) ∧
    Tendsto (fun k => ⟪Λ k, proj (polarCone K) (G (x k))⟫_ℝ) atTop (𝓝 0)

/-- The Augmented Lagrangian (§4, p. 8):
`L_ρ(x, Λ) = f(x) + (ρ/2) [‖Π_𝒦°(G(x) + Λ/ρ)‖² − ‖Λ/ρ‖²]`. -/
noncomputable def augLag (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → E)
    (K : Set E) (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) (Λ : E) : ℝ :=
  f x + ρ / 2 * (‖proj (polarCone K) (G x + ρ⁻¹ • Λ)‖ ^ 2 - ‖ρ⁻¹ • Λ‖ ^ 2)

/-- The multiplier `Λ^k := ρ_k Π_𝒦°(G(x^k) + Λ̂^k/ρ_k)` of Step 2, (22), p. 9. -/
noncomputable def mult (K : Set E) (G : EuclideanSpace ℝ (Fin n) → E) (ρ : ℕ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (Λhat : ℕ → E) (k : ℕ) : E :=
  ρ k • proj (polarCone K) (G (x k) + (ρ k)⁻¹ • Λhat k)

/-- The vector `V^k := Λ̂^k/ρ_k − Π_𝒦°(G(x^k) + Λ̂^k/ρ_k)` of Step 3, (23), p. 9. -/
noncomputable def Vk (K : Set E) (G : EuclideanSpace ℝ (Fin n) → E) (ρ : ℕ → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (Λhat : ℕ → E) (k : ℕ) : E :=
  (ρ k)⁻¹ • Λhat k - proj (polarCone K) (G (x k) + (ρ k)⁻¹ • Λhat k)

/-- `(x^k, Λ̂^k, ρ_k)_{k ∈ ℕ}` is a sequence generated by Algorithm 1 (p. 9) with inputs
`{ε_k}`, `ℬ`, `τ`, `σ`, `ρ₀`. Every free choice of the algorithm (the point `x^k` of Step 1,
`Λ̂^{k+1} ∈ ℬ` of Step 2, `ρ_{k+1} ≥ τ ρ_k` of Step 4) is left free. The convention
`‖V^{−1}‖ = ∞` makes the test of Step 4 pass at `k = 0`, so `ρ_1 = ρ_0`. The initial point
`x^{−1}` plays no role and is omitted. -/
structure IsALRun (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → E)
    (K : Set E) (ε : ℕ → ℝ) (B : Set E) (τ σ ρ₀ : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (Λhat : ℕ → E) (ρ : ℕ → ℝ) : Prop where
  eps_pos : ∀ k, 0 < ε k
  eps_tendsto : Tendsto ε atTop (𝓝 0)
  B_nonempty : B.Nonempty
  B_convex : Convex ℝ B
  B_compact : IsCompact B
  B_subset : B ⊆ polarCone K
  one_lt_tau : 1 < τ
  sigma_pos : 0 < σ
  sigma_lt_one : σ < 1
  rho0_pos : 0 < ρ₀
  rho_zero : ρ 0 = ρ₀
  Λhat_mem : ∀ k, Λhat k ∈ B
  step1 : ∀ k, ‖gradient (fun y => augLag f G K (ρ k) y (Λhat k)) (x k)‖ ≤ ε k
  step4_zero : ρ 1 = ρ 0
  step4_keep : ∀ k, 1 ≤ k →
    ‖Vk K G ρ x Λhat k‖ ≤ σ * ‖Vk K G ρ x Λhat (k - 1)‖ → ρ (k + 1) = ρ k
  step4_increase : ∀ k, 1 ≤ k →
    ¬ (‖Vk K G ρ x Λhat k‖ ≤ σ * ‖Vk K G ρ x Λhat (k - 1)‖) → τ * ρ k ≤ ρ (k + 1)

/-- The generalized Łojasiewicz inequality (28), p. 10, for `Ψ` at `x̄`: there are `δ > 0` and
a function `ψ`, continuous on the open ball `B(x̄, δ)`, with `ψ(x) → 0` as `x → x̄` and
`|Ψ(x) − Ψ(x̄)| ≤ ψ(x) ‖DΨ(x)‖` on `B(x̄, δ)`. -/
def GenLojasiewicz (Ψ : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ δ > 0, ∃ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
    ContinuousOn ψ (Metric.ball xbar δ) ∧
    Tendsto ψ (𝓝 xbar) (𝓝 0) ∧
    ∀ y ∈ Metric.ball xbar δ, |Ψ y - Ψ xbar| ≤ ψ y * ‖fderiv ℝ Ψ y‖

/-- Theorem 4.2's function `Ψ(x) = (1/2) ‖Π_𝒦°(G(x))‖²`, p. 10. -/
noncomputable def Psi (K : Set E) (G : EuclideanSpace ℝ (Fin n) → E)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (1 / 2) * ‖proj (polarCone K) (G y)‖ ^ 2

end NCPSeqOpt.AugLag


