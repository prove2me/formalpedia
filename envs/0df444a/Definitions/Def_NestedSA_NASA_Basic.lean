-- Prove2me | Definitions.Def_NestedSA_NASA_Basic
-- name    : NestedSA_NASA_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:38:13.929+00:00
-- url     : https://prove2.me/theorems/2fb71e6a-ba60-4502-babb-634e0aad7ac7
-- title:
--   NASA: the subproblem solution $\bar y$, its value $\eta$, the optimality measure $V$, the merit function $W$ and the constants of §3
-- statement:
--   Consider problem (1.1), $\min_{x\in X} F(x)$ with $F(x)=f(g(x))$, where $f:\mathbb R^m\to\mathbb R$, $g:\mathbb R^n\to\mathbb R^m$ and $X\subseteq\mathbb R^n$ is closed and convex, and let $\Pi_X$ be the Euclidean projection onto $X$. This file collects the deterministic objects of Ghadimi, Ruszczyński and Wang's analysis.
--
--   1. **Subproblem solution** (p. 7). For $\beta>0$,
--   $$\bar y(x,z,\beta)=\operatorname*{argmin}_{y\in X}\Big\{\langle z,y-x\rangle+\tfrac\beta2\|y-x\|^2\Big\}=\Pi_X\Big(x-\tfrac1\beta z\Big).$$
--   2. **Optimal value** (3.14): $\eta(x,z)=\langle z,\bar y-x\rangle+\frac\beta2\|\bar y-x\|^2$ with $\bar y=\bar y(x,z,\beta)$, also viewed as a function of the pair $(x,z)$ in the Euclidean product, whose norm is $\sqrt{\|x\|^2+\|z\|^2}$.
--   3. **Gradient of the composite objective**: $\nabla F(x)$, the gradient of $x\mapsto f(g(x))$.
--   4. **Optimality measure** (2.10): $V(x,z)=\|\bar y(x,z,1)-x\|^2+\|z-\nabla F(x)\|^2$.
--   5. **Optimal value of (1.1)**: $F^*=\inf_{x\in X}F(x)$.
--   6. **Merit function** (3.15): $W(x,z,u)=a\,(F(x)-F^*)-\eta(x,z)+\frac\gamma2\|g(x)-u\|^2$.
--   7. **Constants**: $L_{\nabla F}=L_g^2L_{\nabla f}+L_fL_{\nabla g}$ (Lemma 2), $L_{\nabla\eta}=2\sqrt{(1+\beta)^2+(1+\frac1{2\beta})^2}$ (Lemma 3), $L_1=\frac{2L_{\nabla F}^2}{a^2}+4L_g^4L_{\nabla f}^2$ and $L_2=4L_g^2L_{\nabla f}^2$ (3.32), and the products (3.27)
--   $$\Gamma_1=\begin{cases}1,&\tau_0=1/a,\\ 1-a\tau_0,&\tau_0<1/a,\end{cases}\qquad \Gamma_k=\Gamma_1\prod_{i=1}^{k-1}(1-a\tau_i)\quad(k\ge2).$$
--   8. **Noise constant**: the paper's $\sigma^2$ of (3.26) in the form its proof establishes,
--   $$\hat\sigma^2=\tfrac12\Big(\big[aL_{\nabla F}+L_{\nabla\eta}+\gamma L_g^2+2aL_g^2L_{\nabla f}\big]\frac{\max(\sigma_J^2\sigma_s^2,\|z^0\|^2)}{\beta^2}+\gamma b^2\sigma_G^2+4L_{\nabla\eta}\big[\max\big(1,\tfrac{a^2}2\big)\|z^0\|^2+24a^2\sigma_J^2\sigma_s^2\big]\Big).$$
--
--   These are the quantities in which every statement of the mission is written: $V$ measures how far a primal–dual pair $(x,z)$ is from satisfying the first-order condition $-\nabla F(x)\in N_X(x)$, and $W$ is the Lyapunov function of the convergence proof.
--
--   **Formalization Note** The argmin of (2.5) is rendered through the projection identity printed on p. 7, with the projection supplied as a function $P$ tied to $X$ by the published predicate `SpectralProjGrad.Shared.IsProjOnto`; $\eta$ is the objective evaluated at that point, not an infimum. $F^*$ is `sInf` of $F(X)$; the theorems that use it assume $F$ bounded below on the nonempty set $X$. The paper does not define $\Gamma_0$; the formula gives $\Gamma_0=\Gamma_1$, which no statement uses. The paper prints $\sigma^2$ with $L_{\nabla F}$ in place of $aL_{\nabla F}$, $\sigma_J^2\sigma_s^2$ in place of $\max(\sigma_J^2\sigma_s^2,\|z^0\|^2)$, $b^2\sigma_g^2$ in place of $\gamma b^2\sigma_G^2$, and $\|z^0\|^2$ in place of $\max(1,a^2/2)\|z^0\|^2$ (the two agree for $a\le\sqrt2$); its proof establishes $\hat\sigma^2$ (see Proposition 1(b)).
-- source:
--   Ghadimi, Ruszczyński, Wang, A Single Time-Scale Stochastic Approximation Method for Nested Stochastic Optimization, arXiv:1812.01094v2, p. 2 (1.1), p. 5 Notation, p. 7 (2.10), p. 9 Lemma 2, p. 10 (3.14), (3.15), Lemma 3, p. 12 (3.26), (3.27), p. 14 (3.32)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto

open scoped RealInnerProductSpace

namespace NestedSA.NASA

/-- The solution of subproblem (2.5) at `(x, z)` with coefficient `β` (p. 7):
`ȳ(x, z, β) = argmin_{y ∈ X} {⟨z, y − x⟩ + β/2 ‖y − x‖²} = Π_X(x − β⁻¹ z)`. The argmin is rendered through the
projection identity printed on p. 7; every theorem ties `P` to `X` by `SpectralProjGrad.Shared.IsProjOnto X P`. -/
noncomputable def ybar {n : ℕ} (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x z : EuclideanSpace ℝ (Fin n)) (β : ℝ) : EuclideanSpace ℝ (Fin n) :=
  P (x - β⁻¹ • z)

/-- The optimal value (3.14) of subproblem (2.5): `η(x, z) = ⟨z, ȳ − x⟩ + β/2 ‖ȳ − x‖²` with `ȳ = ȳ(x, z, β)`
(the objective evaluated at its minimizer). -/
noncomputable def eta {n : ℕ} (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⟪z, ybar P x z β - x⟫ + β / 2 * ‖ybar P x z β - x‖ ^ 2

/-- `η` as a function of the joint variable `(x, z)`, carried by the Euclidean (`L²`) product
`WithLp 2 (ℝⁿ × ℝⁿ)`, whose norm is `√(‖x‖² + ‖z‖²)`. -/
noncomputable def etaJoint {n : ℕ} (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ)
    (p : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) : ℝ :=
  eta P β p.fst p.snd

/-- The gradient `∇F(x)` of the composite objective `F = f ∘ g` of (1.1). -/
noncomputable def gradF {n m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  gradient (fun y => f (g y)) x

/-- The optimality measure (2.10): `V(x, z) = ‖ȳ(x, z, 1) − x‖² + ‖z − ∇F(x)‖²`. -/
noncomputable def V {n m : ℕ} (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖ybar P x z 1 - x‖ ^ 2 + ‖z - gradF f g x‖ ^ 2

/-- The optimal value `F* = inf_{x ∈ X} f(g(x))` of problem (1.1) (Notation, p. 5). Theorems using it assume
`F` bounded below on the nonempty set `X`, so this infimum is the true one. -/
noncomputable def Fstar {n m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf ((fun x => f (g x)) '' X)

/-- The merit function (3.15): `W(x, z, u) = a(F(x) − F*) − η(x, z) + γ/2 ‖g(x) − u‖²`, with `η` taken at
coefficient `β`. -/
noncomputable def W {n m : ℕ} (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (X : Set (EuclideanSpace ℝ (Fin n))) (a γ β : ℝ) (x z : EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin m)) : ℝ :=
  a * (f (g x) - Fstar f g X) - eta P β x z + γ / 2 * ‖g x - u‖ ^ 2

/-- Lemma 2's constant `L_∇F := L_g² L_∇f + L_f L_∇g`. -/
def LgradF (Lf Lg Ldf Ldg : ℝ) : ℝ := Lg ^ 2 * Ldf + Lf * Ldg

/-- Lemma 3's constant `L_∇η = 2 √((1 + β)² + (1 + 1/(2β))²)`. -/
noncomputable def Leta (β : ℝ) : ℝ := 2 * Real.sqrt ((1 + β) ^ 2 + (1 + 1 / (2 * β)) ^ 2)

/-- `L₁ := 2 L_∇F² / a² + 4 L_g⁴ L_∇f²` of (3.32), with `L_∇F = LgradF Lf Lg Ldf Ldg`. -/
noncomputable def L1 (a Lf Lg Ldf Ldg : ℝ) : ℝ := 2 * LgradF Lf Lg Ldf Ldg ^ 2 / a ^ 2 + 4 * Lg ^ 4 * Ldf ^ 2

/-- `L₂ := 4 L_g² L_∇f²` of (3.32). -/
def L2 (Lg Ldf : ℝ) : ℝ := 4 * Lg ^ 2 * Ldf ^ 2

/-- `Γ₁` of (3.27): `1` if `τ₀ = 1/a`, and `1 − aτ₀` if `τ₀ < 1/a`. -/
noncomputable def Gamma1 (a : ℝ) (τ : ℕ → ℝ) : ℝ := if τ 0 = 1 / a then 1 else 1 - a * τ 0

/-- `Γ_k` of (3.27): `Γ_k = Γ₁ ∏_{i=1}^{k-1} (1 − aτ_i)` for `k ≥ 1` (for `k = 1` the product is empty).
The paper does not define `Γ₀`; the formula gives `Γ₀ = Γ₁`, a value no statement uses. -/
noncomputable def Gamma (a : ℝ) (τ : ℕ → ℝ) (k : ℕ) : ℝ :=
  Gamma1 a τ * ∏ i ∈ Finset.Ico 1 k, (1 - a * τ i)

/-- The noise constant `σ²` of (3.26), in the form its proof establishes (see the theorems' notes):
`σ̂² = ½([aL_∇F + L_∇η + γL_g² + 2aL_g²L_∇f] · max(σ_J²σ_s², ‖z⁰‖²)/β² + γb²σ_G²
  + 4L_∇η[max(1, a²/2)‖z⁰‖² + 24a²σ_J²σ_s²])`.
The paper prints `L_∇F` for `aL_∇F`, `σ_J²σ_s²` for `max(σ_J²σ_s², ‖z⁰‖²)`, `b²σ_g²` for `γb²σ_G²`, and `‖z⁰‖²`
for `max(1, a²/2)‖z⁰‖²` (the two agree for `a ≤ √2`). -/
noncomputable def sigmaHatSq {n : ℕ} (a b γ β Lf Lg Ldf Ldg σG σJ σs : ℝ) (z0 : EuclideanSpace ℝ (Fin n)) :
    ℝ :=
  1 / 2 * ((a * LgradF Lf Lg Ldf Ldg + Leta β + γ * Lg ^ 2 + 2 * a * Lg ^ 2 * Ldf) *
      max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2) / β ^ 2
    + γ * b ^ 2 * σG ^ 2 + 4 * Leta β * (max 1 (a ^ 2 / 2) * ‖z0‖ ^ 2 + 24 * a ^ 2 * σJ ^ 2 * σs ^ 2))

end NestedSA.NASA


