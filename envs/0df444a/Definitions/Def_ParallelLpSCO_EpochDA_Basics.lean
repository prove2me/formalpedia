-- Prove2me | Definitions.Def_ParallelLpSCO_EpochDA_Basics
-- name    : ParallelLpSCO_EpochDA_Basics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:03:59.878061+00:00
-- url     : https://prove2.me/theorems/22e3782c-c5ff-4cd1-9c18-b358bc1b4462
-- title:
--   ℓp norms, $J_p$, subgradients, the ℓp Gaussian $GG_p$, $\hat f_{\rho,p}$ (Def. 1), p-GREG (Def. 2), Problem 1 oracles, Assumption 1, Definitions 5 and 7
-- statement:
--   Points of $\mathbb R^d$ are vectors $x=(x_1,\dots,x_d)$, and $\langle u,v\rangle=\sum_i u_iv_i$. Fix a real exponent $p$ (the paper's standing range is $p\in[2,\infty)$) and its Hölder conjugate $q=p/(p-1)$.
--
--   - The **ℓp norm** is $\|x\|_p=(\sum_i|x_i|^p)^{1/p}$ and $B_p(c,r)=\{x:\|x-c\|_p\le r\}$ is the closed ℓp ball.
--   - $J_p(z)=(|z_i|^{p-2}z_i)_{i}$ is the gradient of $\|z\|_p^p/p$, and for $\Phi(x)=\|x-c\|_p^p/p$ the **Bregman divergence** is $D_\Phi(x,y)=\Phi(x)-\Phi(y)-\langle J_p(y-c),x-y\rangle$.
--   - $v$ is a **subgradient** of $f:\mathbb R^d\to\mathbb R$ at $x$ when $f(y)\ge f(x)+\langle v,y-x\rangle$ for all $y$ (the published `LinearOptimization.IsSubgradientOn` on the whole space).
--   - The **generalized ℓp Gaussian** $GG_p(\mu,\sigma^2)$ has density
--   $$\Big(\frac{(2\Gamma(1+1/p))^d}{\Gamma(1+d/p)}(2\sigma^2)^{d/2}\Gamma(1+d/2)\Big)^{-1}\exp\Big(-\frac{\|x-\mu\|_p^2}{2\sigma^2}\Big);$$
--   $\gamma_{\rho,p}$ is the density of $GG_p(0,\rho^2)$ and `ggLaw d p ρ` its law ($\sigma^2$ is a scale, not the variance).
--   - **Definition 1.** $\hat f_{\rho,p}(x)=\int f(x-y)\gamma_{\rho,p}(y)\,dy$.
--   - **Definition 2.** Given $\xi\sim GG_p(0,\rho^2)$ and the oracle's answer $a=g(\bar x+\xi)$, the **p-GREG estimator** is $\tilde\nabla^g_{\bar x}\hat f_{\rho,p}(x)=\frac{\gamma_{\rho,p}(x-\bar x-\xi)}{\gamma_{\rho,p}(\xi)}\,a$.
--   - A **stochastic oracle** is a map $g(x,u)$: the answer at $x$ to a query whose fresh uniform draw is $u\in[0,1]$. Its $q$-th moment at $x$ is $\mathbb E_u\|g(x,u)\|_q^q$. **Problem 1's oracle** for $f$ with constant $L$: for every $x$, $g(x,\cdot)$ is a random vector with $\mathbb E[g(x)]\in\partial f(x)$ and $\mathbb E\|g(x)\|_q^q\le L^q$.
--   - **Assumption 1.** $X$ is closed and convex, $F$ is convex on $X$, and some unbiased subgradient estimator (subgradients relative to $X$) has $\mathbb E\|\hat\nabla F(x)\|_q^q\le G^q$ for all $x\in X$.
--   - `IsBallProx p F X r λ x̄ x⋆`: $x^\star$ minimizes $F(x)+\frac\lambda p\|x-\bar x\|_p^p$ over $X\cap B_p(\bar x,r)$ (the point $x^\star_{\bar x,\lambda}$ of Definitions 6–8, read as local minimization over $X\cap B_p(\bar x,r)$, as Propositions 11–12 say).
--   - **Definition 7**, for one call: a random output $x$ satisfies $\mathbb E[F(x)+\frac\lambda p\|x-\bar x\|_p^p]\le F(x^\star)+\frac\lambda p\|x^\star-\bar x\|_p^p+\phi$ (the expectation exists).
--   - **Definition 5** (BROO of radius $r$ for $F$ on $X$): for every query $x\in X$, $\lambda>0$, $\rho>0$, the point $\tilde x=O_{\lambda,\rho}(x)$ lies in $X\cap B_p(x,r)$ and $F(\tilde x)+\frac\lambda p\|\tilde x-x\|_p^p\le \min_{x'\in X\cap B_p(x,r)}\{F(x')+\frac\lambda p\|x'-x\|_p^p\}+\frac{\lambda2^{2-p}}{p}\rho^p$.
--
--   **Formalization Note.** Vectors are `Fin d → ℝ`; `lpNorm` is the explicit sum, not `PiLp`. Expectations of vectors are Bochner integrals and $q$-th moments are lower Lebesgue integrals in $[0,\infty]$. The oracle is a map of the query point and a uniform draw; every law on $\mathbb R^d$ is the image of a uniform draw, so this is no restriction. In Definition 5, "$\min_{x'\in B_r(x)}$" is taken over $X\cap B_p(x,r)$ since $F$ is defined on $X$, and "$\le\min+\text{tol}$" is written as "$\le$ every value $+$ tol".
-- source:
--   Nie, Shyam, Bullins, Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in ℓp Geometries, STOC 2027 submission (manuscript, sha256 fe68639b…), pp. 5–7 (§1.3, §2.1–2.2: GG_p density, Definitions 1–2), p. 31 (Assumption 1), p. 32 (J_p, Definition 5), p. 47 (Problem 1, Definition 7)

import Mathlib
import Definitions.Def_LinearOptimization_Subgradient

open MeasureTheory

/-!
# ℓp geometry, the generalized ℓp Gaussian, p-GREG and the stochastic gradient oracle

Nie, Shyam, Bullins, *Bias-Reduced and Parallel Heavy-Tailed Stochastic Convex Optimization in
ℓp Geometries*, STOC 2027 submission (manuscript, sha256 fe68639b…): §1.3 pp. 5–6 (notation),
§2 p. 7 (the GG_p density, Definition 1, Definition 2), §3 p. 31 (Assumption 1), §3.5 p. 32
(J_p, Definition 5), §4.1 p. 47 (Problem 1, Definition 7).

Points of `ℝ^d` are `Fin d → ℝ`; the pairing `⟨u, v⟩` is the dot product. The exponent `p` is a
real number (the paper's standing range is `p ∈ [2, ∞)`), and `q = p/(p − 1)` is its Hölder
conjugate. A random answer of the oracle at a point is the image of one uniform draw from
`[0, 1]` (`unitInterval`) under a map `g x`: every law on `ℝ^d` arises this way, and a fresh draw
per query makes the answers independent.
-/

namespace ParallelLpSCO.EpochDA

/-- Points of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- The Hölder conjugate `q = p/(p − 1)` of `p`. -/
noncomputable def conjExp (p : ℝ) : ℝ := p / (p - 1)

/-- The ℓp norm `‖x‖_p = (∑ᵢ |xᵢ|^p)^{1/p}`. -/
noncomputable def lpNorm {d : ℕ} (p : ℝ) (x : Vec d) : ℝ :=
  (∑ i, |x i| ^ p) ^ (1 / p)

/-- The closed ℓp ball `B_p(c, r) = {x : ‖x − c‖_p ≤ r}`. -/
def lpBall {d : ℕ} (p : ℝ) (c : Vec d) (r : ℝ) : Set (Vec d) :=
  {x | lpNorm p (x - c) ≤ r}

/-- `J_p(z) = (|zᵢ|^{p−2} zᵢ)ᵢ`, the gradient of `‖z‖_p^p / p`. -/
noncomputable def Jp {d : ℕ} (p : ℝ) (z : Vec d) : Vec d :=
  fun i => |z i| ^ (p - 2) * z i

/-- `v` is a subgradient of `f : ℝ^d → ℝ` at `x`: `f y ≥ f x + ⟨v, y − x⟩` for every `y`
(the published `LinearOptimization.IsSubgradientOn` on the whole space). -/
def IsSubgrad {d : ℕ} (f : Vec d → ℝ) (x v : Vec d) : Prop :=
  LinearOptimization.IsSubgradientOn f Set.univ v x

/-- The Bregman divergence of `Φ(x) = ‖x − c‖_p^p / p`:
`D_Φ(x, y) = Φ(x) − Φ(y) − ⟨J_p(y − c), x − y⟩`. -/
noncomputable def bregman {d : ℕ} (p : ℝ) (c x y : Vec d) : ℝ :=
  lpNorm p (x - c) ^ p / p - lpNorm p (y - c) ^ p / p - ∑ i, Jp p (y - c) i * (x i - y i)

/-! ## The generalized ℓp Gaussian `GG_p(µ, σ²)` (§2.1, p. 7) -/

/-- The normalizer `(2Γ(1 + 1/p))^d / Γ(1 + d/p) · (2σ²)^{d/2} Γ(1 + d/2)` of `GG_p(µ, σ²)`. -/
noncomputable def ggNormalizer (d : ℕ) (p σ : ℝ) : ℝ :=
  (2 * Real.Gamma (1 + 1 / p)) ^ d / Real.Gamma (1 + (d : ℝ) / p) *
    (2 * σ ^ 2) ^ ((d : ℝ) / 2) * Real.Gamma (1 + (d : ℝ) / 2)

/-- The density of `GG_p(µ, σ²)` at `x`: `ggNormalizer⁻¹ · exp(−‖x − µ‖_p² / (2σ²))`.
`σ²` is a scale parameter, not the variance. -/
noncomputable def ggDensity {d : ℕ} (p : ℝ) (μ : Vec d) (σ : ℝ) (x : Vec d) : ℝ :=
  (ggNormalizer d p σ)⁻¹ * Real.exp (-(lpNorm p (x - μ)) ^ 2 / (2 * σ ^ 2))

/-- `γ_{ρ,p}`: the density of `GG_p(0, ρ²)`. -/
noncomputable def gamma {d : ℕ} (p ρ : ℝ) (x : Vec d) : ℝ :=
  ggDensity p 0 ρ x

/-- The law `GG_p(0, ρ²)` on `ℝ^d`: Lebesgue measure with density `γ_{ρ,p}`. -/
noncomputable def ggLaw (d : ℕ) (p ρ : ℝ) : Measure (Vec d) :=
  volume.withDensity fun x => ENNReal.ofReal (gamma p ρ x)

/-- Definition 1 (GG_p-convolution): `f̂_{ρ,p}(x) = ∫ f(x − y) γ_{ρ,p}(y) dy`. -/
noncomputable def fHat {d : ℕ} (p ρ : ℝ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ y, f (x - y) * gamma p ρ y

/-- Definition 2 (p-GREG estimator of radius `ρ` at `x`, anchored at `x̄`), given the sample
`ξ ∼ GG_p(0, ρ²)` and the oracle's answer `a = g(x̄ + ξ)` at the point `x̄ + ξ`:
`(γ_{ρ,p}(x − x̄ − ξ) / γ_{ρ,p}(ξ)) · a`. -/
noncomputable def pgreg {d : ℕ} (p ρ : ℝ) (xbar x ξ a : Vec d) : Vec d :=
  (gamma p ρ (x - xbar - ξ) / gamma p ρ ξ) • a

/-! ## Stochastic gradient oracles (Problem 1, p. 47; Assumption 1, p. 31) -/

/-- A stochastic oracle on `ℝ^d`: the answer at `x` to a query whose fresh uniform draw is `u`. -/
abbrev Oracle (d : ℕ) := Vec d → unitInterval → Vec d

/-- The `q`-th moment `E‖g(x)‖_q^q` of the oracle's answer at `x`, `q = p/(p − 1)`. -/
noncomputable def qMoment {d : ℕ} (p : ℝ) (g : Oracle d) (x : Vec d) : ENNReal :=
  ∫⁻ u, ENNReal.ofReal (lpNorm (conjExp p) (g x u) ^ conjExp p)

/-- Problem 1's oracle: for every `x`, `g(x)` is a random vector with `E[g(x)] ∈ ∂f(x)` and
`E‖g(x)‖_q^q ≤ L^q`. (The mean is a Bochner integral; it exists because the `q`-th moment is
finite, `q > 1`.) -/
def IsGradOracle {d : ℕ} (p L : ℝ) (f : Vec d → ℝ) (g : Oracle d) : Prop :=
  ∀ x, AEStronglyMeasurable (g x) volume ∧ IsSubgrad f x (∫ u, g x u) ∧
    qMoment p g x ≤ ENNReal.ofReal (L ^ conjExp p)

/-- Assumption 1 (p. 31): `F : X → ℝ` is convex, `X` is closed and convex, and there is an
unbiased subgradient estimator with `E‖∇̂F(x)‖_q^q ≤ G^q` for all `x ∈ X` (subgradients relative
to `X`). Values of `F` outside `X` play no role. -/
def Assumption1 {d : ℕ} (p : ℝ) (F : Vec d → ℝ) (X : Set (Vec d)) : Prop :=
  IsClosed X ∧ Convex ℝ X ∧ ConvexOn ℝ X F ∧
    ∃ (G : ℝ) (g : Oracle d), ∀ x ∈ X, AEStronglyMeasurable (g x) volume ∧
      LinearOptimization.IsSubgradientOn F X (∫ u, g x u) x ∧
      qMoment p g x ≤ ENNReal.ofReal (G ^ conjExp p)

/-! ## Proximal points and the oracles of §3.5 and §4.1 -/

/-- `x⋆` minimizes `F(x) + (λ/p)‖x − x̄‖_p^p` over `X ∩ B_p(x̄, r)` (the point `x⋆_{x̄,λ}` of
Definitions 6–8 read as in Propositions 11–12: local minimization over `X ∩ B_p(x̄, r)`). -/
def IsBallProx {d : ℕ} (p : ℝ) (F : Vec d → ℝ) (X : Set (Vec d)) (r lam : ℝ)
    (xbar xstar : Vec d) : Prop :=
  xstar ∈ X ∩ lpBall p xbar r ∧
    ∀ x ∈ X ∩ lpBall p xbar r,
      F xstar + lam / p * lpNorm p (xstar - xbar) ^ p ≤ F x + lam / p * lpNorm p (x - xbar) ^ p

/-- Definition 7 for one call: the random output `x` (on `(Ω, P)`) of a call at `x̄` satisfies
`E[F(x) + (λ/p)‖x − x̄‖_p^p] ≤ F(x⋆) + (λ/p)‖x⋆ − x̄‖_p^p + ϕ` (the expectation exists). -/
def BallOracleGuarantee {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (p : ℝ) (F : Vec d → ℝ)
    (lam phi : ℝ) (xbar xstar : Vec d) (P : Measure Ω) (x : Ω → Vec d) : Prop :=
  Integrable (fun ω => F (x ω) + lam / p * lpNorm p (x ω - xbar) ^ p) P ∧
    ∫ ω, (F (x ω) + lam / p * lpNorm p (x ω - xbar) ^ p) ∂P ≤
      F xstar + lam / p * lpNorm p (xstar - xbar) ^ p + phi

/-- Definition 5 (Ball Regularized Optimization Oracle of radius `r` for `F` on `X`): for every
query `x ∈ X`, `λ > 0`, `ρ > 0`, the point `x̃ = O λ ρ x` lies in `X ∩ B_p(x, r)` and
`F(x̃) + (λ/p)‖x̃ − x‖_p^p ≤ min_{x' ∈ X ∩ B_p(x, r)} {F(x') + (λ/p)‖x' − x‖_p^p} + λ 2^{2−p} ρ^p / p`. -/
def IsBROO {d : ℕ} (p : ℝ) (F : Vec d → ℝ) (X : Set (Vec d)) (r : ℝ)
    (O : ℝ → ℝ → Vec d → Vec d) : Prop :=
  ∀ x ∈ X, ∀ lam > 0, ∀ ρ > 0,
    O lam ρ x ∈ X ∩ lpBall p x r ∧
      ∀ x' ∈ X ∩ lpBall p x r,
        F (O lam ρ x) + lam / p * lpNorm p (O lam ρ x - x) ^ p ≤
          F x' + lam / p * lpNorm p (x' - x) ^ p + lam * (2 : ℝ) ^ (2 - p) * ρ ^ p / p

end ParallelLpSCO.EpochDA


