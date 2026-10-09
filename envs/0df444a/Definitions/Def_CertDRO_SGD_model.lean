-- Prove2me | Definitions.Def_CertDRO_SGD_model
-- name    : CertDRO_SGD_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T18:18:55.331076+00:00
-- url     : https://prove2.me/theorems/36a3dddc-6a82-4744-b370-3d81dee1b1c4
-- title:
--   Assumptions A and B, the robust surrogate φ_γ, the objective F and the iterates of Algorithm 1
-- statement:
--   This file fixes the model of Sinha, Namkoong, Volpi and Duchi for stochastic gradient descent on the Wasserstein penalty problem.
--
--   **Spaces.** Parameters live in $\Theta=\mathbb R^d$ and data in a set $Z\subseteq\mathbb R^m$; both carry the Euclidean norm $\|\cdot\|_2$, which is its own dual norm.
--
--   **Assumption A** (with the standing conditions on the transportation cost). A cost $c:Z\times Z\to\mathbb R$ satisfies Assumption A when $c\ge0$ on $Z\times Z$, $c(z,z)=0$ for $z\in Z$, $c$ is continuous on $Z\times Z$, and for each $z_0\in Z$ the map $z\mapsto c(z,z_0)$ is $1$-strongly convex on $Z$:
--   $$c(tz+(1-t)z',z_0)\le t\,c(z,z_0)+(1-t)\,c(z',z_0)-\tfrac{t(1-t)}2\|z-z'\|_2^2 .$$
--
--   **Assumption B.** A function $f:\Theta\times\mathbb R^m\to\mathbb R$ with partial gradients $g_\theta(\theta,z)=\nabla_\theta f(\theta,z)$ and $g_z(\theta,z)=\nabla_z f(\theta,z)$ (for $z\in Z$) satisfies Assumption B with constants $L_{\theta\theta},L_{zz},L_{\theta z},L_{z\theta}\ge0$ when, for all $\theta,\theta'\in\Theta$ and $z,z'\in Z$,
--   $$\|g_\theta(\theta,z)-g_\theta(\theta',z)\|_2\le L_{\theta\theta}\|\theta-\theta'\|_2,\qquad \|g_z(\theta,z)-g_z(\theta,z')\|_2\le L_{zz}\|z-z'\|_2,$$
--   $$\|g_\theta(\theta,z)-g_\theta(\theta,z')\|_2\le L_{\theta z}\|z-z'\|_2,\qquad \|g_z(\theta,z)-g_z(\theta',z)\|_2\le L_{z\theta}\|\theta-\theta'\|_2 .$$
--
--   **Robust surrogate and objective.** For a loss $\ell$, a penalty $\gamma$ and $z_0\in\mathbb R^m$, write $f(\theta,z;z_0)=\ell(\theta;z)-\gamma c(z,z_0)$, and set $\bar f(\theta)=\sup_{z\in Z}f(\theta,z)$ for a general $f$. The robust surrogate (2b) and the objective are
--   $$\varphi_\gamma(\theta;z_0)=\sup_{z\in Z}\{\ell(\theta;z)-\gamma c(z,z_0)\},\qquad F(\theta)=\mathbb E_{P_0}[\varphi_\gamma(\theta;Z)] .$$
--   The smoothness constant of Theorem 2 is $L_\varphi=L_{\theta\theta}+L_{\theta z}L_{z\theta}/(\gamma-L_{zz})$.
--
--   **Maximizers.** A point $z_\star\in Z$ is a maximizer of $z\mapsto\ell(\theta;z)-\gamma c(z,z_0)$ over $Z$ if no point of $Z$ has a larger value; a point $\hat z\in Z$ is an $\epsilon$-approximate maximizer if $\ell(\theta;\hat z)-\gamma c(\hat z,z_0)\ge\varphi_\gamma(\theta;z_0)-\epsilon$. An $\epsilon$-oracle is a map $\hat z(\theta,z_0)$ returning an $\epsilon$-approximate maximizer for every $\theta$ and every $z_0\in Z$.
--
--   **Standing hypotheses.** $Z$ is nonempty, convex and closed, $c$ satisfies Assumption A, $\ell$ satisfies Assumption B, and $\gamma>L_{zz}$.
--
--   **Algorithm 1** with $\Theta=\mathbb R^d$ (so the projection is the identity), constant stepsize $\alpha$ and samples $z^0,\dots,z^{T-1}$: $\theta^0$ is given and
--   $$\theta^{t+1}=\theta^t-\alpha\,\nabla_\theta\ell(\theta^t;\hat z^t),\qquad \hat z^t=\hat z(\theta^t,z^t),\qquad t=0,\dots,T-1 .$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\Theta$ and $\mathbb R^m$ are `EuclideanSpace ℝ (Fin d)` and `EuclideanSpace ℝ (Fin m)`. The cost is real valued and only its values on $Z\times Z$ are constrained. The loss is defined on all of $\Theta\times\mathbb R^m$ and its partial gradients are required at points of $Z$ only; the Lipschitz conditions are required on $Z$ only. Suprema are `sSup` of the image of $Z$; under the standing hypotheses and $z_0\in Z$ the set is nonempty and bounded above, so this is the true supremum. $F$ is a Bochner integral; the theorems assume $\varphi_\gamma(\theta;\cdot)$ is $P_0$-integrable for every $\theta$. Strong convexity uses Mathlib's `StrongConvexOn Z 1`, whose modulus convention $\tfrac m2\|x-y\|^2$ matches the paper's. The iterate sequence is indexed by $\mathbb N$ and frozen after step $T$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 4 (cost c, (4)); p. 5, Assumptions A and B, (2b), Lemma 1 (f̄); p. 6, Algorithm 1, Theorem 2 (F, L_φ); p. 40, §B.3 (f(θ, z; z₀))

import Mathlib

namespace CertDRO.SGD

open MeasureTheory

/-- The parameter space `Θ = ℝ^d` with the Euclidean (ℓ²) norm. -/
abbrev Param (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The ambient data space `ℝ^m` with the Euclidean (ℓ²) norm; the data set `Z` is a subset of it. -/
abbrev Data (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- Assumption A (p. 5), with the standing conditions on the transportation cost of p. 4, for the
ℓ²-norm: on `Z × Z` the cost `c` is nonnegative, continuous and vanishes on the diagonal, and for
each `z₀ ∈ Z` the map `z ↦ c(z, z₀)` is `1`-strongly convex on `Z`. Values of `c` outside `Z × Z`
are irrelevant. -/
structure AssumptionA {m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ) : Prop where
  nonneg : ∀ z ∈ Z, ∀ z₀ ∈ Z, 0 ≤ c z z₀
  diag : ∀ z ∈ Z, c z z = 0
  continuousOn : ContinuousOn (Function.uncurry c) (Z ×ˢ Z)
  strongConvexOn : ∀ z₀ ∈ Z, StrongConvexOn Z 1 (fun z => c z z₀)

/-- Assumption B (p. 5) for a function `f : Θ × ℝ^m → ℝ` on `Θ × Z`, for the ℓ²-norm (whose dual norm
is again the ℓ²-norm): `gθ θ z` is the gradient of `f(·, z)` at `θ`, `gz θ z` is the gradient of
`f(θ, ·)` at `z` (for `z ∈ Z`), and the four Lipschitz conditions hold with nonnegative constants
`Lθθ, Lzz, Lθz, Lzθ`. -/
structure AssumptionB {d m : ℕ} (Z : Set (Data m)) (f : Param d → Data m → ℝ)
    (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ : ℝ) : Prop where
  hasGradientAt_θ : ∀ θ, ∀ z ∈ Z, HasGradientAt (fun θ' => f θ' z) (gθ θ z) θ
  hasGradientAt_z : ∀ θ, ∀ z ∈ Z, HasGradientAt (fun z' => f θ z') (gz θ z) z
  Lθθ_nonneg : 0 ≤ Lθθ
  Lzz_nonneg : 0 ≤ Lzz
  Lθz_nonneg : 0 ≤ Lθz
  Lzθ_nonneg : 0 ≤ Lzθ
  lip_θθ : ∀ θ θ', ∀ z ∈ Z, ‖gθ θ z - gθ θ' z‖ ≤ Lθθ * ‖θ - θ'‖
  lip_zz : ∀ θ, ∀ z ∈ Z, ∀ z' ∈ Z, ‖gz θ z - gz θ z'‖ ≤ Lzz * ‖z - z'‖
  lip_θz : ∀ θ, ∀ z ∈ Z, ∀ z' ∈ Z, ‖gθ θ z - gθ θ z'‖ ≤ Lθz * ‖z - z'‖
  lip_zθ : ∀ θ θ', ∀ z ∈ Z, ‖gz θ z - gz θ' z‖ ≤ Lzθ * ‖θ - θ'‖

/-- The supremum `f̄(θ) = sup_{z ∈ Z} f(θ, z)` of Lemma 1 (p. 5). -/
noncomputable def supOver {d m : ℕ} (Z : Set (Data m)) (f : Param d → Data m → ℝ) (θ : Param d) : ℝ :=
  sSup (f θ '' Z)

/-- The penalized loss `f(θ, z; z₀) = ℓ(θ; z) − γ c(z, z₀)` (§B.3, p. 40). -/
def penalized {d m : ℕ} (ℓ : Param d → Data m → ℝ) (c : Data m → Data m → ℝ) (γ : ℝ)
    (z₀ : Data m) (θ : Param d) (z : Data m) : ℝ :=
  ℓ θ z - γ * c z z₀

/-- The robust surrogate (2b), p. 5: `φ_γ(θ; z₀) = sup_{z ∈ Z} { ℓ(θ; z) − γ c(z, z₀) }`. -/
noncomputable def robustSurrogate {d m : ℕ} (Z : Set (Data m)) (ℓ : Param d → Data m → ℝ)
    (c : Data m → Data m → ℝ) (γ : ℝ) (θ : Param d) (z₀ : Data m) : ℝ :=
  supOver Z (penalized ℓ c γ z₀) θ

/-- The robust surrogate objective `F(θ) = E_{P₀}[φ_γ(θ; Z)]` (p. 6), a Bochner integral. -/
noncomputable def robustObjective {d m : ℕ} (Z : Set (Data m)) (ℓ : Param d → Data m → ℝ)
    (c : Data m → Data m → ℝ) (γ : ℝ) (P₀ : Measure (Data m)) (θ : Param d) : ℝ :=
  ∫ z, robustSurrogate Z ℓ c γ θ z ∂P₀

/-- The smoothness constant of Theorem 2 (p. 6): `L_φ = Lθθ + Lθz Lzθ / (γ − Lzz)`. -/
noncomputable def Lphi (Lθθ Lzz Lθz Lzθ γ : ℝ) : ℝ :=
  Lθθ + Lθz * Lzθ / (γ - Lzz)

/-- `zs` is a maximizer of `z ↦ ℓ(θ; z) − γ c(z, z₀)` over `Z`. -/
def IsMaximizer {d m : ℕ} (Z : Set (Data m)) (ℓ : Param d → Data m → ℝ)
    (c : Data m → Data m → ℝ) (γ : ℝ) (θ : Param d) (z₀ zs : Data m) : Prop :=
  zs ∈ Z ∧ ∀ z ∈ Z, penalized ℓ c γ z₀ θ z ≤ penalized ℓ c γ z₀ θ zs

/-- `zh` is an `ε`-approximate maximizer of `z ↦ ℓ(θ; z) − γ c(z, z₀)` over `Z` (Algorithm 1, p. 6):
`zh ∈ Z` and `ℓ(θ; zh) − γ c(zh, z₀) ≥ φ_γ(θ; z₀) − ε`. -/
def IsApproxMaximizer {d m : ℕ} (Z : Set (Data m)) (ℓ : Param d → Data m → ℝ)
    (c : Data m → Data m → ℝ) (γ ε : ℝ) (θ : Param d) (z₀ zh : Data m) : Prop :=
  zh ∈ Z ∧ robustSurrogate Z ℓ c γ θ z₀ - ε ≤ penalized ℓ c γ z₀ θ zh

/-- The standing hypotheses of Theorem 2 and of the §2.1 paragraph after Algorithm 1 (pp. 5–6):
`Z ⊆ ℝ^m` is nonempty, convex and closed; the cost satisfies Assumption A; the loss `ℓ`, with partial
gradients `gθ`, `gz`, satisfies Assumption B; and the penalty exceeds the smoothness in `z`,
`γ > Lzz`. -/
structure Standing {d m : ℕ} (Z : Set (Data m)) (c : Data m → Data m → ℝ)
    (ℓ : Param d → Data m → ℝ) (gθ : Param d → Data m → Param d) (gz : Param d → Data m → Data m)
    (Lθθ Lzz Lθz Lzθ γ : ℝ) : Prop where
  nonempty : Z.Nonempty
  convex : Convex ℝ Z
  closed : IsClosed Z
  assumptionA : AssumptionA Z c
  assumptionB : AssumptionB Z ℓ gθ gz Lθθ Lzz Lθz Lzθ
  gamma_gt : Lzz < γ

/-- An `ε`-approximate maximization oracle for Algorithm 1: for every `θ` and every `z₀ ∈ Z`,
`zhat θ z₀` is an `ε`-approximate maximizer of `z ↦ ℓ(θ; z) − γ c(z, z₀)` over `Z`. -/
def IsOracle {d m : ℕ} (Z : Set (Data m)) (ℓ : Param d → Data m → ℝ)
    (c : Data m → Data m → ℝ) (γ ε : ℝ) (zhat : Param d → Data m → Data m) : Prop :=
  ∀ θ, ∀ z₀ ∈ Z, IsApproxMaximizer Z ℓ c γ ε θ z₀ (zhat θ z₀)

/-- The iterates of Algorithm 1 (p. 6) with `Θ = ℝ^d` (so `Proj_Θ` is the identity) and constant
stepsize `α`, driven by the samples `ω = (z⁰, …, z^{T−1})`:
`θ⁰ = θ₀`, `θ^{t+1} = θ^t − α ∇_θ ℓ(θ^t; ẑ^t)` with `ẑ^t = zhat θ^t z^t`, for `t < T`.
(After step `T` the sequence is frozen; only `t ≤ T` is used.) -/
noncomputable def run {d m T : ℕ} (gθ : Param d → Data m → Param d)
    (zhat : Param d → Data m → Data m) (α : ℝ) (θ₀ : Param d) (ω : Fin T → Data m) :
    ℕ → Param d
  | 0 => θ₀
  | t + 1 =>
    if h : t < T then
      run gθ zhat α θ₀ ω t - α • gθ (run gθ zhat α θ₀ ω t) (zhat (run gθ zhat α θ₀ ω t) (ω ⟨t, h⟩))
    else run gθ zhat α θ₀ ω t

end CertDRO.SGD


