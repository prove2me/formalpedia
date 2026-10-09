-- Prove2me | Definitions.Def_DistCov_Indep_Setting
-- name    : DistCov_Indep_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:30:20.46805+00:00
-- url     : https://prove2.me/theorems/0cb74bc1-3939-45a4-bb98-c3932be64ff5
-- title:
--   pp. 3–4, 9–11, 13, 15 — finite first moment, a_µ, D(µ), D(µ₁ − µ₂), d_µ, dcov(θ), negative and strong negative type, embeddings, barycenters, tensor embedding
-- statement:
--   This file sets up the objects of Lyons' theory of distance covariance on metric spaces.
--
--   **Moments and centred distances (p. 3).** Let $(\mathcal X,d)$ be a metric space with its Borel $\sigma$-field. A finite (positive) measure $\mu$ on $\mathcal X$ has a **finite first moment** if $\int_{\mathcal X} d(o,x)\,d\mu(x)<\infty$ for some $o\in\mathcal X$; by the triangle inequality the choice of $o$ does not matter. For such $\mu$ define
--   $$a_\mu(x):=\int d(x,x')\,d\mu(x'),\qquad D(\mu):=\int d(x,x')\,d\mu^2(x,x'),$$
--   $$d_\mu(x,x'):=d(x,x')-a_\mu(x)-a_\mu(x')+D(\mu).$$
--   For two finite measures $\mu_1,\mu_2$ the quantity $D(\mu_1-\mu_2)$ is the integral of $d$ against the signed measure $(\mu_1-\mu_2)^2$, i.e.
--   $$D(\mu_1-\mu_2)=\iint d\,d(\mu_1\times\mu_1)-2\iint d\,d(\mu_1\times\mu_2)+\iint d\,d(\mu_2\times\mu_2).$$
--
--   **Distance covariance (p. 4).** For a second metric space $(\mathcal Y,d)$ and a probability measure $\theta$ on $\mathcal X\times\mathcal Y$ with marginals $\mu$ on $\mathcal X$ and $\nu$ on $\mathcal Y$, both of finite first moment, set $\delta_\theta((x,y),(x',y')):=d_\mu(x,x')\,d_\nu(y,y')$ and
--   $$\operatorname{dcov}(\theta):=\int \delta_\theta\big((x,y),(x',y')\big)\,d\theta^2\big((x,y),(x',y')\big).$$
--   $\theta$ is a **product measure** if $\theta=\mu\times\nu$, the product of its own marginals.
--
--   **Negative type (pp. 9, 11).** $(\mathcal X,d)$ has **negative type** if for all $n$, all $x_1,\dots,x_n\in\mathcal X$ and all real $\alpha_1,\dots,\alpha_n$ with $\sum_i\alpha_i=0$,
--   $$\sum_{i,j\le n}\alpha_i\alpha_j\,d(x_i,x_j)\le 0. \tag{3.1}$$
--   It has **strong negative type** if it has negative type and, for probability measures $\mu_1,\mu_2$ with finite first moments, $D(\mu_1-\mu_2)=0$ only when $\mu_1=\mu_2$.
--
--   **Embeddings and barycenters (pp. 10–11, 13, 15).** For a real Hilbert space $H$, an **embedding** is a map $\phi:\mathcal X\to H$ with $d(x,x')=\|\phi(x)-\phi(x')\|^2$ for all $x,x'$, i.e. an isometric embedding of $(\mathcal X,d^{1/2})$. Its **barycenter map** is $\beta_\phi(\mu):=\int\phi(x)\,d\mu(x)$. $M^1(\mathcal X)$ is the set of finite signed measures $\mu$ such that $|\mu|$ has a finite first moment; $M^{1,1}(\mathcal X\times\mathcal Y)$ is the set of finite signed $\theta$ such that both marginals of $|\theta|$ have finite first moment. Recorded here are: injectivity of $\beta_\phi$ on probability measures with finite first moment; injectivity of $\beta_\phi$ on $M^1(\mathcal X)$; and, for the **tensor embedding** $(x,y)\mapsto\phi(x)\otimes\psi(y)$ into the Hilbert tensor product $H\otimes K$ (with $\langle h_1\otimes k_1,h_2\otimes k_2\rangle=\langle h_1,h_2\rangle\langle k_1,k_2\rangle$), injectivity of $\beta_{\phi\otimes\psi}$ on $M^{1,1}(\mathcal X\times\mathcal Y)$. Finally $\ell^2(\mathbb N)$ is the real sequence space used as the target of existence statements.
--
--   **Formalization Note** Measures are Mathlib `Measure`s (positive). Since the Bochner integral does not integrate against signed measures, $D(\mu_1-\mu_2)$ is defined by its bilinear expansion (`Ddiff`, with `energy μ₁ μ₂` the cross term). Injectivity on $M^1(\mathcal X)$ is encoded through pairs of finite measures: $\beta_\phi(m_1)=\beta_\phi(m_2)\Rightarrow m_1=m_2$ for finite $m_1,m_2$ with finite first moment; this is equivalent to injectivity on signed measures because $\mu\in M^1$ iff its Jordan parts $\mu^\pm$ have finite first moment, and $\beta$ is linear. The same encoding, with finite first moments of both marginals of $m_1$ and of $m_2$, is used for $M^{1,1}$. The Hilbert tensor product is the completion `UniformSpace.Completion (H ⊗[ℝ] K)` of the algebraic tensor product with Mathlib's inner product. Hilbert spaces are real (Errata (viii), p. 27). The definitions themselves are total functions; the theorems of this mission state the finite-first-moment, separability and Borel hypotheses that make every integral here genuine.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), pp. 3–4 (§2: finite first moment, a_µ, D(µ), d_µ, δ_θ, dcov), p. 9 ((3.1), negative type), pp. 10–11 (embedding, (3.3), strong negative type, barycenter map), p. 13 (tensor embedding), p. 15 (M¹, M^{1,1}); Errata (i), p. 24 and (viii), p. 27

import Mathlib

namespace DistCov.Indep

open MeasureTheory
open scoped TensorProduct

variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [MetricSpace Y] [MeasurableSpace Y]
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- p. 3: `μ` has a finite first moment if `∫ d(o, x) dμ(x) < ∞` for some `o`. For a (positive)
measure; the choice of `o` does not matter by the triangle inequality. -/
def FiniteFirstMoment (μ : Measure X) : Prop := ∃ o : X, Integrable (fun x => dist o x) μ

/-- `a_μ(x) := ∫ d(x, x′) dμ(x′)` (p. 3). -/
noncomputable def meanDist (μ : Measure X) (x : X) : ℝ := ∫ x', dist x x' ∂μ

/-- `∫∫ d(x, x′) dμ₁(x) dμ₂(x′)`, over the product measure `μ₁ × μ₂`. -/
noncomputable def energy (μ₁ μ₂ : Measure X) : ℝ := ∫ p, dist p.1 p.2 ∂(μ₁.prod μ₂)

/-- `D(μ) := ∫ d(x, x′) dμ²(x, x′)` (p. 3). -/
noncomputable def D (μ : Measure X) : ℝ := energy μ μ

/-- `D(μ₁ − μ₂)` for two finite measures: the bilinear expansion of `∫ d d(μ₁ − μ₂)²`. -/
noncomputable def Ddiff (μ₁ μ₂ : Measure X) : ℝ := energy μ₁ μ₁ - 2 * energy μ₁ μ₂ + energy μ₂ μ₂

/-- `d_μ(x, x′) := d(x, x′) − a_μ(x) − a_μ(x′) + D(μ)` (p. 3). -/
noncomputable def dcent (μ : Measure X) (x x' : X) : ℝ :=
  dist x x' - meanDist μ x - meanDist μ x' + D μ

/-- `dcov(θ) := ∫ δ_θ dθ²`, with `δ_θ((x, y), (x′, y′)) = d_μ(x, x′) d_ν(y, y′)` and `μ`, `ν` the
marginals of `θ` (p. 4). -/
noncomputable def dcov (θ : Measure (X × Y)) : ℝ :=
  ∫ pq, dcent (θ.map Prod.fst) pq.1.1 pq.2.1 * dcent (θ.map Prod.snd) pq.1.2 pq.2.2 ∂(θ.prod θ)

/-- (3.1), p. 9: `(X, d)` has negative type. -/
def NegType (X : Type*) [MetricSpace X] : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (α : Fin n → ℝ), ∑ i, α i = 0 →
    ∑ i, ∑ j, α i * α j * dist (x i) (x j) ≤ 0

/-- p. 11: negative type, and equality in (3.3), `D(μ₁ − μ₂) ≤ 0`, only when `μ₁ = μ₂`, for
probability measures with finite first moment. -/
def StrongNegType (X : Type*) [MetricSpace X] [MeasurableSpace X] : Prop :=
  NegType X ∧ ∀ μ₁ μ₂ : Measure X, IsProbabilityMeasure μ₁ → IsProbabilityMeasure μ₂ →
    FiniteFirstMoment μ₁ → FiniteFirstMoment μ₂ → Ddiff μ₁ μ₂ = 0 → μ₁ = μ₂

/-- `θ` is a product measure: it equals the product of its own marginals. -/
def IsProduct (θ : Measure (X × Y)) : Prop := θ = (θ.map Prod.fst).prod (θ.map Prod.snd)

/-- p. 10: an embedding is an isometric embedding of `(X, d^{1/2})`: `d(x, x′) = ‖ϕ(x) − ϕ(x′)‖²`. -/
def IsNegTypeEmbedding (ϕ : X → H) : Prop := ∀ x x', dist x x' = ‖ϕ x - ϕ x'‖ ^ 2

/-- p. 11: the barycenter `β_ϕ(μ) = ∫ ϕ dμ`. -/
noncomputable def bary (ϕ : X → H) (μ : Measure X) : H := ∫ x, ϕ x ∂μ

/-- `β_ϕ` is injective on the probability measures with finite first moment (Proposition 3.1). -/
def BaryInjProb (ϕ : X → H) : Prop :=
  ∀ μ₁ μ₂ : Measure X, IsProbabilityMeasure μ₁ → IsProbabilityMeasure μ₂ →
    FiniteFirstMoment μ₁ → FiniteFirstMoment μ₂ → bary ϕ μ₁ = bary ϕ μ₂ → μ₁ = μ₂

/-- `β_ϕ` is injective on `M¹(X)`: for finite measures `m₁`, `m₂` with finite first moment,
`β_ϕ(m₁) = β_ϕ(m₂)` forces `m₁ = m₂` (every `μ ∈ M¹(X)` is `m₁ − m₂` by the Jordan
decomposition). -/
def BaryInjM1 (ϕ : X → H) : Prop :=
  ∀ m₁ m₂ : Measure X, IsFiniteMeasure m₁ → IsFiniteMeasure m₂ →
    FiniteFirstMoment m₁ → FiniteFirstMoment m₂ → bary ϕ m₁ = bary ϕ m₂ → m₁ = m₂

/-- The Hilbert tensor product `H ⊗ K`: the completion of the algebraic tensor product with its
inner product `⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫⟪b, d⟫`. -/
abbrev HTensor (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] := UniformSpace.Completion (H ⊗[ℝ] K)

/-- The tensor embedding `(x, y) ↦ ϕ(x) ⊗ ψ(y)` of `X × Y` (p. 13). -/
noncomputable def tensorEmb (ϕ : X → H) (ψ : Y → K) (p : X × Y) : HTensor H K :=
  ((ϕ p.1 ⊗ₜ[ℝ] ψ p.2 : H ⊗[ℝ] K) : UniformSpace.Completion (H ⊗[ℝ] K))

/-- `β_{ϕ⊗ψ}` is injective on `M^{1,1}(X × Y)`: for finite measures `m₁`, `m₂` on `X × Y` whose
marginals have finite first moment, `β_{ϕ⊗ψ}(m₁) = β_{ϕ⊗ψ}(m₂)` forces `m₁ = m₂`. -/
def TensorBaryInjM11 (ϕ : X → H) (ψ : Y → K) : Prop :=
  ∀ m₁ m₂ : Measure (X × Y), IsFiniteMeasure m₁ → IsFiniteMeasure m₂ →
    FiniteFirstMoment (m₁.map Prod.fst) → FiniteFirstMoment (m₁.map Prod.snd) →
    FiniteFirstMoment (m₂.map Prod.fst) → FiniteFirstMoment (m₂.map Prod.snd) →
    bary (tensorEmb ϕ ψ) m₁ = bary (tensorEmb ϕ ψ) m₂ → m₁ = m₂

/-- `ℓ²(ℕ)`, the target of existential embeddings. -/
abbrev L2N := lp (fun _ : ℕ => ℝ) 2

end DistCov.Indep


