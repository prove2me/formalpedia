-- Prove2me | Definitions.Def_AlignmentUniformity_Basic
-- name    : AlignmentUniformity_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-23T17:26:00.209097+00:00
-- url     : https://prove2.me/theorems/b6fbe937-2b38-46ad-9a6a-8586b436000a
-- title:
--   Contrastive loss, alignment and uniformity, and Gaussian energies on the hypersphere
-- statement:
--   Objects of Sections 3, 4.1 and 4.2 and Appendix A of Wang and Isola (2020).
--
--   1. **Spaces.** Data live in $\mathbb{R}^n$ and features in $\mathbb{R}^m$, both with the Euclidean norm. $S^{m-1}=\{u\in\mathbb{R}^m:\|u\|_2=1\}$, and $S^d$ is the unit sphere of $\mathbb{R}^{d+1}$.
--   2. **Gaussian potential.** For $t>0$, $G_t(u,v)=e^{-t\|u-v\|_2^2}$.
--   3. **Measures on the sphere.** $\mathcal{M}(S^d)$ is the set of Borel probability measures on $\mathbb{R}^{d+1}$ that give no mass to the complement of $S^d$. $\sigma_d$ is the normalized surface area measure of $S^d$.
--   4. **Energies.** For a kernel $K$ and finite measures $\mu,\nu$: $I_K(\mu,\nu)=\int\!\int K(u,v)\,d\nu(v)\,d\mu(u)$, and $I_K[\mu]=I_K(\mu,\mu)$. The energy of the finite signed measure $\nu_1-\nu_2$ is $I_K(\nu_1,\nu_1)-I_K(\nu_1,\nu_2)-I_K(\nu_2,\nu_1)+I_K(\nu_2,\nu_2)$.
--   5. **Point configurations.** For $u_1,\dots,u_N$, the pairwise potential is $\sum_{1\le i<j\le N}G_t(u_i,u_j)$ and the normalized counting measure is $\frac1N\sum_i\delta_{u_i}$.
--   6. **Weak\* convergence.** $\mu_n\to\mu$ weak\* if $\int f\,d\mu_n\to\int f\,d\mu$ for every continuous $f:\mathbb{R}^k\to\mathbb{R}$.
--   7. **Hypergeometric function (eq. 5).** $_0F_1(;\alpha;z)=\sum_{n\ge0}\frac{z^n}{(\alpha)_n\,n!}$, with $(\alpha)_0=1$ and $(\alpha)_n=\alpha(\alpha+1)\cdots(\alpha+n-1)$.
--   8. **Relaxed problem (eqs. 12-13).** $U_\mu(u)=\int e^{u^\top v/\tau}\,d\mu(v)$, and the objective is $\int\log U_\mu(u)\,d\mu(u)$.
--   9. **Data and positive pairs (Assumption, Section 3).** $p_{\mathrm{data}}$ is a distribution on $\mathbb{R}^n$. $p_{\mathrm{pos}}$ is a distribution on $\mathbb{R}^n\times\mathbb{R}^n$ that is symmetric under $(x,y)\mapsto(y,x)$ and whose first marginal is $p_{\mathrm{data}}$.
--   10. **Encoders.** An encoder is a Borel measurable $f:\mathbb{R}^n\to\mathbb{R}^m$ with $\|f(x)\|_2=1$ for every $x$.
--   11. **Contrastive loss (eq. 1).** For $\tau>0$ and $M$ negatives,
--   $$\mathcal{L}_{\mathsf{contrastive}}(f;\tau,M)=\mathbb{E}_{(x,y)\sim p_{\mathrm{pos}},\ x_i^-\overset{\text{i.i.d.}}{\sim}p_{\mathrm{data}}}\Big[-\log\frac{e^{f(x)^\top f(y)/\tau}}{e^{f(x)^\top f(y)/\tau}+\sum_{i=1}^Me^{f(x_i^-)^\top f(y)/\tau}}\Big].$$
--   12. **The two limit terms (eq. 2).** The alignment term is $-\frac1\tau\mathbb{E}_{(x,y)\sim p_{\mathrm{pos}}}[f(x)^\top f(y)]$. The uniformity term is $\mathbb{E}_{x\sim p_{\mathrm{data}}}\big[\log\mathbb{E}_{x^-\sim p_{\mathrm{data}}}[e^{f(x^-)^\top f(x)/\tau}]\big]$.
--   13. **Alignment and uniformity losses (Section 4.1).** $\mathcal{L}_{\mathsf{align}}(f;\alpha)=\mathbb{E}_{(x,y)\sim p_{\mathrm{pos}}}\|f(x)-f(y)\|_2^\alpha$ and $\mathcal{L}_{\mathsf{uniform}}(f;t)=\log\mathbb{E}_{x,y\overset{\text{i.i.d.}}{\sim}p_{\mathrm{data}}}G_t(f(x),f(y))$.
--   14. **Perfect alignment and uniformity (Section 4.2).** $f$ is perfectly aligned if $f(x)=f(y)$ almost surely over $(x,y)\sim p_{\mathrm{pos}}$. It is perfectly uniform if the law of $f(x)$, $x\sim p_{\mathrm{data}}$, is $\sigma_{m-1}$.
--
--   **Formalization Note** $\mathbb{R}^k$ is `EuclideanSpace ℝ (Fin k)`. Measures on the sphere are measures on the ambient space that are concentrated on the sphere. $\sigma_d$ is Mathlib's `Measure.toSphere` of Lebesgue measure, divided by its total mass and pushed forward to the ambient space. The paper writes $p_{\mathrm{data}}$ and $p_{\mathrm{pos}}$ as densities. Here they are probability measures, which is also how the paper uses them for finite datasets in Section 4.2. A finite signed measure is written as a difference $\nu_1-\nu_2$ of finite measures, and its energy is expanded by bilinearity.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Section 3 (Assumption, eq. (1)), Sections 4.1-4.2 (Definitions of the uniform distribution, weak* convergence, perfect alignment and perfect uniformity; L_align, L_uniform, eq. (2)), Appendix A.1-A.2 (eqs. (4), (5), (12), (13))

import Mathlib

/-!
Wang and Isola, *Understanding Contrastive Representation Learning through Alignment and
Uniformity on the Hypersphere*, ICML 2020, arXiv:2005.10242v10: the data and positive-pair
distributions and the contrastive loss of Section 3, the alignment and uniformity losses, the
Gaussian potential, the uniform distribution on the sphere and weak* convergence of Section 4.1,
perfect alignment and perfect uniformity of Section 4.2, and the energies, the hypergeometric
function `₀F₁` and the relaxed problem of Appendix A.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace AlignmentUniformity

/-- The Euclidean space `ℝ^k`. Data live in `ℝ^n`; features live in `ℝ^m`, on the unit sphere
`S^{m-1}`; the sphere `S^d` of Section 4.1 is the unit sphere of `ℝ^{d+1}`. -/
abbrev Vec (k : ℕ) := EuclideanSpace ℝ (Fin k)

section Sphere

variable {k : ℕ}

/-- Section 4.1.2, p. 4: the Gaussian potential kernel `G_t(u, v) = exp(-t ‖u - v‖₂²)`. -/
def gaussKernel (t : ℝ) (u v : Vec k) : ℝ := Real.exp (-t * ‖u - v‖ ^ 2)

/-- Proposition 1 (Section 4.1.2, p. 5) and Appendix A.1, p. 14: `μ ∈ 𝓜(S^{k-1})`, i.e. `μ` is a
Borel probability measure on the unit sphere, viewed as a Borel probability measure on `ℝ^k`
that gives no mass to the complement of the sphere. -/
def IsSphereProb (μ : Measure (Vec k)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Metric.sphere (0 : Vec k) 1)ᶜ = 0

/-- Definition (Uniform distribution on `S^d`), Section 4.1.2, p. 5: `σ` is the normalized surface
area measure on the unit sphere of `ℝ^k`, pushed forward to `ℝ^k`. The surface area measure is
Mathlib's `Measure.toSphere` of Lebesgue measure, `s ↦ k · vol {r x : 0 < r < 1, x ∈ s}`. -/
def sphereUnif (k : ℕ) : Measure (Vec k) :=
  ((((volume : Measure (Vec k)).toSphere Set.univ)⁻¹ • (volume : Measure (Vec k)).toSphere)).map
    Subtype.val

/-- Appendix A.1, p. 14 (Definition of strict positive definiteness): the energy
`∫∫ K(u, v) dν(v) dμ(u)`. For `μ = ν` this is `I_K[μ]`; for `K = G_t` it is the expected pairwise
Gaussian potential of Proposition 1, eq. (4). -/
def energy (K : Vec k → Vec k → ℝ) (μ ν : Measure (Vec k)) : ℝ :=
  ∫ u, ∫ v, K u v ∂ν ∂μ

/-- Appendix A.1, p. 14 (Definition of strict positive definiteness): the energy `I_K[ν₁ - ν₂]` of
the finite signed measure `ν₁ - ν₂`, expanded by bilinearity. -/
def signedEnergy (K : Vec k → Vec k → ℝ) (ν₁ ν₂ : Measure (Vec k)) : ℝ :=
  energy K ν₁ ν₁ - energy K ν₁ ν₂ - energy K ν₂ ν₁ + energy K ν₂ ν₂

/-- Proposition 2, Section 4.1.2, p. 5: the pairwise potential `∑_{1 ≤ i < j ≤ N} G_t(u_i, u_j)`
of an `N`-point configuration. -/
def pairPotential (t : ℝ) {N : ℕ} (u : Fin N → Vec k) : ℝ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, gaussKernel t (u i) (u j)

/-- Proposition 2, Section 4.1.2, p. 5: the normalized counting measure `(1/N) ∑_i δ_{u_i}` of an
`N`-point configuration. -/
def normCounting {N : ℕ} (u : Fin N → Vec k) : Measure (Vec k) :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (u i)

/-- Definition (Weak* convergence of measures), Section 4.1.2, p. 5: `μ_n → μ` weak* if
`∫ f dμ_n → ∫ f dμ` for every continuous `f : ℝ^k → ℝ`. -/
def WeakStarTendsto (μs : ℕ → Measure (Vec k)) (μ : Measure (Vec k)) : Prop :=
  ∀ f : Vec k → ℝ, Continuous f →
    Tendsto (fun n => ∫ x, f x ∂(μs n)) atTop (𝓝 (∫ x, f x ∂μ))

/-- Appendix A.1, eq. (5), p. 15: the confluent hypergeometric limit function
`₀F₁(; α; z) = ∑_{n ≥ 0} z^n / ((α)_n n!)`, with `(α)_n = α (α + 1) ⋯ (α + n - 1)` the rising
Pochhammer symbol. -/
def hyp0F1 (α z : ℝ) : ℝ :=
  ∑' n : ℕ, z ^ n / ((ascPochhammer ℝ n).eval α * (n.factorial : ℝ))

/-- Appendix A.2, eq. (12), p. 20: `U_μ(u) = ∫ exp(uᵀv / τ) dμ(v)`. -/
def expPotential (τ : ℝ) (μ : Measure (Vec k)) (u : Vec k) : ℝ :=
  ∫ v, Real.exp (inner ℝ u v / τ) ∂μ

/-- Appendix A.2, eq. (13), p. 20: the objective `∫ log U_μ(u) dμ(u)` of the relaxed problem. -/
def relaxedObjective (τ : ℝ) (μ : Measure (Vec k)) : ℝ :=
  ∫ u, Real.log (expPotential τ μ u) ∂μ

end Sphere

section Encoders

variable {n m : ℕ}

/-- Assumption, Section 3, p. 3: `p_pos` is symmetric and its marginal is `p_data`
(`p_pos(x, y) = p_pos(y, x)` and `∫ p_pos(x, y) dy = p_data(x)`), written for distributions. -/
def IsPosPairLaw (pdata : Measure (Vec n)) (ppos : Measure (Vec n × Vec n)) : Prop :=
  ppos.map Prod.swap = ppos ∧ ppos.map Prod.fst = pdata

/-- Section 3, p. 3 and Section 4.2, p. 5: an encoder `f : ℝ^n → S^{m-1}` is a Borel measurable map
whose values are `ℓ₂`-normalized feature vectors. -/
def IsEncoder (f : Vec n → Vec m) : Prop :=
  Measurable f ∧ ∀ x, ‖f x‖ = 1

/-- Eq. (1), Section 3, p. 3: the contrastive loss
`E_{(x,y) ∼ p_pos, x⁻ᵢ ∼ p_data i.i.d.} [-log (e^{f(x)ᵀf(y)/τ} /
(e^{f(x)ᵀf(y)/τ} + ∑_{i=1}^M e^{f(x⁻ᵢ)ᵀf(y)/τ}))]` with `M` negative samples. -/
def contrastiveLoss (pdata : Measure (Vec n)) (ppos : Measure (Vec n × Vec n))
    (f : Vec n → Vec m) (τ : ℝ) (M : ℕ) : ℝ :=
  ∫ w, -Real.log (Real.exp (inner ℝ (f w.1.1) (f w.1.2) / τ) /
      (Real.exp (inner ℝ (f w.1.1) (f w.1.2) / τ) +
        ∑ i, Real.exp (inner ℝ (f (w.2 i)) (f w.1.2) / τ)))
    ∂(ppos.prod (Measure.pi fun _ : Fin M => pdata))

/-- Eq. (2), Theorem 1, Section 4.2, p. 6: the first (alignment) term of the limit,
`-(1/τ) E_{(x,y) ∼ p_pos}[f(x)ᵀ f(y)]`. -/
def alignTerm (ppos : Measure (Vec n × Vec n)) (f : Vec n → Vec m) (τ : ℝ) : ℝ :=
  -(1 / τ) * ∫ z, inner ℝ (f z.1) (f z.2) ∂ppos

/-- Eq. (2), Theorem 1, Section 4.2, p. 6: the second (uniformity) term of the limit,
`E_{x ∼ p_data}[log E_{x⁻ ∼ p_data}[e^{f(x⁻)ᵀ f(x)/τ}]]`. -/
def uniformTerm (pdata : Measure (Vec n)) (f : Vec n → Vec m) (τ : ℝ) : ℝ :=
  ∫ x, Real.log (∫ x', Real.exp (inner ℝ (f x') (f x) / τ) ∂pdata) ∂pdata

/-- Section 4.1.1, p. 4: the alignment loss `L_align(f; α) = E_{(x,y) ∼ p_pos} ‖f(x) - f(y)‖₂^α`,
`α > 0`. -/
def alignLoss (ppos : Measure (Vec n × Vec n)) (f : Vec n → Vec m) (α : ℝ) : ℝ :=
  ∫ z, ‖f z.1 - f z.2‖ ^ α ∂ppos

/-- Section 4.1.2, p. 4: the uniformity loss
`L_uniform(f; t) = log E_{x, y ∼ p_data i.i.d.}[G_t(f(x), f(y))]`, `t > 0`. -/
def uniformLoss (pdata : Measure (Vec n)) (f : Vec n → Vec m) (t : ℝ) : ℝ :=
  Real.log (∫ x, ∫ y, gaussKernel t (f x) (f y) ∂pdata ∂pdata)

/-- Definition (Perfect Alignment), Section 4.2, p. 6: `f(x) = f(y)` almost surely over
`(x, y) ∼ p_pos`. -/
def PerfectlyAligned (ppos : Measure (Vec n × Vec n)) (f : Vec n → Vec m) : Prop :=
  ∀ᵐ z ∂ppos, f z.1 = f z.2

/-- Definition (Perfect Uniformity), Section 4.2, p. 6: the distribution of `f(x)`, `x ∼ p_data`,
is the uniform distribution `σ_{m-1}` on `S^{m-1}`. -/
def PerfectlyUniform (pdata : Measure (Vec n)) (f : Vec n → Vec m) : Prop :=
  pdata.map f = sphereUnif m

end Encoders

end AlignmentUniformity


