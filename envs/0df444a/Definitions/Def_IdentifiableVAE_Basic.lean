-- Prove2me | Definitions.Def_IdentifiableVAE_Basic
-- name    : IdentifiableVAE_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T06:56:58.770351+00:00
-- url     : https://prove2.me/theorems/729b2349-75ec-4b1c-a955-9b2c5be7f8f1
-- title:
--   Conditionally factorial exponential-family latent model, observed law and the relations $\sim$, $\sim_A$, $\sim_P$
-- statement:
--   Objects of Sections 3.1 and 4 of Khemakhem, Kingma, Monti and Hyvärinen (AISTATS 2020).
--
--   1. **Parameters.** A parameter $\theta=(f,Q,T,\lambda)$ consists of a mixing function $f:\mathbb{R}^n\to\mathbb{R}^d$, base measures $Q_i:\mathbb{R}\to\mathbb{R}$, sufficient statistics $T_{i,j}:\mathbb{R}\to\mathbb{R}$ and natural parameters $\lambda_{i,j}:\mathbb{R}^m\to\mathbb{R}$, for $1\le i\le n$ and $1\le j\le k$. The paper writes $\theta=(f,T,\lambda)$.
--   2. **Prior (eq. 7).** $Z_i(u)=\int_{\mathbb{R}}Q_i(t)\exp\big(\sum_jT_{i,j}(t)\lambda_{i,j}(u)\big)\,dt$ and $p_{T,\lambda}(z\mid u)=\prod_{i=1}^n\frac{Q_i(z_i)}{Z_i(u)}\exp\big(\sum_{j=1}^kT_{i,j}(z_i)\lambda_{i,j}(u)\big)$. The prior law of $z$ given $u$ is Lebesgue measure on $\mathbb{R}^n$ with this density.
--   3. **Observations (eqs. 5, 6).** $x=f(z)+\varepsilon$, where the noise $\varepsilon\sim P_\varepsilon$ is independent of $z$. The conditional law $p_\theta(x\mid u)$ is the convolution of the push-forward of the prior by $f$ with $P_\varepsilon$.
--   4. **Admissible parameters.** Let $U\subset\mathbb{R}^m$ be the support of $u$. Then $\theta$ describes a model on $U$ if $f$ is measurable and injective, every $Q_i$ is measurable and positive, every $T_{i,j}$ is measurable, and every factor of the prior is integrable, so that $Z_i(u)<\infty$ for every $u\in U$.
--   5. **Relations (Definition 2, eq. 13).** Write $\mathbf T(z)=(T_{1,1}(z_1),\dots,T_{n,k}(z_n))\in\mathbb{R}^{nk}$. Then $\theta\sim\tilde\theta$ if there are an $nk\times nk$ matrix $A$ and $c\in\mathbb{R}^{nk}$ such that for every $z$ there is $\tilde z$ with $\tilde f(\tilde z)=f(z)$ and $\mathbf T(z)=A\tilde{\mathbf T}(\tilde z)+c$. This is $\mathbf T(f^{-1}(x))=A\tilde{\mathbf T}(\tilde f^{-1}(x))+c$ for all $x\in f(\mathbb{R}^n)$. The relation $\sim_A$ requires $A$ invertible. The relation $\sim_P$ requires $A$ invertible and block-permutation: for some permutation $\sigma$, the rows of block $i$ vanish outside the columns of block $\sigma(i)$. The almost-everywhere versions of $\sim,\sim_A,\sim_P$ ask the same for Lebesgue-almost every $z$ only.
--   6. **Identifiability (Definition 1).** $\theta$ is identifiable up to a relation $R$ within a class $\Theta$ if every $\tilde\theta\in\Theta$ with $p_\theta(\cdot\mid u)=p_{\tilde\theta}(\cdot\mid u)$ for all $u\in U$ satisfies $\theta\mathrel R\tilde\theta$.
--   7. **Assumptions.**
--      - (i): $\{\omega\in\mathbb{R}^d:\varphi_\varepsilon(\omega)=0\}$ is Lebesgue-null, where $\varphi_\varepsilon$ is the characteristic function of the noise.
--      - (iii): each $T_{i,j}$ is differentiable almost everywhere, and no nonzero $\alpha\in\mathbb{R}^k$ makes $\sum_j\alpha_jT_{i,j}$ constant on a set of positive measure.
--      - (iv), eq. (14): there are distinct $u^0,\dots,u^{nk}\in U$ such that $L=(\lambda(u^1)-\lambda(u^0),\dots,\lambda(u^{nk})-\lambda(u^0))$ is invertible.
--      - (2.i): each $T_{i,j}$ is twice differentiable.
--      - (2.ii): $f$ has all first partial derivatives and all second cross derivatives $\partial^2f/\partial z_s\partial z_t$, $s\ne t$.
--      - (3.i): no $T_{i,1}$ is strictly increasing or strictly decreasing.
--      - (3.ii): all partial derivatives of $f$ exist and are continuous.
--      - Proof of Theorem 3: $f$ is a $C^1$ embedding with injective differential at every point. A function $g:\mathbb{R}\to\mathbb{R}$ has isolated turning points if every $t$ has a punctured neighbourhood on each side of which $g$ is strictly monotonic.
--
--   **Formalization Note** The latent domain is $\mathbb{R}^n$, the default domain of Appendix A. Observations live in `EuclideanSpace ℝ (Fin d)` so that Mathlib's characteristic function applies. The base measures $Q_i$ are part of the parameter because the proofs let $\tilde Q_i$ differ from $Q_i$. Assumption (iii) is read as linear independence of $T_{i,1},\dots,T_{i,k}$ together with the constant function, on subsets of the latent coordinate line. The almost-everywhere relations are what the proofs establish.
-- source:
--   Khemakhem, Kingma, Monti and Hyvärinen, Variational Autoencoders and Nonlinear ICA: A Unifying Framework, AISTATS 2020, arXiv:1907.04809v4, Section 3.1 eqs. (5)-(7), Section 4 Notations, Definitions 1-2 eqs. (12)-(14), Theorems 1-3 assumptions, pp. 4-6; Appendix B.2 eqs. (20)-(24), p. 13

import Mathlib

/-!
Khemakhem, Kingma, Monti and Hyvärinen, *Variational Autoencoders and Nonlinear ICA: A Unifying
Framework*, AISTATS 2020, arXiv:1907.04809v4: the conditional generative model (5)-(7) of
Section 3.1, its observed conditional law, the assumptions of Theorems 1-3 and 6, identifiability
up to an equivalence relation (Definition 1) and the relations `∼`, `∼_A`, `∼_P` of Definition 2
(Section 4.1).

Latent vectors are `z : Fin n → ℝ` (the latent domain is `ℝⁿ`, the default domain of
Appendix A), observations live in `EuclideanSpace ℝ (Fin d)`, auxiliary variables are
`u : Fin m → ℝ`, and the vector of sufficient statistics is indexed by `Fin n × Fin k`.
-/

open MeasureTheory

noncomputable section

namespace IdentifiableVAE

/-- Section 3.1, eqs. (5)-(7), and Section 4 "Notations": the parameters of the conditional
generative model `p_θ(x, z | u) = p_f(x | z) p_{T,λ}(z | u)`: the mixing function
`f : ℝⁿ → ℝᵈ`, the base measures `Q_i`, the sufficient statistics `T_{i,j}` and the natural
parameters `λ_{i,j}(u)`. The paper writes `θ = (f, T, λ)`; the base measures `Q_i` of eq. (7)
are carried with the parameter because the proofs (eq. (29)) allow `Q̃_i ≠ Q_i`. -/
structure Param (n d m k : ℕ) where
  /-- The mixing function `f` of eq. (6). -/
  f : (Fin n → ℝ) → EuclideanSpace ℝ (Fin d)
  /-- The base measures `Q_i` of eq. (7). -/
  Q : Fin n → ℝ → ℝ
  /-- The sufficient statistics `T_{i,j}` of eq. (7). -/
  T : Fin n → Fin k → ℝ → ℝ
  /-- The natural parameters `λ_{i,j}(u)` of eq. (7). -/
  lam : (Fin m → ℝ) → Fin n → Fin k → ℝ

variable {n d m k : ℕ}

/-- Eq. (7): the exponent `∑_j T_{i,j}(t) λ_{i,j}(u)` of the `i`-th latent factor. -/
def expoTerm (θ : Param n d m k) (u : Fin m → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  ∑ j, θ.T i j t * θ.lam u i j

/-- Eq. (7): the unnormalised `i`-th factor `Q_i(t) exp(∑_j T_{i,j}(t) λ_{i,j}(u))`. -/
def unnormFactor (θ : Param n d m k) (u : Fin m → ℝ) (i : Fin n) (t : ℝ) : ℝ :=
  θ.Q i t * Real.exp (expoTerm θ u i t)

/-- Eq. (7): the normalising constant `Z_i(u) = ∫ Q_i(t) exp(∑_j T_{i,j}(t) λ_{i,j}(u)) dt`. -/
def normConst (θ : Param n d m k) (u : Fin m → ℝ) (i : Fin n) : ℝ :=
  ∫ t, unnormFactor θ u i t

/-- Eq. (7): the conditionally factorial exponential-family prior density
`p_{T,λ}(z | u) = ∏_i Q_i(z_i) / Z_i(u) · exp(∑_j T_{i,j}(z_i) λ_{i,j}(u))`. -/
def priorDensity (θ : Param n d m k) (u : Fin m → ℝ) (z : Fin n → ℝ) : ℝ :=
  ∏ i, unnormFactor θ u i (z i) / normConst θ u i

/-- Eq. (7): the prior law of `z` given `u`, i.e. Lebesgue measure on `ℝⁿ` with density
`p_{T,λ}(z | u)`. -/
def priorMeasure (θ : Param n d m k) (u : Fin m → ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity fun z => ENNReal.ofReal (priorDensity θ u z)

/-- Eqs. (5), (6), (21) and (24): the conditional law `p_θ(x | u)` of the observation
`x = f(z) + ε`, with `z ∼ p_{T,λ}(· | u)` and the noise `ε ∼ P_ε` independent of `z`: the
convolution of the push-forward of the prior by `f` with the noise law. -/
def obsLaw (Pε : Measure (EuclideanSpace ℝ (Fin d))) (θ : Param n d m k) (u : Fin m → ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  Measure.conv ((priorMeasure θ u).map θ.f) Pε

/-- Section 3.1 and Section 4 "Notations": `θ` describes a model (5)-(7) when the auxiliary
variable ranges over its support `U`: `f` is measurable and injective, each `Q_i` is measurable
and positive (the proofs take `log Q_i` in eq. (29)), each `T_{i,j}` is measurable, and every
factor of eq. (7) is integrable, so that `Z_i(u)` is finite for every `u ∈ U`. -/
structure IsParam (θ : Param n d m k) (U : Set (Fin m → ℝ)) : Prop where
  measurable_f : Measurable θ.f
  injective_f : Function.Injective θ.f
  measurable_Q : ∀ i, Measurable (θ.Q i)
  pos_Q : ∀ i t, 0 < θ.Q i t
  measurable_T : ∀ i j, Measurable (θ.T i j)
  integrable_factor : ∀ u ∈ U, ∀ i, Integrable (unnormFactor θ u i)

/-- Section 4 "Notations": the vector of sufficient statistics
`T(z) = (T_{1,1}(z_1), …, T_{n,k}(z_n)) ∈ ℝ^{nk}`, indexed by `Fin n × Fin k`. -/
def suffStat (θ : Param n d m k) (z : Fin n → ℝ) : Fin n × Fin k → ℝ :=
  fun p => θ.T p.1 p.2 (z p.1)

/-- Definition 2, eq. (13): `T(f⁻¹(x)) = A T̃(f̃⁻¹(x)) + c` for every `x ∈ X = f(ℝⁿ)`,
written over `z = f⁻¹(x)`: for every latent `z` there is `z̃ = f̃⁻¹(f(z))` with
`T(z) = A T̃(z̃) + c`. -/
def LinRel (θ θ' : Param n d m k) (A : Matrix (Fin n × Fin k) (Fin n × Fin k) ℝ)
    (c : Fin n × Fin k → ℝ) : Prop :=
  ∀ z, ∃ z', θ'.f z' = θ.f z ∧ suffStat θ z = A.mulVec (suffStat θ' z') + c

/-- The almost-everywhere form of eq. (13), which is what the proofs of Theorems 1-3 and 6 in
Appendices B and E establish: for Lebesgue-almost every latent `z` there is `z̃ = f̃⁻¹(f(z))`
with `T(z) = A T̃(z̃) + c`. -/
def LinRelAE (θ θ' : Param n d m k) (A : Matrix (Fin n × Fin k) (Fin n × Fin k) ℝ)
    (c : Fin n × Fin k → ℝ) : Prop :=
  ∀ᵐ z ∂(volume : Measure (Fin n → ℝ)), ∃ z', θ'.f z' = θ.f z ∧
    suffStat θ z = A.mulVec (suffStat θ' z') + c

/-- Definition 2, footnote 4: `A` is a block permutation matrix, i.e. there is a permutation
`σ` of `{1, …, n}` such that the block of rows of `T_i` only has nonzero entries in the block of
columns of `T̃_{σ(i)}`. -/
def IsBlockPerm (A : Matrix (Fin n × Fin k) (Fin n × Fin k) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i l a b, a ≠ σ i → A (i, l) (a, b) = 0

/-- Definition 2, eq. (13): the relation `∼` (an arbitrary `nk × nk` matrix `A`). -/
def Sim (θ θ' : Param n d m k) : Prop :=
  ∃ A c, LinRel θ θ' A c

/-- Definition 2: the relation `∼_A` (eq. (13) with `A` invertible). -/
def SimA (θ θ' : Param n d m k) : Prop :=
  ∃ A c, IsUnit A ∧ LinRel θ θ' A c

/-- Definition 2: the relation `∼_P` (eq. (13) with `A` an invertible block permutation
matrix). -/
def SimP (θ θ' : Param n d m k) : Prop :=
  ∃ A c, IsUnit A ∧ IsBlockPerm A ∧ LinRel θ θ' A c

/-- The relation `∼` of Definition 2 in the almost-everywhere form established by the proofs. -/
def SimAE (θ θ' : Param n d m k) : Prop :=
  ∃ A c, LinRelAE θ θ' A c

/-- The relation `∼_A` of Definition 2 in the almost-everywhere form established by the
proofs. -/
def SimAAE (θ θ' : Param n d m k) : Prop :=
  ∃ A c, IsUnit A ∧ LinRelAE θ θ' A c

/-- The relation `∼_P` of Definition 2 in the almost-everywhere form established by the
proofs. -/
def SimPAE (θ θ' : Param n d m k) : Prop :=
  ∃ A c, IsUnit A ∧ IsBlockPerm A ∧ LinRelAE θ θ' A c

/-- Definition 1, eq. (12), for one parameter: `θ` is identifiable up to `rel` within the
parameter class `Θ` if every `θ̃ ∈ Θ` with the same observed conditional laws
`p_θ(x | u) = p_θ̃(x | u)` for all `u ∈ U` is related to `θ`. -/
def IdentifiableUpTo (Pε : Measure (EuclideanSpace ℝ (Fin d))) (U : Set (Fin m → ℝ))
    (Θ : Set (Param n d m k)) (rel : Param n d m k → Param n d m k → Prop)
    (θ : Param n d m k) : Prop :=
  ∀ θ' ∈ Θ, (∀ u ∈ U, obsLaw Pε θ u = obsLaw Pε θ' u) → rel θ θ'

/-- Theorem 1, assumption (i): the zero set `{ω | φ_ε(ω) = 0}` of the characteristic function
of the noise has Lebesgue measure zero. -/
def CharFunZeroNull (Pε : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  volume {ω : EuclideanSpace ℝ (Fin d) | charFun Pε ω = 0} = 0

/-- Theorem 1, assumption (iii): every `T_{i,j}` is differentiable almost everywhere, and for
every `i` the statistics `T_{i,1}, …, T_{i,k}` are linearly independent, together with the
constants, on every subset of `ℝ` of positive measure: no nonzero `α` makes
`∑_j α_j T_{i,j}` constant on such a set. -/
def SuffStatRegular (θ : Param n d m k) : Prop :=
  (∀ i j, ∀ᵐ t ∂(volume : Measure ℝ), DifferentiableAt ℝ (θ.T i j) t) ∧
    ∀ i (S : Set ℝ), 0 < volume S → ∀ (α : Fin k → ℝ) (α₀ : ℝ),
      (∀ t ∈ S, ∑ j, α j * θ.T i j t = α₀) → α = 0

/-- Theorem 1, assumption (iv), eq. (14): there are `nk + 1` distinct points
`u⁰, …, u^{nk}` of `U` such that the `nk × nk` matrix
`L = (λ(u¹) - λ(u⁰), …, λ(u^{nk}) - λ(u⁰))` is invertible. The points `u¹, …, u^{nk}` are
indexed by `Fin n × Fin k`, and so are the columns of `L`. -/
def HasInvertibleL (θ : Param n d m k) (U : Set (Fin m → ℝ)) : Prop :=
  ∃ (u₀ : Fin m → ℝ) (u : Fin n × Fin k → Fin m → ℝ), u₀ ∈ U ∧ (∀ p, u p ∈ U) ∧
    Function.Injective u ∧ (∀ p, u p ≠ u₀) ∧
    (Matrix.of fun r p : Fin n × Fin k => θ.lam (u p) r.1 r.2 - θ.lam u₀ r.1 r.2).det ≠ 0

/-- Theorem 2, assumption (2.i): every sufficient statistic `T_{i,j}` is twice
differentiable. -/
def TwiceDiffStats (θ : Param n d m k) : Prop :=
  ∀ i j, Differentiable ℝ (θ.T i j) ∧ Differentiable ℝ (deriv (θ.T i j))

/-- Theorem 2, assumption (2.ii): the mixing function `f` has all first partial derivatives
and all second-order cross derivatives `∂²f / ∂z_s ∂z_t`, `s ≠ t`, at every point. -/
def HasSecondCrossPartials (f : (Fin n → ℝ) → EuclideanSpace ℝ (Fin d)) : Prop :=
  (∀ t z, LineDifferentiableAt ℝ f z (Pi.single t 1)) ∧
    ∀ s t z, s ≠ t →
      LineDifferentiableAt ℝ (fun w => lineDeriv ℝ f w (Pi.single t 1)) z (Pi.single s 1)

/-- Theorem 3, assumption (3.ii): all partial derivatives `∂f / ∂z_t` of the mixing function
exist everywhere and are continuous. -/
def HasContinuousPartials (f : (Fin n → ℝ) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ t, (∀ z, LineDifferentiableAt ℝ f z (Pi.single t 1)) ∧
    Continuous fun z => lineDeriv ℝ f z (Pi.single t 1)

/-- Theorem 3, assumption (3.i) with footnote 5: no sufficient statistic `T_{i,1}` is monotonic,
where monotonic means strictly increasing or strictly decreasing. -/
def NotMonotoneStats (θ : Param n d m 1) : Prop :=
  ∀ i, ¬ StrictMono (θ.T i 0) ∧ ¬ StrictAnti (θ.T i 0)

/-- Proof of Theorem 3 (Appendix B.4: "by hypothesis, `v_i` is of class `C¹`, and its Jacobian
is non-zero everywhere"): `f` is a `C¹` embedding with injective differential. For two such
mixing functions with the same image, `f̃⁻¹ ∘ f` is a `C¹` diffeomorphism of `ℝⁿ`. -/
def IsC1Embedding (f : (Fin n → ℝ) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ContDiff ℝ 1 f ∧ Topology.IsEmbedding f ∧ ∀ z, Function.Injective (fderiv ℝ f z)

/-- Proof of Theorem 3 (Appendix B.4: "we can choose `U` such that `T_i` has only one minimum"):
the turning points of `g` are isolated, i.e. every `t` has a punctured neighbourhood on each side
of which `g` is strictly monotone. -/
def IsolatedTurningPoints (g : ℝ → ℝ) : Prop :=
  ∀ t, ∃ δ > 0,
    (StrictMonoOn g (Set.Ioo (t - δ) t) ∨ StrictAntiOn g (Set.Ioo (t - δ) t)) ∧
    (StrictMonoOn g (Set.Ioo t (t + δ)) ∨ StrictAntiOn g (Set.Ioo t (t + δ)))

end IdentifiableVAE


