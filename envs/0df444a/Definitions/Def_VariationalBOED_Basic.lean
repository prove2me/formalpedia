-- Prove2me | Definitions.Def_VariationalBOED_Basic
-- name    : VariationalBOED_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T15:50:32.15069+00:00
-- url     : https://prove2.me/theorems/f2548d30-7622-4ff1-a4d2-3db081bcbf66
-- title:
--   Bayesian model, expected information gain and variational EIG bounds
-- statement:
--   Objects of Sections 2-4 and Appendices A-B of Foster et al. (2019). Everything is for one fixed design $d$, which is not written.
--
--   1. **Densities.** The parameter $\theta$ ranges over a measurable space $\Theta$ and the outcome $y$ over a measurable space $\mathcal Y$, carrying $\sigma$-finite reference measures $\nu_\Theta$ and $\nu_{\mathcal Y}$ (for instance Lebesgue or counting measure). A probability density is a measurable $f\ge0$ with $\int f\,d\nu=1$; a conditional density $f(b\mid a)$ is jointly measurable and a probability density in $b$ for every $a$. $\mathbb P_f$ denotes the measure with density $f$, and $H[f]=-\int f\log f\,d\nu$ is the (differential) entropy.
--   2. **Model (Section 2).** A prior density $p(\theta)$ and a likelihood $p(y\mid\theta,d)$. The marginal is $p(y\mid d)=\int p(\theta)p(y\mid\theta,d)\,d\nu_\Theta(\theta)$, the posterior is $p(\theta\mid y,d)=p(\theta)p(y\mid\theta,d)/p(y\mid d)$, and the joint law of $(\theta,y)$ has density $p(y,\theta\mid d)=p(\theta)p(y\mid\theta,d)$.
--   3. **Expected information gain (eq. 3).** $\mathrm{EIG}(d)=\mathbb E_{p(y,\theta\mid d)}\big[\log\frac{p(y\mid\theta,d)}{p(y\mid d)}\big]$.
--   4. **Validity (Appendix A.1).** An approximation is valid when it is a (conditional) density with the same support as the density it approximates: $q_p(\theta\mid y,d)>0\iff p(\theta\mid y,d)>0$ for every $y$ with $p(y\mid d)>0$; $q_m(y\mid d)>0\iff p(y\mid d)>0$; $q_\ell(y\mid\theta,d)>0\iff p(y\mid\theta,d)>0$. A valid VNMC proposal $q_v$ is a valid posterior approximation such that, for every $y$ with $p(y\mid d)>0$, the weight $p(y,\theta\mid d)/q_v(\theta\mid y,d)$ is bounded in $\theta$ (the assumption used in the proof of Lemma 1).
--   5. **Bounds and estimates (Section 3).**
--      - $\mathcal L_{\mathrm{post}}(d)=\mathbb E_{p(y,\theta\mid d)}\big[\log\frac{q_p(\theta\mid y,d)}{p(\theta)}\big]$ (eq. 6);
--      - $\mathcal U_{\mathrm{marg}}(d)=\mathbb E_{p(y,\theta\mid d)}\big[\log\frac{p(y\mid\theta,d)}{q_m(y\mid d)}\big]$ (eq. 9);
--      - $\mathcal U_{\mathrm{VNMC}}(d,L)=\mathbb E\big[\log p(y\mid\theta_0,d)-\log\frac1L\sum_{\ell=1}^L\frac{p(y,\theta_\ell\mid d)}{q_v(\theta_\ell\mid y,d)}\big]$ with $(\theta_0,y,\theta_{1:L})\sim p(y,\theta_0\mid d)\prod_{\ell=1}^Lq_v(\theta_\ell\mid y,d)$ (eq. 10);
--      - $\mathcal I_{m+\ell}(d)=\mathbb E_{p(y,\theta\mid d)}\big[\log\frac{q_\ell(y\mid\theta,d)}{q_m(y\mid d)}\big]$ (eq. 12).
--   6. **Lemma 1 (3).** For fixed $y$, the product law $\prod_{\ell=1}^Lq_v(\theta_\ell\mid y,d)$ and the mixture $P(\theta_{1:L}\mid y,d)=\frac1L\sum_{\ell=1}^Lp(\theta_\ell\mid y,d)\prod_{k\ne\ell}q_v(\theta_k\mid y,d)$ on $\Theta^L$.
--   7. **Monte Carlo (Theorem 1).** For samples $X_1,X_2,\dots$ and $f:\mathcal X\times\Phi\to\mathbb R$: $\hat\mu_N(\phi)=\frac1N\sum_{n=1}^Nf(X_n,\phi)$ and $\mu(\phi)=\mathbb E[f(X_1,\phi)]$.
--
--   **Formalization Note** Densities are real-valued, and every expectation is a Bochner integral. Lean gives a non-integrable integrand the integral $0$, so each statement assumes outright that the expectations it uses are finite. $\log0=0$ in Lean, but the support conditions make every logarithm that matters have a positive argument almost surely. The design $d$ is fixed and suppressed. The samples $X_n$ are indexed from $0$.
-- source:
--   Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, Variational Bayesian Optimal Experimental Design, arXiv:1903.05480v3 (NeurIPS 2019), Section 2 (eq. 3), Section 3 (eqs. 6, 9, 10, 12), Section 4 (Theorem 1), Appendix A.1-A.4

import Mathlib

/-!
Foster, Jankowiak, Bingham, Horsfall, Teh, Rainforth and Goodman, *Variational Bayesian Optimal
Experimental Design*, arXiv:1903.05480v3 (NeurIPS 2019): the Bayesian model and the expected
information gain of Section 2 (eq. (3)), the variational bounds and estimates `L_post`, `U_marg`,
`U_VNMC`, `I_{m+ℓ}` of Section 3 (eqs. (6), (9), (10), (12)) with the validity conventions of
Appendix A, and the Monte Carlo estimator of Theorem 1 (Section 4).

Conventions. All quantities are for one fixed design `d`, which is suppressed from the notation.
The parameter `θ` lives in a measurable space `Th` and the outcome `y` in a measurable space `Y`;
all densities (`p(θ)`, `p(y|θ,d)`, and the variational densities) are real-valued densities with
respect to fixed reference measures `nuT` on `Th` and `nuY` on `Y` (for instance Lebesgue or
counting measure). A conditional density of `θ` given `y` is a function `Y → Th → ℝ`; a
conditional density of `y` given `θ` is a function `Th → Y → ℝ`.
-/

open MeasureTheory

noncomputable section

namespace VariationalBOED

section Densities

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Section 2: `f` is a probability density with respect to the reference measure `ν`:
measurable, nonnegative, and of total integral `1`. -/
def IsProbDensity (ν : Measure α) (f : α → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ ∫ x, f x ∂ν = 1

/-- Section 2: `f a ·` is a probability density with respect to `ν` for every `a`, and
`(a, b) ↦ f a b` is jointly measurable (a conditional density such as `p(y|θ,d)`). -/
def IsCondDensity (ν : Measure β) (f : α → β → ℝ) : Prop :=
  Measurable (Function.uncurry f) ∧ (∀ a b, 0 ≤ f a b) ∧ ∀ a, ∫ b, f a b ∂ν = 1

/-- The measure with density `f` with respect to `ν`, i.e. the distribution written `f(x)` in the
paper (Sections 2-3). -/
def densMeasure (ν : Measure α) (f : α → ℝ) : Measure α :=
  ν.withDensity (fun x => ENNReal.ofReal (f x))

/-- Lemma 2 and Appendix A.4: the (differential) entropy `H[f] = -E_f[log f]` of a density `f`
with respect to `ν`. -/
def diffEntropy (ν : Measure α) (f : α → ℝ) : ℝ :=
  -∫ x, f x * Real.log (f x) ∂ν

end Densities

section Model

variable {Th Y : Type*} [MeasurableSpace Th] [MeasurableSpace Y]

/-- Section 2: a Bayesian model `p(θ) p(y|θ,d)`: a prior density `p` on `Th` and a likelihood
`lik θ y = p(y|θ,d)` that is a probability density in `y` for every `θ`. -/
def IsModel (nuT : Measure Th) (nuY : Measure Y) (p : Th → ℝ) (lik : Th → Y → ℝ) : Prop :=
  IsProbDensity nuT p ∧ IsCondDensity nuY lik

/-- Section 2: the marginal density `p(y|d) = E_{p(θ)}[p(y|θ,d)]`. -/
def marginal (nuT : Measure Th) (p : Th → ℝ) (lik : Th → Y → ℝ) (y : Y) : ℝ :=
  ∫ θ, p θ * lik θ y ∂nuT

/-- Section 2, eq. (3): the posterior density `p(θ|y,d) = p(θ) p(y|θ,d) / p(y|d)` (meaningful
where `p(y|d) > 0`). -/
def posterior (nuT : Measure Th) (p : Th → ℝ) (lik : Th → Y → ℝ) (y : Y) (θ : Th) : ℝ :=
  p θ * lik θ y / marginal nuT p lik y

/-- Section 2: the joint distribution `p(y,θ|d) = p(θ) p(y|θ,d)` of `(θ, y)`. -/
def jointLaw (nuT : Measure Th) (nuY : Measure Y) (p : Th → ℝ) (lik : Th → Y → ℝ) :
    Measure (Th × Y) :=
  densMeasure (nuT.prod nuY) (fun z => p z.1 * lik z.1 z.2)

/-- Section 2: the marginal distribution `p(y|d)` of the outcome. -/
def marginalLaw (nuT : Measure Th) (nuY : Measure Y) (p : Th → ℝ) (lik : Th → Y → ℝ) :
    Measure Y :=
  densMeasure nuY (marginal nuT p lik)

/-- Eq. (3): the integrand `log (p(y|θ,d) / p(y|d))` of the expected information gain. -/
def eigIntegrand (nuT : Measure Th) (p : Th → ℝ) (lik : Th → Y → ℝ) (z : Th × Y) : ℝ :=
  Real.log (lik z.1 z.2 / marginal nuT p lik z.2)

/-- Eq. (3): the expected information gain
`EIG(d) = E_{p(y,θ|d)}[log (p(y|θ,d) / p(y|d))]`. -/
def eig (nuT : Measure Th) (nuY : Measure Y) (p : Th → ℝ) (lik : Th → Y → ℝ) : ℝ :=
  ∫ z, eigIntegrand nuT p lik z ∂jointLaw nuT nuY p lik

/-- Appendix A.1: a valid posterior approximation `q(θ|y,d)`: a conditional density of `θ` given
`y` with the same support as the posterior `p(θ|y,d)` at every `y` with `p(y|d) > 0`. -/
def IsValidPosteriorApprox (nuT : Measure Th) (p : Th → ℝ) (lik : Th → Y → ℝ)
    (q : Y → Th → ℝ) : Prop :=
  IsCondDensity nuT q ∧
    ∀ y, 0 < marginal nuT p lik y → ∀ θ, (0 < q y θ ↔ 0 < posterior nuT p lik y θ)

/-- Eq. (6): the integrand `log (q_p(θ|y,d) / p(θ))` of the variational posterior bound. -/
def postIntegrand (p : Th → ℝ) (q : Y → Th → ℝ) (z : Th × Y) : ℝ :=
  Real.log (q z.2 z.1 / p z.1)

/-- Eq. (6): the variational posterior bound
`L_post(d) = E_{p(y,θ|d)}[log (q_p(θ|y,d) / p(θ))]`. -/
def postBound (nuT : Measure Th) (nuY : Measure Y) (p : Th → ℝ) (lik : Th → Y → ℝ)
    (q : Y → Th → ℝ) : ℝ :=
  ∫ z, postIntegrand p q z ∂jointLaw nuT nuY p lik

/-- Appendix A.2 (with the validity convention of Appendix A.1): a valid marginal approximation
`q_m(y|d)`: a probability density on `Y` with the same support as `p(y|d)`. -/
def IsValidMarginalApprox (nuT : Measure Th) (nuY : Measure Y) (p : Th → ℝ)
    (lik : Th → Y → ℝ) (qm : Y → ℝ) : Prop :=
  IsProbDensity nuY qm ∧ ∀ y, (0 < qm y ↔ 0 < marginal nuT p lik y)

/-- Eq. (9): the integrand `log (p(y|θ,d) / q_m(y|d))` of the variational marginal bound. -/
def margIntegrand (lik : Th → Y → ℝ) (qm : Y → ℝ) (z : Th × Y) : ℝ :=
  Real.log (lik z.1 z.2 / qm z.2)

/-- Eq. (9): the variational marginal bound
`U_marg(d) = E_{p(y,θ|d)}[log (p(y|θ,d) / q_m(y|d))]`. -/
def margBound (nuT : Measure Th) (nuY : Measure Y) (p : Th → ℝ) (lik : Th → Y → ℝ)
    (qm : Y → ℝ) : ℝ :=
  ∫ z, margIntegrand lik qm z ∂jointLaw nuT nuY p lik

/-- Lemma 1 with its proof in Appendix A.3: a valid VNMC proposal `q_v(θ|y,d)`: a valid posterior
approximation (Appendix A.1) such that, at every `y` with `p(y|d) > 0`, the importance weight
`p(y,θ|d) / q_v(θ|y,d)` is bounded in `θ` (the assumption invoked in the proof in Appendix A.3). -/
def IsValidVNMCProposal (nuT : Measure Th) (p : Th → ℝ) (lik : Th → Y → ℝ)
    (qv : Y → Th → ℝ) : Prop :=
  IsValidPosteriorApprox nuT p lik qv ∧
    ∀ y, 0 < marginal nuT p lik y → ∃ B : ℝ, ∀ θ, p θ * lik θ y / qv y θ ≤ B

/-- Eq. (10): the sampling distribution of `(θ₀, y, θ_{1:L})`, namely
`p(y, θ₀|d) ∏_{ℓ=1}^L q_v(θ_ℓ|y,d)`. -/
def vnmcLaw (nuT : Measure Th) [SigmaFinite nuT] (nuY : Measure Y) (p : Th → ℝ)
    (lik : Th → Y → ℝ) (qv : Y → Th → ℝ) (L : ℕ) : Measure ((Th × Y) × (Fin L → Th)) :=
  densMeasure ((nuT.prod nuY).prod (Measure.pi fun _ : Fin L => nuT))
    (fun x => p x.1.1 * lik x.1.1 x.1.2 * ∏ i, qv x.1.2 (x.2 i))

/-- Eq. (10): the integrand
`log p(y|θ₀,d) - log ((1/L) ∑_{ℓ=1}^L p(y,θ_ℓ|d) / q_v(θ_ℓ|y,d))` of the VNMC bound. -/
def vnmcIntegrand (p : Th → ℝ) (lik : Th → Y → ℝ) (qv : Y → Th → ℝ) (L : ℕ)
    (x : (Th × Y) × (Fin L → Th)) : ℝ :=
  Real.log (lik x.1.1 x.1.2) -
    Real.log ((1 / (L : ℝ)) * ∑ i, p (x.2 i) * lik (x.2 i) x.1.2 / qv x.1.2 (x.2 i))

/-- Eq. (10): the variational nested Monte Carlo bound `U_VNMC(d, L)`. -/
def vnmcBound (nuT : Measure Th) [SigmaFinite nuT] (nuY : Measure Y) (p : Th → ℝ)
    (lik : Th → Y → ℝ) (qv : Y → Th → ℝ) (L : ℕ) : ℝ :=
  ∫ x, vnmcIntegrand p lik qv L x ∂vnmcLaw nuT nuY p lik qv L

/-- Lemma 1 (3): the distribution `∏_{ℓ=1}^L q_v(θ_ℓ|y,d)` of `L` independent proposal draws. -/
def vnmcProposalProd (nuT : Measure Th) [SigmaFinite nuT] (qv : Y → Th → ℝ) (L : ℕ) (y : Y) :
    Measure (Fin L → Th) :=
  densMeasure (Measure.pi fun _ : Fin L => nuT) (fun θs => ∏ i, qv y (θs i))

/-- Lemma 1 (3): the mixture
`(1/L) ∑_{ℓ=1}^L p(θ_ℓ|y,d) ∏_{k ≠ ℓ} q_v(θ_k|y,d)` on `L`-tuples of parameters. -/
def vnmcMixture (nuT : Measure Th) [SigmaFinite nuT] (p : Th → ℝ) (lik : Th → Y → ℝ)
    (qv : Y → Th → ℝ) (L : ℕ) (y : Y) : Measure (Fin L → Th) :=
  densMeasure (Measure.pi fun _ : Fin L => nuT)
    (fun θs => (1 / (L : ℝ)) *
      ∑ l, posterior nuT p lik y (θs l) * ∏ k ∈ Finset.univ.erase l, qv y (θs k))

/-- Section 3 (implicit likelihood, eq. (12)) with the validity convention of Appendix A.1: a valid
likelihood approximation `q_ℓ(y|θ,d)`: a conditional density of `y` given `θ` with the same
support as `p(y|θ,d)`. -/
def IsValidLikelihoodApprox (nuY : Measure Y) (lik : Th → Y → ℝ) (ql : Th → Y → ℝ) : Prop :=
  IsCondDensity nuY ql ∧ ∀ θ y, (0 < ql θ y ↔ 0 < lik θ y)

/-- Eq. (12): the integrand `log (q_ℓ(y|θ,d) / q_m(y|d))` of the marginal + likelihood
estimate. -/
def mlIntegrand (qm : Y → ℝ) (ql : Th → Y → ℝ) (z : Th × Y) : ℝ :=
  Real.log (ql z.1 z.2 / qm z.2)

/-- Eq. (12): the marginal + likelihood approximation
`I_{m+ℓ}(d) = E_{p(y,θ|d)}[log (q_ℓ(y|θ,d) / q_m(y|d))]`. -/
def mlEstimate (nuT : Measure Th) (nuY : Measure Y) (p : Th → ℝ) (lik : Th → Y → ℝ)
    (qm : Y → ℝ) (ql : Th → Y → ℝ) : ℝ :=
  ∫ z, mlIntegrand qm ql z ∂jointLaw nuT nuY p lik

end Model

section MonteCarlo

variable {Ω S E : Type*} [MeasurableSpace Ω]

/-- Theorem 1: the Monte Carlo estimator `μ̂_N(φ) = (1/N) ∑_{n=1}^N f(X_n, φ)` (the samples
`X_1, X_2, …` are indexed from `0` here). -/
def mcEstimate (f : S → E → ℝ) (X : ℕ → Ω → S) (N : ℕ) (φ : E) (ω : Ω) : ℝ :=
  (1 / (N : ℝ)) * ∑ n ∈ Finset.range N, f (X n ω) φ

/-- Theorem 1: the target `μ(φ) = E[f(X_1, φ)]` of the Monte Carlo estimator. -/
def mcMean (P : Measure Ω) (f : S → E → ℝ) (X : ℕ → Ω → S) (φ : E) : ℝ :=
  ∫ ω, f (X 0 ω) φ ∂P

end MonteCarlo

end VariationalBOED


