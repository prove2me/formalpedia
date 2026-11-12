-- Prove2me | Definitions.Def_GMMPostSamp_Main_Toolkit
-- name    : GMMPostSamp_Main_Toolkit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:20:30.238901+00:00
-- url     : https://prove2.me/theorems/c5ecfb15-eadf-4870-9511-06eb35a31f59
-- title:
--   Total variation, χ², entropy, variance, covariance, exponential tilts, the Gibbs kernel of a tilt mixture and its Dirichlet form
-- statement:
--   Let $\Omega$ be a measurable space. For probability measures $\mu,\nu$ on $\Omega$ the **total variation distance** is
--   $$\mathrm{TV}(\mu,\nu)=\tfrac12\int_\Omega\Big|\frac{d\mu}{d\rho}-\frac{d\nu}{d\rho}\Big|\,d\rho,\qquad \rho=\mu+\nu,$$
--   the paper's $\tfrac12\int|\pi(\omega)-\mu(\omega)|\,d\omega$ with densities taken against a common dominating measure; on a finite set it is $\tfrac12\sum_a|p(a)-q(a)|$ (`tvFin`). The **$\chi^2$-divergence** is $\chi^2(\rho\|\pi)=\int(\frac{d\rho}{d\pi}-1)^2d\pi$ when $\rho\ll\pi$ and $+\infty$ otherwise; the **KL divergence** is Mathlib's `klDiv` (also possibly $+\infty$). For $f\ge0$ with mean $m=\mathbb E_\mu f$, the **entropy** is $\mathrm{Ent}_\mu[f]=\int (f\log(f/m)-f+m)\,d\mu\in[0,\infty]$, which equals $\mathbb E_\mu[f\log f]-m\log m$ whenever $f\log f$ is integrable; $\mathrm{Var}_\mu$ is the $[0,\infty]$-valued variance and $\mathrm{Cov}_\mu[f,g]=\mathbb E_\mu[fg]-\mathbb E_\mu f\,\mathbb E_\mu g$.
--
--   For a statistic $t:\Omega\to\mathbb R^d$ and $v\in\mathbb R^d$, $Z_t(v)=\int e^{\langle v,t(\omega)\rangle}\pi(d\omega)\in[0,\infty]$ (8) and the **exponential tilt** $T_{v,t}\pi$ has density $e^{\langle v,t\rangle}/Z_t(v)$ with respect to $\pi$ (7). $\mathrm{Cov}_\pi[t]\preceq\beta I_d$ means $\mathrm{Var}_\pi[\langle u,t\rangle]\le\beta\|u\|_2^2$ for all $u$, the bound being a real number (so $\beta\|u\|_2^2\ge0$; a negative bound is not clamped to $0$) (`CovLe`), and the log-MGF condition $\log\mathbb E_\pi[e^{\langle u,t-\mathbb E_\pi t\rangle}]\le\frac\beta2\|u\|_2^2$ for all $u$ is `LogMGFLe`.
--
--   Given a mixing law $\nu$ on $\mathbb R^m$ and a Markov kernel $\kappa$ ($\kappa(w)=\pi_{s(w)}$), the joint law $\tilde\pi=\nu\otimes\kappa$ on $\mathbb R^m\times\Omega$ is (18). The **Gibbs kernel** (19) moves $\omega$ by drawing $w\sim\tilde\pi(\cdot\mid\omega)$ and then $\omega'\sim\kappa(w)$. For a kernel $P$ and a measure $\pi$, the **Dirichlet form** (4) is
--   $$\mathcal E_P(f,g)=\tfrac12\iint(f(\omega)-f(\omega'))(g(\omega)-g(\omega'))\,\pi(d\omega)P(\omega,d\omega').$$
--
--   These are the objects of §2.1–§3.2 used by Lemmas 1–3 and Proposition 3.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. $\tilde\pi(\cdot\mid\omega)$ is Mathlib's `Measure.condKernel` of the swapped joint law, unique up to a null set of the $\Omega$-marginal; none of the statements made about $P$ depends on the version.
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 8 §2.1 (TV, χ², KL, Var, Ent, Cov); p. 9 (4), (7), (8); p. 11 (12)–(13); p. 14 (18)–(19)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-!
# Divergences, exponential tilts, mixtures, the Gibbs kernel and its Dirichlet form

Kumar, Sarkar, Tian, Zhu, *Posterior Sampling in Gaussian Mixture Models Beyond the
Clusterability Threshold*, STOC 2027 submission (manuscript sha256 ba5079cd…), §2.1 (p. 8),
§2.2 (4) (p. 9), §2.3 (7)–(8) (p. 9), §3.2 (12)–(13) (p. 11), (18)–(19) (p. 14).

* `tv μ ν = ½ ∫ |dμ/dρ − dν/dρ| dρ` with the reference measure `ρ = μ + ν` (the paper's
  `½∫|π(ω) − µ(ω)| dω`, densities taken with respect to any common dominating measure).
* `chiSq ρ π = ∫ (dρ/dπ − 1)² dπ` if `ρ ≪ π`, and `∞` otherwise. `KL` is Mathlib's
  `InformationTheory.klDiv` (also `∞` when `ρ` is not absolutely continuous or the log-likelihood
  ratio is not integrable).
* `ent μ f = ∫ (f log(f/m) − f + m) dμ ∈ [0, ∞]`, `m = E_μ f`. For `f > 0` with `f log f`
  integrable this is `E_μ[f log f] − m log m`; the integrand is nonnegative, so `ent` is the
  paper's `Ent_μ[f]` with the value `∞` when `f log f` is not integrable.
* `Var` is Mathlib's `evariance` (`[0, ∞]`-valued), `cov μ f g = E[fg] − E f E g`.
* `tilt π t v = T_{v,t}π` is Mathlib's `Measure.tilted π ⟨v, t(·)⟩`, density
  `exp⟨v, t⟩ / Z_t(v)`; `Zt π t v = Z_t(v) = ∫ exp⟨v, t⟩ dπ` in `[0, ∞]`.
* `CovLe π t β` is `Cov_π[t] ⪯ β I`, written as the quadratic forms
  `Var_π[⟨u, t⟩] ≤ β ‖u‖²` for every `u` (the definition of the Loewner order), with
  `0 ≤ β ‖u‖²` stated so that a negative bound is not clamped to `0` by `ENNReal.ofReal`.
* `LogMGFLe π t β` is `log E_π[exp⟨u, t − E_π t⟩] ≤ (β/2)‖u‖²` for every `u`, written as
  `E_π[exp⟨u, t − E_π t⟩] ≤ exp((β/2)‖u‖²)` (equivalent, `log` being increasing).
* `gibbsKernel ν κ` is the Gibbs kernel (19): from `ω` draw `w ∼ π̃(· | ω)`, then
  `ω' ∼ κ w`, where `π̃ = ν ⊗ κ` is the joint law (18) and `π̃(· | ω)` is Mathlib's
  disintegration (`Measure.condKernel`) of `π̃` with respect to its `Ω`-marginal (unique up to a
  null set of that marginal, which changes none of the statements made about the kernel).
* `dirichletForm π P f g = ½ ∬ (f ω − f ω')(g ω − g ω') π(dω) P(ω, dω')`, (4).
-/

/-- Total variation distance `TV(μ, ν) = ½ ∫ |dμ/dρ − dν/dρ| dρ`, `ρ = μ + ν`. -/
noncomputable def tv {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : ℝ :=
  (1 / 2 : ℝ) * ∫ ω, |(μ.rnDeriv (μ + ν) ω).toReal - (ν.rnDeriv (μ + ν) ω).toReal| ∂(μ + ν)

/-- Total variation distance between two functions on a finite set read as mass functions:
`½ ∑ₐ |p a − q a|`. -/
noncomputable def tvFin {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |p a - q a|

/-- The χ²-divergence `χ²(ρ ‖ π) = ∫ (dρ/dπ − 1)² dπ`, `∞` unless `ρ ≪ π`. -/
noncomputable def chiSq {Ω : Type*} [MeasurableSpace Ω] (ρ π : Measure Ω) : ENNReal :=
  open Classical in
  if ρ ≪ π then ∫⁻ ω, ENNReal.ofReal (((ρ.rnDeriv π ω).toReal - 1) ^ 2) ∂π else ⊤

/-- Entropy `Ent_μ[f] = E_μ[f log f] − E_μ f · log E_μ f` of a nonnegative function, written with
the nonnegative integrand `f log(f/m) − f + m`, `m = E_μ f` (`0 log 0 = 0`); value in `[0, ∞]`. -/
noncomputable def ent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (f ω * Real.log (f ω / ∫ x, f x ∂μ) - f ω + ∫ x, f x ∂μ) ∂μ

/-- Covariance `Cov_μ[f, g] = E_μ[f g] − E_μ[f] E_μ[g]`. -/
noncomputable def cov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  ∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)

/-- The normalizing constant `Z_t(v) = ∫ exp⟨v, t(ω)⟩ π(dω)` (8), in `[0, ∞]`. -/
noncomputable def Zt {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (π : Measure Ω)
    (t : Ω → EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin d)) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (inner ℝ v (t ω))) ∂π

/-- The exponential tilt `T_{v,t}π`, density `∝ exp⟨v, t(ω)⟩` with respect to `π` (7). -/
noncomputable def tilt {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (π : Measure Ω)
    (t : Ω → EuclideanSpace ℝ (Fin d)) (v : EuclideanSpace ℝ (Fin d)) : Measure Ω :=
  π.tilted fun ω => inner ℝ v (t ω)

/-- `Cov_π[t] ⪯ β I_d`: `Var_π[⟨u, t⟩] ≤ β ‖u‖²` for every `u ∈ ℝ^d`, the right-hand side
being a real number (so `0 ≤ β ‖u‖²` is part of the inequality: no clamping of a negative bound
to `0`). -/
def CovLe {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (π : Measure Ω)
    (t : Ω → EuclideanSpace ℝ (Fin d)) (β : ℝ) : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin d), 0 ≤ β * ‖u‖ ^ 2 ∧
    evariance (fun ω => inner ℝ u (t ω)) π ≤ ENNReal.ofReal (β * ‖u‖ ^ 2)

/-- `log E_π[exp⟨u, t − E_π[t]⟩] ≤ (β/2)‖u‖²` for every `u ∈ ℝ^d`, written without the
logarithm: `E_π[exp⟨u, t − E_π t⟩] ≤ exp((β/2)‖u‖²)`. -/
def LogMGFLe {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (π : Measure Ω)
    (t : Ω → EuclideanSpace ℝ (Fin d)) (β : ℝ) : Prop :=
  ∀ u : EuclideanSpace ℝ (Fin d),
    ∫⁻ ω, ENNReal.ofReal (Real.exp (inner ℝ u (t ω - ∫ x, t x ∂π))) ∂π ≤
      ENNReal.ofReal (Real.exp (β / 2 * ‖u‖ ^ 2))

/-- The Gibbs kernel (19) of the joint law `π̃ = ν ⊗ κ` on `ℝ^m × Ω` (18): from `ω`, draw
`w ∼ π̃(· | ω)` (the disintegration of `π̃` along its `Ω`-marginal) and step to `ω' ∼ κ w`. -/
noncomputable def gibbsKernel {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin m))) [IsFiniteMeasure ν]
    (κ : Kernel (EuclideanSpace ℝ (Fin m)) Ω) [IsFiniteKernel κ] : Kernel Ω Ω :=
  κ ∘ₖ ((ν ⊗ₘ κ).map Prod.swap).condKernel

/-- The Dirichlet form (4): `E_P(f, g) = ½ ∬ (f ω − f ω')(g ω − g ω') π(dω) P(ω, dω')`. -/
noncomputable def dirichletForm {Ω : Type*} [MeasurableSpace Ω] (π : Measure Ω)
    (P : Kernel Ω Ω) (f g : Ω → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ p, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(π ⊗ₘ P)

end GMMPostSamp.Main


