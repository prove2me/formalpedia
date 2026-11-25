-- Prove2me | Definitions.Def_Arxiv1707_02146_Basic
-- name    : Arxiv1707_02146_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T00:15:12.425561+00:00
-- url     : https://prove2.me/theorems/6f674c77-ce0a-416b-818f-ac6c638bcec9
-- title:
--   Broadband transmission matrix, exponential decay, Gaussian envelope and spectral degrees of freedom
-- statement:
--   Objects of the broadband-transmission-matrix model of Mounaix, de Aguiar and Gigan (2017).
--
--   1. **Spectral channels and fields (eq. 1).** The pulse is split into $N_\lambda$ uncorrelated spectral channels $\lambda_1,\dots,\lambda_{N_\lambda}$. At channel $\lambda_i$ the monochromatic transmission matrix $T(\lambda_i)$ maps the field $E^{in}(\lambda_i)\in\mathbb{C}^n$ on the $n$ modulated SLM pixels to the modulated output field $E^{out,M}(\lambda_i)=T(\lambda_i)E^{in}(\lambda_i)\in\mathbb{C}^m$ on the $m$ camera pixels. $E^{out,R}(\lambda_i)\in\mathbb{C}^m$ is the output field produced by the static reference part of the SLM.
--   2. **Broadband intensity (eq. 1).** At camera pixel $x$, the intensity is $I_x=\sum_{i}\big|E^{out,R}_x(\lambda_i)+E^{out,M}_x(\lambda_i)\big|^2$, and the static term is $I_{0,x}=\sum_i\big(|E^{out,R}_x(\lambda_i)|^2+|E^{out,M}_x(\lambda_i)|^2\big)$.
--   3. **Effective TM and BBTM.** $T'(\lambda_i)=\operatorname{diag}\big(\overline{E^{out,R}(\lambda_i)}\big)\,T(\lambda_i)$, i.e. row $x$ of $T(\lambda_i)$ multiplied by $\overline{E^{out,R}_x(\lambda_i)}$, and the Broadband Transmission Matrix is $B=\sum_{i=1}^{N_\lambda}T'(\lambda_i)$.
--   4. **Exponential decay.** A profile $f$ decays with decay time $\tau>0$ if $f(t)=C\,e^{-t/\tau}$ for all $t\ge0$, for some constant $C\neq0$.
--   5. **Traversal time.** $\tau=\kappa/\delta\lambda$ for a spectral correlation bandwidth $\delta\lambda$ and a fixed constant $\kappa$ (the relation $\tau_m\propto1/\delta\lambda_m$).
--   6. **Gaussian envelope.** $G_{A,\lambda_0,w}(\lambda)=A\exp\!\big(-4\ln2\,(\lambda-\lambda_0)^2/w^2\big)$ is the Gaussian centred at $\lambda_0$ with full width at half maximum $w$. A function is a Gaussian of FWHM $w$ centred at $\lambda_0$ if it equals $G_{A,\lambda_0,w}$ for some $A>0$ and $w>0$.
--   7. **Spectral degrees of freedom.** $N_\lambda=\Delta\lambda/\delta\lambda$ for an envelope of width $\Delta\lambda$ and correlation bandwidth $\delta\lambda$.
--
--   **Formalization Note** Fields are complex vectors indexed by $\mathrm{Fin}\,n$ (SLM pixels) and $\mathrm{Fin}\,m$ (camera pixels); spectral channels are indexed by $\mathrm{Fin}\,N_\lambda$. The FWHM is built into the parametrisation of the Gaussian; the statement on the Gaussian cross product also states the half-maximum set explicitly.
-- source:
--   Mounaix, de Aguiar and Gigan, Temporal recompression through a scattering medium via a broadband transmission matrix, arXiv:1707.02146v1 (2017), main text: eq. (1) and following paragraph (PDF p. 2), definition of N_lambda and tau_m proportional to 1/delta_lambda_m (PDF p. 2), time-domain and spectral paragraphs (PDF pp. 3-4)

import Mathlib

/-!
Mounaix, de Aguiar and Gigan, *Temporal recompression through a scattering medium via a broadband
transmission matrix*, arXiv:1707.02146v1 (2017): the broadband intensity model and Broadband
Transmission Matrix of eq. (1) (PDF p. 2), the exponential time-of-flight decay and the relation
`τ ∝ 1/δλ` (PDF pp. 2-3), the Gaussian spectral envelope (PDF pp. 3-4) and the number of spectral
degrees of freedom `N_λ = Δλ/δλ` (PDF p. 2).
-/

open Matrix ComplexConjugate

noncomputable section

namespace Arxiv1707_02146

section BBTM

variable {N m n : ℕ}

/-- Eq. (1), PDF p. 2: the modulated output fields `E^{out,M}(λ_i) = T(λ_i) E^{in}(λ_i)` at the `m`
camera pixels, for `N` spectral channels `λ_1, …, λ_N`, monochromatic transmission matrices
`T(λ_i)` (`m` output pixels × `n` modulated SLM pixels) and input fields `E^{in}(λ_i)` on the
modulated SLM pixels. -/
def modulatedField (T : Fin N → Matrix (Fin m) (Fin n) ℂ) (Ein : Fin N → Fin n → ℂ)
    (i : Fin N) : Fin m → ℂ :=
  T i *ᵥ Ein i

/-- Eq. (1), first line, PDF p. 2: the spectrally unresolved intensity at camera pixel `x`, the
incoherent sum over the `N` spectral channels of `|E^{out,R}(λ_i) + E^{out,M}(λ_i)|²`, where
`ER i x = E^{out,R}(λ_i)` at pixel `x` is the output field of the static reference part. -/
def broadbandIntensity (ER : Fin N → Fin m → ℂ) (T : Fin N → Matrix (Fin m) (Fin n) ℂ)
    (Ein : Fin N → Fin n → ℂ) (x : Fin m) : ℝ :=
  ∑ i, Complex.normSq (ER i x + modulatedField T Ein i x)

/-- Eq. (1), second line, PDF p. 2: the static term `I_0` at pixel `x`, which contains all
field-squared terms `|E^{out,R}(λ_i)|² + |E^{out,M}(λ_i)|²`. -/
def staticTerm (ER : Fin N → Fin m → ℂ) (T : Fin N → Matrix (Fin m) (Fin n) ℂ)
    (Ein : Fin N → Fin n → ℂ) (x : Fin m) : ℝ :=
  ∑ i, (Complex.normSq (ER i x) + Complex.normSq (modulatedField T Ein i x))

/-- Eq. (1), third line, PDF p. 2 (and the monochromatic case `T' = S_ref^* T`, PDF p. 2): the
effective transmission matrix `T'(λ_i) = (E^{out,R}(λ_i))^* T(λ_i)`, i.e. row `x` of `T(λ_i)`
multiplied by the complex conjugate of the reference field at pixel `x`. -/
def effectiveTM (ER : Fin N → Fin m → ℂ) (T : Fin N → Matrix (Fin m) (Fin n) ℂ) (i : Fin N) :
    Matrix (Fin m) (Fin n) ℂ :=
  Matrix.diagonal (fun x => conj (ER i x)) * T i

/-- PDF p. 2, paragraph after eq. (1): the Broadband Transmission Matrix
`B = ∑_{i=1}^{N_λ} T'(λ_i)`. -/
def bbtm (ER : Fin N → Fin m → ℂ) (T : Fin N → Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m) (Fin n) ℂ :=
  ∑ i, effectiveTM ER T i

end BBTM

/-- PDF p. 3: a (time-of-flight) profile `f` decays for `t ≥ 0` in the form `∝ e^{-t/τ}`, with
decay time `τ > 0` and a nonzero proportionality constant. -/
def HasExpDecay (f : ℝ → ℝ) (τ : ℝ) : Prop :=
  0 < τ ∧ ∃ C : ℝ, C ≠ 0 ∧ ∀ t : ℝ, 0 ≤ t → f t = C * Real.exp (-t / τ)

/-- PDF p. 2 (`τ_m ∝ 1/δλ_m`): the traversal time `κ / δλ` attached to a spectral correlation
bandwidth `δλ`, with a fixed proportionality constant `κ`. -/
def traversalTime (κ bw : ℝ) : ℝ := κ / bw

/-- PDF pp. 3-4: the Gaussian spectral profile of amplitude `A`, centred at `l0`, with full width
at half maximum `w`: `A · exp(-4 ln 2 · (λ - l0)² / w²)`. -/
def gaussianProfile (A l0 w : ℝ) (lam : ℝ) : ℝ :=
  A * Real.exp (-(4 * Real.log 2) * (lam - l0) ^ 2 / w ^ 2)

/-- PDF pp. 3-4: `f` is a Gaussian centred at `l0` with FWHM `w > 0` and positive amplitude. -/
def IsGaussianFWHM (f : ℝ → ℝ) (l0 w : ℝ) : Prop :=
  0 < w ∧ ∃ A : ℝ, 0 < A ∧ f = gaussianProfile A l0 w

/-- PDF p. 2: the number of spectral degrees of freedom `N_λ = Δλ / δλ` of a spectral envelope of
width `Δλ` and spectral correlation bandwidth `δλ`. -/
def numSpectralModes (width bw : ℝ) : ℝ := width / bw

end Arxiv1707_02146


