-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Covariance
-- name    : PrivateContinualCounting_Kraft_Supplement_Covariance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:25:39.369883+00:00
-- url     : https://prove2.me/theorems/5c379e49-9487-441e-bb91-cf7b5ec63d1a
-- title:
--   Integer covariance kernels and spectral decompositions
-- statement:
--   A covariance kernel is a function $\Gamma:\mathbb Z\times\mathbb Z\to\mathbb R$. Positive semidefiniteness is the nonnegativity of every finite quadratic form. For a finite integer window $W$, a coordinate $j\in W$ and arbitrary real coefficients $b_i$, the coordinate lower bound is
--   $$\sum_{i,k\in W}b_i\Gamma(i,k)b_k\ge c b_j^2.$$
--   The stationarised-envelope predicate collects symmetry, finite-window positive semidefiniteness, $\Gamma(i+1,k+1)=\Gamma(i,k)$, the coordinate lower bound and
--   $$\sum_{i,k=1}^w\Gamma(a+i,a+k)\le B(w)\quad(a\in\mathbb Z,\ w\ge1).$$
--   These predicates are used as conclusions of stationarisation and as the inherited input of interpolation, never as assumptions defining an additive process.
--
--   A spectral decomposition specifies finite positive measures $\nu,\nu_s$ on the circle and a nonnegative measurable integrable density $f$ such that
--   $$\nu=f\,dm+\nu_s,\quad\nu_s\perp m,\quad\Gamma(i,k)=\int e^{\mathrm i(i-k)\theta}\,d\nu(\theta).$$
--   Here $m$ is the published normalized circle measure on $(-\pi,\pi]$, and $\nu$ is supported there and invariant under circle reflection (the endpoints are identified). The singular part is retained. Positivity almost everywhere and reciprocal integrability of $f$ are not part of the definition: Lemma 4.3 must prove them. This separates the covariance and spectral interfaces from privacy and from any special envelope.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 9, PDF p. 11, Section 4 and Lemmas 4.2–4.3; p. 21, PDF p. 23, Appendix D

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Privacy
import Definitions.Def_PrivateContinualCounting_Kraft_SpectralConstruction

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

abbrev Kernel := ℤ → ℤ → ℝ

def KernelPSD (Γ : Kernel) : Prop :=
  ∀ (W : Finset ℤ) (b : ℤ → ℝ), 0 ≤ ∑ i ∈ W, ∑ k ∈ W, b i * Γ i k * b k

def KernelLowerBound (Γ : Kernel) (c : ℝ) : Prop :=
  ∀ (W : Finset ℤ) (j : ℤ), j ∈ W → ∀ b : ℤ → ℝ,
    c * (b j)^2 ≤ ∑ i ∈ W, ∑ k ∈ W, b i * Γ i k * b k

def StationaryEnvelope (Γ : Kernel) (c : ℝ) (B : ℕ → ℝ) : Prop :=
  (∀ i k, Γ i k = Γ k i) ∧ KernelPSD Γ ∧
  (∀ i k, Γ (i+1) (k+1) = Γ i k) ∧ KernelLowerBound Γ c ∧
  ∀ (a : ℤ) (w : ℕ), 0 < w →
    (∑ i ∈ Finset.range w, ∑ k ∈ Finset.range w,
      Γ (a+(i:ℤ)+1) (a+(k:ℤ)+1)) ≤ B w

/-- Reflection on (-π,π], with the endpoints identified. -/
noncomputable def circleReflect (θ : ℝ) : ℝ := if θ = Real.pi then Real.pi else -θ

/-- Actual Herglotz representation and Lebesgue decomposition; no reciprocal
integrability or positivity is assumed. f is a nonnegative measurable representative. -/
def SpectralDecomposition (Γ : Kernel) (ν νs : Measure ℝ) (f : ℝ → ℝ) : Prop :=
  IsFiniteMeasure ν ∧ IsFiniteMeasure νs ∧
  ν (Set.Ioc (-Real.pi) Real.pi)ᶜ = 0 ∧
  ν.map circleReflect = ν ∧
  Measurable f ∧ (∀ θ, 0 ≤ f θ) ∧ Integrable f circleMeasure ∧
  ν = circleMeasure.withDensity (fun θ => ENNReal.ofReal (f θ)) + νs ∧
  νs.MutuallySingular circleMeasure ∧
  ∀ i k : ℤ, (Γ i k : ℂ) =
    ∫ θ, Complex.exp (((i-k : ℤ) : ℂ) * (θ : ℂ) * Complex.I) ∂ν

end PrivateContinualCounting.Kraft.Supplement


