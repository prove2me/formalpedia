-- Prove2me | Definitions.Def_QuantumFunctionalEstimation_Master_Functionals
-- name    : QuantumFunctionalEstimation_Master_Functionals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:28:31.794203+00:00
-- url     : https://prove2.me/theorems/3d7db450-2a08-404c-ae33-1ccef7294276
-- title:
--   Spectral functionals, oscillation, local slopes, and copy cutoff
-- statement:
--   For a real function $\phi$ extending a function on $[0,\infty)$ and a density matrix $\rho$ of dimension $d$, define
--   $$\mathcal L_\phi(\rho)=\frac1d\sum_{i=1}^d\phi(d\lambda_i(\rho)).$$
--   The eigenvalues include zeros with multiplicity. For $I=[a,b]$, define
--   $$M=\sup_{x\in I}|x-1|,\quad A_\phi=\sup_{x,y\in I}|\phi(x)-\phi(y)|,$$
--   $$L_\phi=\sup_{\substack{x,y\in[1/2,4/3]\\x\ne y}}\left|\frac{\phi(x)-\phi(y)}{x-y}\right|,\quad g_\phi=\left|\int\phi\,d\mu_0-\int\phi\,d\mu_1\right|.$$
--   For $c>0$ the copy cutoff is $n_0=\lfloor cd^2/M^2\rfloor$. The goal guards finite suprema with boundedness and positivity and supplies law-relative measurability for the expectations.
--
--   The spectral sum permits arbitrary real-valued functions on the nonnegative half-line, including discontinuous functions. Only the local slope quantity imposes Lipschitz regularity.
--
--   Differences from the source:
--   - encoding: phi on the nonnegative half-line and spectral trace → an arbitrary real extension evaluated in a finite eigenvalue sum; reason: state eigenvalues are nonnegative, so no off-domain value is used
--   - encoding: finite positive A_phi, L_phi and well-defined expectations → real suprema with explicit boundedness guards in the goal and law-relative a.e. measurability; reason: prevents total-function defaults from representing infinite quantities
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), §1.1, printed pp. 1–2 (PDF pp. 3–4); Definition 4.1 and Eq. (17), printed p. 18 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/451.pdf

import Definitions.Def_QuantumFunctionalEstimation_Master_Model
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace QuantumFunctionalEstimation.Master

/-- Spectral sum including zero eigenvalues with multiplicity; no continuity of phi is used.
Only evaluation on density matrices is used, so its arbitrary real extension off [0,infinity) is irrelevant. -/
def spectralFunctional {ι : Type} [Fintype ι] [DecidableEq ι]
    (φ : ℝ → ℝ) (ρ : Matrix ι ι ℂ) : ℝ :=
  (∑ i, φ ((Fintype.card ι : ℝ) * QAlgorithms.ascEigenvalues ρ i)) / Fintype.card ι

/-- Definition 4.1. Nonempty compact interval makes this a genuine finite supremum. -/
def radius (a b : ℝ) : ℝ := sSup ((fun x : ℝ => |x - 1|) '' Set.Icc a b)

/-- The set of oscillation values; boundedness is explicitly required in the goal. -/
def oscillationValues (φ : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {t | ∃ x ∈ Set.Icc a b, ∃ y ∈ Set.Icc a b, t = |φ x - φ y|}

def oscillation (φ : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (oscillationValues φ a b)

/-- The absolute divided differences on exactly [1/2,4/3], excluding the diagonal. -/
def slopeValues (φ : ℝ → ℝ) : Set ℝ :=
  {t | ∃ x ∈ Set.Icc (1 / 2 : ℝ) (4 / 3), ∃ y ∈ Set.Icc (1 / 2 : ℝ) (4 / 3),
    x ≠ y ∧ t = |(φ x - φ y) / (x - y)|}

def localLipschitz (φ : ℝ → ℝ) : ℝ := sSup (slopeValues φ)

/-- Absolute gap, with no preferred orientation of the two laws. -/
def gap (φ : ℝ → ℝ) (μ₀ μ₁ : ProbabilityMeasure ℝ) : ℝ :=
  |(∫ x, φ x ∂(μ₀ : Measure ℝ)) - ∫ x, φ x ∂(μ₁ : Measure ℝ)|

/-- The source's copy cutoff; M is positive as a consequence of the positive gap in the goal. -/
def copyCutoff (c : ℝ) (d : ℕ) (a b : ℝ) : ℕ := ⌊c * (d : ℝ) ^ 2 / radius a b ^ 2⌋₊

end QuantumFunctionalEstimation.Master


