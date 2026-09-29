-- Prove2me | Definitions.Def_keating_snaith_cue
-- name    : keating_snaith_cue
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T12:12:41.380032+00:00
-- url     : https://prove2.me/theorems/0157ec18-a59f-400c-96cd-a069cd01454b
-- title:
--   The CUE characteristic polynomial $Z$ and the ensemble average $\langle\cdot\rangle_{CUE(N)}$
-- statement:
--   This item fixes the objects of the mission.
--
--   Let $N \ge 1$ and let $\theta = (\theta_1,\dots,\theta_N)$ be the **eigenphases** of an $N \times N$ unitary matrix, so that its eigenvalues are $e^{i\theta_1},\dots,e^{i\theta_N}$. Under Haar measure on $U(N)$ — equivalently, for the circular unitary ensemble $\mathrm{CUE}(N)$ — Weyl's formula gives the eigenphases the joint density
--
--   $$
--   \frac{1}{(2\pi)^N N!}\prod_{1\le j<k\le N}\bigl|e^{i\theta_j}-e^{i\theta_k}\bigr|^2
--   $$
--
--   on the box $(0,2\pi]^N$. Accordingly the **CUE average** of a function $f$ of the eigenphases is defined by
--
--   $$
--   \langle f\rangle_{\mathrm{CUE}(N)} \;=\; \frac{1}{(2\pi)^N N!}\int_{(0,2\pi]^N} \prod_{1\le j<k\le N}\bigl|e^{i\theta_j}-e^{i\theta_k}\bigr|^2 \, f(\theta)\, d\theta_1\cdots d\theta_N ,
--   $$
--
--   which is a probability average: the average of the constant function $1$ is $1$. The definition is stated for functions with values in any real normed space, so that both real- and complex-valued averages are covered.
--
--   The **characteristic polynomial** evaluated at the point $1$ of the unit circle is
--
--   $$
--   Z(\theta) \;=\; \prod_{n=1}^{N}\bigl(1-e^{i\theta_n}\bigr),
--   $$
--
--   and the two real observables attached to it are $\log|Z|$ and
--
--   $$
--   \operatorname{Im}\log Z \;=\; \sum_{n=1}^{N}\frac{\theta_n-\pi}{2}.
--   $$
--
--   The second is the closed form, valid for eigenphases in $(0,2\pi]$, of the branch of $\operatorname{Im}\log Z$ obtained by continuation from $\log Z(U,\theta-i\epsilon)\to 0$ as $\epsilon\to\infty$; it is the sawtooth sum $-\sum_n\sum_{m\ge1}\sin(m\theta_n)/m$.
--
--   Finally, $\sqrt{\tfrac12\log N}$ is recorded as the standardising scale of the central limit theorem, and
--
--   $$
--   \Phi([a,b]) = \frac{1}{\sqrt{2\pi}}\int_a^b e^{-x^2/2}\,dx
--   $$
--
--   as the standard Gaussian mass of an interval.
--
--   These are the only conventions the mission's theorems rest on: every statement in the mission is an assertion about the average $\langle\cdot\rangle_{\mathrm{CUE}(N)}$ of an explicit function of $Z$.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, pp. 28-29, eq. (2.0.1) and eq. (2.1.1); eq. (2.1.10) and (2.1.12) for the branch of Im log Z; §2.3 eq. (2.3.8) for the standardisation

import Mathlib

/-!
# The CUE characteristic polynomial and its ensemble averages

Basic objects for the Keating–Snaith theory of the characteristic polynomial of a random
unitary matrix, following N.C. Snaith, *Random Matrix Theory and zeta functions*,
PhD thesis, University of Bristol, 2000, Chapter 2.
-/

namespace KeatingSnaith

open Finset MeasureTheory
open scoped Real

/-- The set of eigenphase vectors `(θ₁, …, θ_N) ∈ (0, 2π]^N`. -/
def phaseBox (N : ℕ) : Set (Fin N → ℝ) :=
  Set.univ.pi fun _ => Set.Ioc 0 (2 * Real.pi)

/-- The unnormalised Weyl (CUE) eigenvalue density
`∏_{1 ≤ j < k ≤ N} |e^{iθ_j} - e^{iθ_k}|²`. -/
noncomputable def cueDensity (N : ℕ) (θ : Fin N → ℝ) : ℝ :=
  ∏ p ∈ Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2),
    ‖Complex.exp (θ p.1 * Complex.I) - Complex.exp (θ p.2 * Complex.I)‖ ^ 2

/-- The average of `f` over the circular unitary ensemble `CUE(N)`:
`⟨f⟩ = (N! (2π)^N)⁻¹ ∫_{(0,2π]^N} ∏_{j<k} |e^{iθ_j} - e^{iθ_k}|² f(θ) dθ₁ ⋯ dθ_N`. -/
noncomputable def cueAverage (N : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin N → ℝ) → E) : E :=
  ((Nat.factorial N : ℝ) * (2 * Real.pi) ^ N)⁻¹ • ∫ θ in phaseBox N, cueDensity N θ • f θ

/-- The characteristic polynomial `Z(U, 0) = ∏_{n=1}^{N} (1 - e^{iθ_n})` of a unitary matrix
with eigenphases `θ₁, …, θ_N`. -/
noncomputable def charPoly (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  ∏ n, (1 - Complex.exp (θ n * Complex.I))

/-- `log |Z|`, the real part of `log Z`. -/
noncomputable def logAbsZ (N : ℕ) (θ : Fin N → ℝ) : ℝ :=
  Real.log ‖charPoly N θ‖

/-- `Im log Z = ∑_{n=1}^{N} (θ_n - π)/2`, the branch of the imaginary part of `log Z(U, 0)`
fixed by continuation from `log Z(U, -i∞) = 0`; for eigenphases in `(0, 2π]` it is given by
the sawtooth sum `-∑_n ∑_{m≥1} sin(θ_n m)/m`. -/
noncomputable def imLogZ (N : ℕ) (θ : Fin N → ℝ) : ℝ :=
  ∑ n, (θ n - Real.pi) / 2

/-- The standardising scale `√((1/2) log N)` of the Keating–Snaith central limit theorem. -/
noncomputable def cltScale (N : ℕ) : ℝ :=
  Real.sqrt (Real.log N / 2)

/-- The standard Gaussian measure of the interval `[a, b]`. -/
noncomputable def gaussianMass (a b : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x in a..b, Real.exp (-x ^ 2 / 2)

end KeatingSnaith


