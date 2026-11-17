-- Prove2me | Definitions.Def_PFRelease_Supplement_gaussMech
-- name    : PFRelease_Supplement_gaussMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:42:27.568469+00:00
-- url     : https://prove2.me/theorems/5e70680a-26a2-4523-b341-5dded639ca1a
-- title:
--   Gaussian mechanism $\mathcal N_\sigma(g)$, its privacy profile $\delta_{\mathcal N_\sigma}(\varepsilon)$, and per-instance sensitivity bounds
-- statement:
--   Let $\Phi$ be the standard Gaussian CDF. The **privacy profile** of the Gaussian mechanism with standard deviation $\sigma$ is
--   $$
--   \delta_{\mathcal N_\sigma}(\varepsilon):=\Phi\Big(\frac1{2\sigma}-\varepsilon\sigma\Big)-e^{\varepsilon}\,\Phi\Big(-\frac1{2\sigma}-\varepsilon\sigma\Big).
--   $$
--
--   For a real-valued function $g$ on datasets, the **Gaussian mechanism** $\mathcal N_\sigma(g)$ outputs $g(s)+N(0,\sigma^2)$ on input $s$: its law is the Gaussian with mean $g(s)$ and variance $\sigma^2$.
--
--   A function $\Delta:\mathcal X^*\times\mathcal X\to[0,\infty]$ **bounds the per-instance sensitivity** of $g$ (a real-valued function on nonempty datasets) if
--   $$
--   |g(s)-g(s^{i\to\perp})|\le\Delta(s^{i\to\perp},s_i)
--   $$
--   for every $n\ge1$, every $s\in\mathcal X^n$ and every slot $i\in[n]$ with $s_i\neq\perp$.
--
--   These objects describe the scalar releases of PFR: when the score $1/(|s|\Delta(s,x))$ is large on every admitted neighbouring pair, Gaussian noise calibrated to $1/(\tau n)$ is private on those pairs.
--
--   **Formalization Note** $\Phi$ is Mathlib's `cdf (gaussianReal 0 1)`. `gaussMech g σ s` is `gaussianReal (g s) (σ²)` (Mathlib takes the variance); a dataset of $n$ slots enters $g$ as the list of its records. The left side of the sensitivity bound is embedded in $[0,\infty]$; the bound quantifies over every dataset size $n\ge1$, as in Definition D.1.
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), §2, p.7 (PDF p.9); Fact A.2, p.27 (PDF p.29); Definition D.1, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_PFRelease_Dataset

open MeasureTheory ProbabilityTheory

namespace PFRelease.Supplement

/-- The standard Gaussian CDF `Φ(x) = Pr[N(0, 1) ≤ x]` (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release:
Scaling Noise to Typical Sensitivity via Private Filtering*, arXiv:2610.40654, held version sha256 e1d516b3…,
§2, p.7 = PDF p.9, and Fact A.2, p.27).

**Formalization Note** `Φ` is Mathlib's `cdf` of the standard real Gaussian `gaussianReal 0 1`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The privacy profile of the Gaussian mechanism (§2, p.7 = PDF p.9; Fact A.2, p.27):
`δ_{N_σ}(ε) := Φ(1/(2σ) − εσ) − e^ε Φ(−1/(2σ) − εσ)`. -/
noncomputable def gaussProfile (σ ε : ℝ) : ℝ :=
  stdNormalCDF (1 / (2 * σ) - ε * σ) - Real.exp ε * stdNormalCDF (-1 / (2 * σ) - ε * σ)

/-- The Gaussian noise-addition mechanism `N_σ(g)` (§2, p.7 = PDF p.9; Fact A.2, p.27): on a dataset `s`
of `n` records it outputs `g(s) + N(0, σ²)`, i.e. its law is the Gaussian with mean `g(s)` and
variance `σ²`.

**Formalization Note** `g` is a real-valued function on datasets in `X* = List (Option X)`; a dataset
of `n` slots enters through `toList`. Mathlib's `gaussianReal μ v` takes the variance `v ∈ ℝ≥0`,
here `σ²`, so `σ` is the standard deviation (for `σ = 0` the law is the point mass at `g(s)`). -/
noncomputable def gaussMech {X : Type*} {n : ℕ} (g : List (Option X) → ℝ) (σ : ℝ)
    (s : Fin n → Option X) : Measure ℝ :=
  gaussianReal (g (toList s)) (Real.toNNReal (σ ^ 2))

/-- A function `Δ : X* × X → [0, ∞]` bounds the per-instance sensitivity of a real-valued function
`g` on nonempty datasets (Definition D.1, p.39 = PDF p.41) if `|g(s) − g(s^{i→⊥})| ≤ Δ(s^{i→⊥}, sᵢ)`
for every `n ≥ 1`, every `s ∈ Xⁿ` and every slot `i` with `sᵢ ≠ ⊥`.

**Formalization Note** The quantifier over `n ≥ 1` is explicit (it ranges over every dataset size,
not only the size of a later theorem). The left side is embedded in `[0, ∞]` by `ENNReal.ofReal`.
`g` is total on `List (Option X)`; its value on the empty list is never used. -/
def IsPerInstanceBound {X : Type*} (g : List (Option X) → ℝ)
    (Δ : List (Option X) → Option X → ENNReal) : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (s : Fin m → Option X) (i : Fin m), s i ≠ none →
    ENNReal.ofReal |g (toList s) - g (toList (nullOut s {i}))| ≤
      Δ (toList (nullOut s {i})) (s i)

end PFRelease.Supplement


