-- Prove2me | Definitions.Def_PureDPQR_alg2Law
-- name    : PureDPQR_alg2Law
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:50.125264+00:00
-- url     : https://prove2.me/theorems/c9f104e4-73d1-442a-b397-5329630cf1af
-- title:
--   Algorithm 2: parameters (6.1)–(6.2), internal transcript law $Q_h$ and output law
-- statement:
--   **Algorithm 2** takes $h\in H_{N,d}$, a public query table $Q=\{q_i\}_{i\in[k]}$, $0<\varepsilon\le1$ and $0<\beta<\frac12$. It forms the signed list ($K=2k$), sets
--
--   $$\ell=\log K,\quad \pi=\frac{\beta}{32d},\quad A=\log\frac4\pi=\log\frac{128d}{\beta},\quad T=\Big\lceil\frac{N\varepsilon}{\ell}\Big\rceil,\quad \kappa=\frac\varepsilon8,\quad \lambda=\frac{\varepsilon}{8\sqrt{2AT}},\quad \rho=\min\Big\{\frac12,\sqrt{\frac AT}\Big\},$$
--
--   draws $Z_j=B_jL_j$ with independent $B_j\sim\mathrm{Bernoulli}(\pi)$, $L_j\sim\mathrm{Lap}(\kappa)$, runs $y\leftarrow\mathrm{SelectMW}(h+Z)$ and returns $\hat p=D(y)$. Its internal transcript has law $Q_h(y)=\mathbb E_Z[p_{h+Z}(y)]$ on $[K]^T$, and its output has law $\sum_yQ_h(y)\,\delta_{D(y)}$ on $\mathbb R^d$.
--
--   These two laws are the objects of Propositions 22, 23 and Theorem 2.
--
--   **Formalization Note** $Z_j=B_jL_j$ has law $(1-\pi)\delta_0+\pi\mathrm{Lap}(\kappa)$, the coordinate law of the sparse perturbation. $T$ is `Nat.ceil`. The parameters are total functions of $(N,d,k,\varepsilon,\beta)$; theorems state the ranges of Theorem 2, under which every logarithm, root and quotient has a positive argument. The transcript space is finite and discrete; the output space $\mathbb R^d$ carries the Borel σ-algebra.
-- source:
--   Zou, Pure Differentially Private Query Release via Laplace Input Smoothing, arXiv:2611.04721 (held version, sha256 69b70d59…), Algorithm 2 with (6.1)–(6.2), p.25 (PDF p.26)

import Mathlib
import Definitions.Def_PureDPQR_errQ
import Definitions.Def_PureDPQR_transcriptProb
import Definitions.Def_PureDPQR_smoothed

open MeasureTheory

namespace PureDPQR

/-!
# Algorithm 2: parameters, internal transcript law and output law

Z. Zou, *Pure Differentially Private Query Release via Laplace Input Smoothing*, arXiv:2611.04721
(held version, sha256 69b70d59…), Algorithm 2 with (6.1)–(6.2), p.25 (PDF p.26).

Algorithm 2 takes `h ∈ H_{N,d}`, a public query table `Q = {q_i}_{i∈[k]}`, `0 < ε ≤ 1` and
`0 < β < 1/2`. It sets `K = 2k`, the signed list, and

`ℓ = log K, π = β/(32d), A = log(4/π) = log(128d/β), T = ⌈Nε/ℓ⌉, κ = ε/8, λ = ε/(8√(2AT))` (6.1),
`ρ = min{1/2, √(A/T)}` (6.2);

draws `Z_j = B_j L_j` with independent `B_j ∼ Bernoulli(π)`, `L_j ∼ Lap(κ)`, runs
`y ← SelectMW(h + Z)` and returns `p̂ = D(y)`.

**Formalization Note.**
* `Z_j = B_j L_j` has law `(1 − π) δ₀ + π Lap(κ)`, the coordinate law of `sparseLaplace`, so the
  transcript of Algorithm 2 has law `Q_h(y) = E_Z[p_{h+Z}(y)]` (`smoothed`, (4.3)), and the output
  `p̂ = D(y)` has law `∑_y Q_h(y) δ_{D(y)}` (`alg2Law`).
* `T = ⌈Nε/ℓ⌉` is `Nat.ceil`. All parameters are total functions of `N, d, k, ε, β`; theorems
  state the ranges of Theorem 2, under which every logarithm, square root and quotient here has a
  positive argument.
* The transcript space `Fin T → Fin (2k)` is finite with the discrete σ-algebra, so every set of
  transcripts is a measurable event. The output space `Fin d → ℝ` carries the Borel σ-algebra.
-/

/-- `ℓ = log K = log(2k)` (6.1). -/
noncomputable def ellParam (k : ℕ) : ℝ := Real.log (2 * (k : ℝ))

/-- `π = β/(32d)` (6.1). -/
noncomputable def pertParam (d : ℕ) (β : ℝ) : ℝ := β / (32 * (d : ℝ))

/-- `A = log(4/π) = log(128d/β)` (6.1). -/
noncomputable def AParam (d : ℕ) (β : ℝ) : ℝ := Real.log (4 / pertParam d β)

/-- `T = ⌈Nε/ℓ⌉` (6.1). -/
noncomputable def TParam (N k : ℕ) (ε : ℝ) : ℕ := ⌈(N : ℝ) * ε / ellParam k⌉₊

/-- `κ = ε/8` (6.1). -/
noncomputable def kappaParam (ε : ℝ) : ℝ := ε / 8

/-- `λ = ε/(8√(2AT))` (6.1). -/
noncomputable def lamParam (N d k : ℕ) (ε β : ℝ) : ℝ :=
  ε / (8 * Real.sqrt (2 * AParam d β * (TParam N k ε : ℝ)))

/-- `ρ = min{1/2, √(A/T)}` (6.2). -/
noncomputable def rhoParam (N d k : ℕ) (ε β : ℝ) : ℝ :=
  min (1 / 2) (Real.sqrt (AParam d β / (TParam N k ε : ℝ)))

/-- The internal transcript probability of Algorithm 2 on the histogram `h`:
`Q_h(y) = E_Z[p_{h+Z}(y)]`, where `p_v` is the transcript law of `SelectMW(v)` with the parameters
(6.1)–(6.2) and the signed list of `Q`, and `Z` is the sparse Laplace perturbation with
`π = β/(32d)`, `κ = ε/8`. -/
noncomputable def smoothedTranscript (N d k : ℕ) (ε β : ℝ) (Q : Fin k → Fin d → ℝ)
    (h : Fin d → ℕ) (y : Fin (TParam N k ε) → Fin (2 * k)) : ℝ :=
  smoothed (fun v y' => transcriptProb N (lamParam N d k ε β) (rhoParam N d k ε β) (signed Q) v y')
    (pertParam d β) (kappaParam ε) (fun j => (h j : ℝ)) y

/-- The law of the internal transcript `y` of Algorithm 2 on `h`: `∑_y Q_h(y) δ_y` on the finite
transcript space `[K]^T`. -/
noncomputable def transcriptLaw (N d k : ℕ) (ε β : ℝ) (Q : Fin k → Fin d → ℝ) (h : Fin d → ℕ) :
    Measure (Fin (TParam N k ε) → Fin (2 * k)) :=
  ∑ y, ENNReal.ofReal (smoothedTranscript N d k ε β Q h y) • Measure.dirac y

/-- The output law of Algorithm 2 on `h`: the law of `p̂ = D(y)`, `∑_y Q_h(y) δ_{D(y)}` on `ℝ^d`. -/
noncomputable def alg2Law (N d k : ℕ) (ε β : ℝ) (Q : Fin k → Fin d → ℝ) (h : Fin d → ℕ) :
    Measure (Fin d → ℝ) :=
  ∑ y, ENNReal.ofReal (smoothedTranscript N d k ε β Q h y) •
    Measure.dirac (decoder (rhoParam N d k ε β) (signed Q) y)

end PureDPQR


