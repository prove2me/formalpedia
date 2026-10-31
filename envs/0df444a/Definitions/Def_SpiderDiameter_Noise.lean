-- Prove2me | Definitions.Def_SpiderDiameter_Noise
-- name    : SpiderDiameter_Noise
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:08.52728+00:00
-- url     : https://prove2.me/theorems/85ce0a15-25ae-49a4-a320-831c577deec9
-- title:
--   Driving noise of the spider: Brownian motion $B$ and i.i.d. uniform ray indices $\theta_m$
-- statement:
--   Fix an integer $n$ (the number of rays) and a probability space $(\Omega,\mathcal F,P)$. The rays are $R_k=\{e^{2\pi i k/n}t: t\ge 0\}\subset\mathbb C$, $k=1,\dots,n$.
--
--   The spider process is driven by two independent sources of randomness:
--
--   1. a standard real Brownian motion $B=(B_t)_{t\ge0}$, taken in its continuous version: every path $t\mapsto B_t(\omega)$ is continuous with $B_0(\omega)=0$, and each $B_t$ is measurable;
--   2. a sequence $\theta=(\theta_m)_{m\ge0}$ of independent "complex signs", each uniformly distributed over the $n$ rays: $P(\theta_m=k)=1/n$ for every ray $k$.
--
--   The path of $B$ is independent of the whole sequence $\theta$.
--
--   These are the data from which the spider process $S$, its ribs and its diameter are built, and on which the general-start process $(X,Y,Z)$ of Section 3 is realized.
--
--   **Formalization Note** Ray $k$ of the paper is the index $k-1\in\{0,\dots,n-1\}$ (`Fin n`), and the complex sign $e^{2\pi ik/n}$ is recorded by its ray index. Mathlib's `IsBrownianReal` gives almost surely continuous paths; the structure additionally requires every path to be continuous and to start at $0$, i.e. it fixes the standard continuous version.
-- source:
--   Bednarz–Ernst–Osękowski, On the Diameter of the Stopped Spider Process, arXiv:2105.15202v2, §1, p.1 (rays R_k, complex signs θ, Brownian motion B independent of θ)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpiderDiameter

/-- **Direction of the `k`-th ray.**
Bednarz–Ernst–Osękowski, *On the Diameter of the Stopped Spider Process*, arXiv:2105.15202v2,
§1, p.1: the rays are `R_k = {e^{2πik/n} t : t ≥ 0}`, `k = 1, …, n`.

**Formalization Note.** Rays are indexed from `0`: index `k` is the paper's ray `k + 1`, with
direction `e^{2πi(k+1)/n}`. The index is a natural number so that the general-start process of
§3 can name two fixed rays `0` and `1`; only indices `k < n` are used. -/
noncomputable def rayDir (n : ℕ) (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ) + 1) / n)

/-- **The randomness driving the spider process.**
Bednarz–Ernst–Osękowski, arXiv:2105.15202v2, §1, p.1: "Let θ = (θ_m)_{m≥0} be the sequence of
independent 'complex signs', i.e., the family of random variables with the uniform distribution
on {e^{2πik/n} : k = 1, 2, …, n}. Assume further that B = (B_t)_{t≥0} is a Brownian motion
independent of θ".

Fields: `B` a standard real Brownian motion (`IsBrownianReal`, which includes `B₀ = 0` a.s.);
`θ m` the ray index of the `m`-th excursion, uniform on the `n` rays; the `θ m` are independent,
and the path of `B` is independent of the sequence `θ`.

**Formalization Note.** (1) The paper's Brownian motion (Revuz–Yor, which it cites for the
excursion process) has continuous paths starting at `0`; Mathlib's `IsBrownianReal` gives a.s.
continuity only, so the continuous version is chosen: every path is continuous and starts at
`0`, and each `B t` is measurable. Every Brownian motion has such a version. (2) The complex sign
`e^{2πik/n}` is recorded by its ray index `θ m : Fin n` (index `k` ↔ the paper's `k + 1`, see
`rayDir`); uniformity is `P(θ m = k) = 1/n` for every `k`. (3) Independence of `B` and `θ` is
independence of the path `ω ↦ (t ↦ B t ω)` and the sequence `ω ↦ (m ↦ θ m ω)`, as random
elements of the product spaces. -/
structure SpiderNoise (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The driving Brownian motion `B`. -/
  B : ℝ≥0 → Ω → ℝ
  /-- The ray index of the `m`-th excursion (the paper's complex sign `θ_m`). -/
  θ : ℕ → Ω → Fin n
  brownian : IsBrownianReal B P
  measurable_B : ∀ t, Measurable (B t)
  continuous_B : ∀ ω, Continuous (fun t => B t ω)
  zero_B : ∀ ω, B 0 ω = 0
  measurable_θ : ∀ m, Measurable (θ m)
  iIndep_θ : iIndepFun θ P
  uniform_θ : ∀ m (k : Fin n), P (θ m ⁻¹' {k}) = (n : ℝ≥0∞)⁻¹
  indep_B_θ : IndepFun (fun ω t => B t ω) (fun ω m => θ m ω) P

end SpiderDiameter


