-- Prove2me | Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
-- name    : StochApproxDyn_MartingaleNoise_AssumptionA1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:10:30.358978+00:00
-- url     : https://prove2.me/theorems/5ce4ed3e-fb93-4739-b7b9-6a02ec2a7648
-- title:
--   Assumption A1 and the noise deviation $\Delta(t,T)$, Eq. (10)
-- statement:
--   Let $\{\gamma_n\}$ be a step sequence with times $\tau_n$ and inverse $m(t)$, and let $\{U_n\}_{n\ge1}$ be a sequence in $\mathbb R^d$ with piecewise constant process $\bar U$ (see the definition of the interpolation for Section 4.1).
--
--   **Assumption A1** asks that for every $T>0$
--   $$\lim_{n\to\infty}\ \sup\Big\{\Big\|\sum_{i=n}^{k-1}\gamma_{i+1}U_{i+1}\Big\| :\ k=n+1,\dots,m(\tau_n+T)\Big\}=0 .$$
--   The paper states the equivalent form $\lim_{t\to\infty}\Delta(t,T)=0$ for every $T>0$, where
--   $$\Delta(t,T)=\sup_{0\le h\le T}\Big\|\int_t^{t+h}\bar U(s)\,ds\Big\|. \tag{10}$$
--   This file defines the supremum in the first form, the predicate A1 in that form, the quantity $\Delta(t,T)$, and the predicate "$\Delta(t,T)\to0$ as $t\to\infty$ for every $T>0$".
--
--   A1 says that the accumulated noise over any time window of fixed length $T$ becomes negligible as the window moves to infinity; it is the noise hypothesis of Benaïm's Proposition 4.1, under which the interpolated process is an asymptotic pseudotrajectory of the flow of $F$.
--
--   **Formalization Note** Both suprema are taken in $[0,\infty]$. The range $k=n+1,\dots,m(\tau_n+T)$ is finite and may be empty (when $\gamma_{n+1}>T$); the supremum of the empty range is $0$. $\int_t^{t+h}$ is the interval (Bochner) integral; $\bar U$ takes finitely many values on any bounded interval of $[0,\infty)$ under the step-sequence assumptions, so the integral is a genuine one.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.1, p. 12 (PDF p. 13), Proposition 4.1, assumption A1 and Eq. (10)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation

namespace StochApproxDyn.MartingaleNoise

open Filter Topology
open scoped ENNReal

/-- The quantity inside assumption A1 (Benaïm 1999, §4.1, p. 12):
`sup { ‖∑_{i=n}^{k-1} γ_{i+1} U_{i+1}‖ : k = n+1, …, m(τ_n + T) }`,
valued in `[0, ∞]`. The range of `k` is finite; when it is empty (`m(τ_n + T) ≤ n`) the
supremum is `0`. -/
noncomputable def a1Sup {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (T : ℝ) : ℝ≥0∞ :=
  (Finset.Ioc n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T))).sup fun k =>
    ‖∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1)‖ₑ

/-- Assumption A1 (§4.1, p. 12), first form: for all `T > 0`,
`lim_{n→∞} sup { ‖∑_{i=n}^{k-1} γ_{i+1} U_{i+1}‖ : k = n+1, …, m(τ_n + T) } = 0`. -/
def IsA1 {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ T : ℝ, 0 < T → Tendsto (fun n : ℕ => a1Sup γ U n T) atTop (𝓝 0)

/-- `Δ(t, T) = sup_{0 ≤ h ≤ T} ‖∫_t^{t+h} Ū(s) ds‖`, Eq. (10) (§4.1, p. 12), valued in
`[0, ∞]` (it is finite under the standing assumptions, since `Ū` takes finitely many values on
`[t, t + T]`). -/
noncomputable def noiseDev {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) (t T : ℝ) :
    ℝ≥0∞ :=
  ⨆ h ∈ Set.Icc (0 : ℝ) T, ‖∫ s in t..(t + h), noisePath γ U s‖ₑ

/-- Assumption A1 (§4.1, p. 12), second ("equivalent") form: for all `T > 0`,
`lim_{t→∞} Δ(t, T) = 0`. -/
def IsA1Delta {d : ℕ} (γ : ℕ → ℝ) (U : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ T : ℝ, 0 < T → Tendsto (fun t : ℝ => noiseDev γ U t T) atTop (𝓝 0)

end StochApproxDyn.MartingaleNoise


