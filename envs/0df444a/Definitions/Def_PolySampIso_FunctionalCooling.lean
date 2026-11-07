-- Prove2me | Definitions.Def_PolySampIso_FunctionalCooling
-- name    : PolySampIso_FunctionalCooling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:10.212195+00:00
-- url     : https://prove2.me/theorems/4f262edf-2d69-4f26-a6ec-0719310ee9ba
-- title:
--   Algorithm 5 (FunctionalCooling): Gaussian initialization and the cooling schedule
-- statement:
--   **Algorithm 5** takes $\delta\in(0,\tfrac12)$ and oracles $\{O_t\}_{t\ge0}$. **Phase 1:** $D=n+\log(8/\delta)$, $t_1=10^6D^3$, $\hat x=\mathrm{AnalyticCenter}(X,1/(100\sqrt{t_1D}))$, $x\sim\mathcal N(\hat x,t_1^{-1}H(\hat x)^{-1})$, and $x\leftarrow\hat x$ if $\|x-\hat x\|_{\hat x}>4\sqrt{D/t_1}$. **Phase 2:** while $t\ge n/m$, $x\leftarrow O_t(x)$ and $t\leftarrow t(1+1/\sqrt n)^{-1}$. **Phase 3:** while $t\ge1/m$, $x\leftarrow O_t(x)$ and $t\leftarrow t(1+1/\sqrt{mt})^{-1}$. **Phase 4:** $x\leftarrow O_t(x)$, then $x\leftarrow O_0(x)$; return $x$.
--
--   The schedule moves from a strongly cooled measure $\pi_{t_1}$, which a Gaussian at an approximate analytic center warm-starts, to $\pi_0=\pi$, each stage warm-starting the next (Lemmas 24, 26–28).
--
--   **Formalization Note** $\hat x$ is a parameter (only its guarantee is used). The temperatures are an explicit list: $t_1(1+1/\sqrt n)^{-k}$ for $k$ below the first exit index of Phase 2, then the iterates of $t\mapsto t(1+1/\sqrt{mt})^{-1}$ below the first exit index of Phase 3, then the final temperature and $0$. The output law composes the Phase 1 law with the oracle kernels in this order.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Algorithm 5, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_PolySampIso_LogBarrier

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-!
# Algorithm 5: FunctionalCooling(δ, {O_t}_{t≥0})

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Algorithm 5, p.33 (PDF p.35):
"1 Input: target error δ ∈ (0, 1/2), oracles {Ot}t≥0 where Ot is a (3, δ/(2T))-χ2-to-TV oracle for πt,
T := C′(m + √n log(m/δ)) for the constant C′ in Corollary 3
2 D ← n + log 8/δ, t ← t1 := 10⁶D³
3 x̂ ← AnalyticCenter(X, 1/(100√(tD))) ▷ See Proposition 5.
4 x ∼ N(x̂, (1/t) H(x̂)−1)
5 if ∥x − x̂∥x̂ > 4√(D/t) then
6   x ← x̂
7 end
8 while t ≥ n/m do
9   x ← Ot(x)
10  t ← t · (1 + 1/√n)−1
11 end
12 while t ≥ 1/m do
13  x ← Ot(x)
14  t ← t · (1 + 1/√(mt))−1
15 end
16 x ← Ot(x)
17 x ← O0(x)
18 Return: x"

**Formalization Note.**
* Line 3's output `x̂` is a parameter: the lemmas use only its guarantee
  `‖∇ψ(x̂)‖_{x̂,∗} ≤ 1/(100√(t₁D))` (Proposition 5).
* `phase1Law A b δ x̂` is the law of `x` after line 7: the Gaussian `N(x̂, t₁⁻¹H(x̂)⁻¹)`
  (Mathlib's `multivariateGaussian`) pushed forward by the rejection of lines 5–6.
* The temperatures are an explicit list. Phase 2 calls `O_t` at `t₁(1 + 1/√n)^{−k}` for
  `k < k₂`, where `k₂` is the first `k` with `t₁(1 + 1/√n)^{−k} < n/m`; Phase 3 iterates
  `g(t) = t(1 + 1/√(mt))⁻¹` from the temperature where Phase 2 stopped and calls `O_t` at
  `g^k(t₂)` for `k < k₃`, `k₃` the first `k` with `g^k(t₂) < 1/m`; Phase 4 calls `O_{g^{k₃}(t₂)}`
  and then `O_0`. Both first-exit indices exist (the loops terminate, p.35–36), so the `sInf`s are
  attained.
* `coolingLaw A b δ x̂ O` is the law of the output for a family of Markov kernels `O t`
  (`O_t(x)` has law `O t x`, fresh randomness at every call).
-/

/-- `D = n + log(8/δ)` (line 2). -/
noncomputable def coolD (n : ℕ) (δ : ℝ) : ℝ := n + Real.log (8 / δ)

/-- `t₁ = 10⁶D³` (line 2). -/
noncomputable def coolT1 (n : ℕ) (δ : ℝ) : ℝ := 10 ^ 6 * coolD n δ ^ 3

/-- The law of `x` at the end of Phase 1 (lines 4–7), given `x̂`. -/
noncomputable def phase1Law {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (δ : ℝ)
    (xhat : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  open Classical in
  (multivariateGaussian xhat ((1 / coolT1 n δ) • (hessLogBarrier A b xhat)⁻¹)).map fun x =>
    if localNorm A b xhat (x - xhat) > 4 * Real.sqrt (coolD n δ / coolT1 n δ) then xhat else x

/-- The Phase 2 temperatures `t₁(1 + 1/√n)^{−k}`. -/
noncomputable def phase2Temp (n : ℕ) (δ : ℝ) (k : ℕ) : ℝ :=
  coolT1 n δ * ((1 + 1 / Real.sqrt n) ^ k)⁻¹

/-- The number `k₂` of Phase 2 calls: the first `k` with `t₁(1 + 1/√n)^{−k} < n/m`. -/
noncomputable def phase2Count (m n : ℕ) (δ : ℝ) : ℕ :=
  sInf {k : ℕ | phase2Temp n δ k < (n : ℝ) / m}

/-- The Phase 3 update `g(t) = t(1 + 1/√(mt))⁻¹` (line 14). -/
noncomputable def phase3Update (m : ℕ) (t : ℝ) : ℝ :=
  t * (1 + 1 / Real.sqrt (m * t))⁻¹

/-- The temperature at which Phase 3 starts (where Phase 2 stopped). -/
noncomputable def phase3Start (m n : ℕ) (δ : ℝ) : ℝ :=
  phase2Temp n δ (phase2Count m n δ)

/-- The number `k₃` of Phase 3 calls: the first `k` with `g^k(t₂) < 1/m`. -/
noncomputable def phase3Count (m n : ℕ) (δ : ℝ) : ℕ :=
  sInf {k : ℕ | (phase3Update m)^[k] (phase3Start m n δ) < 1 / (m : ℝ)}

/-- The temperatures of the oracle calls of Algorithm 5, in order (Phases 2, 3, 4). -/
noncomputable def coolingSchedule (m n : ℕ) (δ : ℝ) : List ℝ :=
  (List.range (phase2Count m n δ)).map (phase2Temp n δ) ++
    (List.range (phase3Count m n δ)).map (fun k => (phase3Update m)^[k] (phase3Start m n δ)) ++
    [(phase3Update m)^[phase3Count m n δ] (phase3Start m n δ), 0]

/-- The law of the output of Algorithm 5 with oracles `O t` and Phase 1 center `x̂`. -/
noncomputable def coolingLaw {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (δ : ℝ)
    (xhat : EuclideanSpace ℝ (Fin n))
    (O : ℝ → Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (coolingSchedule m n δ).foldl (fun μ t => O t ∘ₘ μ) (phase1Law A b δ xhat)

end PolySampIso


