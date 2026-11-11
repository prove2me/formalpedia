-- Prove2me | Definitions.Def_OCEClocks_DisplayAds_Kernels
-- name    : OCEClocks_DisplayAds_Kernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:22:02.287209+00:00
-- url     : https://prove2.me/theorems/7f2d9dee-68c7-4bfc-ad02-83603c0459b8
-- title:
--   Matching kernel $M_x$ (4), gap kernel $G_t$, winning probability $D_x$, stationary law $\pi$ and reachable measures
-- statement:
--   Fix $\lambda>0$. **Ages** are elements of $[0,\infty)$; $\pi=\mathrm{Exp}(\lambda)$ is the stationary age distribution.
--
--   **The age process started at age $a$.** The last arrival is at time $-a$ and the later arrivals are at $\tau_k=S_0+\dots+S_k$, where the gaps $S_k$ are i.i.d. $\mathrm{Exp}(\lambda)$. The age at time $t\ge0$ is $A(t)=t-\max\big(\{-a\}\cup\{\tau_k:\tau_k\le t\}\big)$. A request of mass $x$ occupies $[0,x)$. Its first age is $a+\tau_0$ if $\tau_0<x$ and $0$ otherwise, and its clock $Y$ is produced from this first age and an independent $V\sim\mathrm{Unif}[0,1]$ exactly as in the First-Age Poisson generator.
--
--   **Matching kernel (4).** On a fresh competing clock of rate $1-x$ the resource loses with probability $1-e^{-(1-x)Y}$. For bounded measurable $f$,
--
--   $$(M_xf)(a)=\mathbb E\big[f(A(x))\,(1-e^{-(1-x)Y})\ \big|\ A(0)=a\big],$$
--
--   and for a finite measure $\nu$ on ages, $(\nu M_x)(H)=\int\mathbb E\big[\mathbf 1\{A(x)\in H\}(1-e^{-(1-x)Y})\mid A(0)=a\big]\,\nu(da)$.
--
--   **Gap kernel.** $(G_tf)(a)=\mathbb E[f(A(t))\mid A(0)=a]$ and $(\nu G_t)(H)=\int\Pr[A(t)\in H\mid A(0)=a]\,\nu(da)$, for $t\ge0$.
--
--   **Winning probability (B.1).** $D_x(b)$ is the probability that a request of mass $x$ whose interval has first age $b$ wins against a fresh competing clock of rate $1-x$.
--
--   **Reachable measures (§5.3).** These are the measures obtained from $\pi$ by a finite sequence of matching kernels $M_x$, $x\in[0,1]$, and gap kernels $G_t$, $t\ge0$.
--
--   These operators carry the paper's analysis: a reachable measure is the law of a resource's age restricted to the outcomes in which it has lost every comparison so far.
--
--   **Formalization Note** Measures on ages are measures on `ℝ` and functions on ages are `ℝ → ℝ`. Conditioning on $A(0)=a$ is realised by the started process (`startedLaw λ`: i.i.d. `expMeasure λ` gaps indexed by `ℕ`, times `unifLaw`); this is how the paper computes these expectations (proofs of Lemmas 16 and 32). `matchingKernelMeasure λ x ν` is the image of `(ν ⊗ startedLaw λ)` weighted by the loss probability under $A(x)$, and `gapKernelMeasure λ t ν` is the image without weight. `winProbGivenAge λ x b` is $D_x(b)=\mathbb E_V[\operatorname{beat}_{1-x}(Y)]$. `Reachable λ` is the inductive closure of `stationaryAge λ = expMeasure λ` under both kernels.
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), pp. 10–11, §4.1 (matching kernel, eq. (4)); p. 14, §5.2 (gap kernel); p. 15, §5.3 (reachable measures); p. 37, B.1 (D_x)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_ExpClock
import Definitions.Def_OCEClocks_DisplayAds_FirstAgeGenerator

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OCEClocks.DisplayAds

/-!
# Matching kernel `M_x`, gap kernel `G_t`, `D_x`, `π` and reachable measures

Huang, Patton, Yang, Zhao, *Online Correlated Exponential Clocks*, STOC 2027 submission
(manuscript of November 3, 2026), pp. 10–11 (§4.1, matching kernel (4)), p. 14 (§5.2, gap
kernel), p. 15 (§5.3, reachable measures), p. 37 (B.1, `D_x`).

Ages live in `[0, ∞)`; measures on ages are finite measures on `ℝ` and functions on ages are
functions `ℝ → ℝ` (only their values on `[0, ∞)` are used). "Given `A(0) = a`" is realised by the
age process started at age `a`: the last arrival is at time `-a` and the later arrivals are at
`τ_k = S_0 + ⋯ + S_k` (`k ∈ ℕ`), with i.i.d. `Exp(λ)` gaps `S_k`; one independent
`V ∼ Unif[0, 1]` drives the randomized step of the clock of a request placed on `[0, x)`.
-/

/-- The randomness of the age process started at a given age: i.i.d. `Exp(λ)` gaps `S_k`,
`k ∈ ℕ`, and an independent uniform `V ∼ Unif[0, 1]`. -/
noncomputable def startedLaw (lam : ℝ) : Measure ((ℕ → ℝ) × ℝ) :=
  (Measure.infinitePi (fun _ : ℕ => expMeasure lam)).prod unifLaw

/-- The `k`-th arrival after time `0`: `τ_k = S_0 + ⋯ + S_k`. -/
def startedArrival (S : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), S i

/-- The age `A(t)` at time `t ≥ 0` of the process started at age `a`:
`t - max ({-a} ∪ {τ_k : τ_k ≤ t})`. -/
noncomputable def startedAge (a t : ℝ) (S : ℕ → ℝ) : ℝ :=
  t - sSup (insert (-a) {s | ∃ k, startedArrival S k = s ∧ s ≤ t})

/-- The first age of the request interval `[0, x)` for the process started at age `a`: the age
`a + τ_0` of the first arrival `τ_0 = S_0` if it falls before `x`, and `0` if there is none. -/
noncomputable def startedFirstAge (a x : ℝ) (S : ℕ → ℝ) : ℝ :=
  if S 0 < x then a + S 0 else 0

/-- `D_x(b)` (B.1, p. 37): the probability that a request of mass `x` whose interval has first age
`b` wins against a fresh competing clock of rate `1 - x`, i.e. `E_V[P(Y < Z)]` for the clock
`Y = clockOf λ x b V` of the generator and `Z ∼ Exp(1 - x)`. -/
noncomputable def winProbGivenAge (lam x b : ℝ) : ℝ :=
  ∫ v, beatProb (1 - x) (clockOf lam x b v) ∂unifLaw

/-- The probability `1 - e^{-(1-x)Y}` that a clock `Y = clockOf λ x b v` loses against a fresh
competing clock of rate `1 - x` (§4.1, p. 10). -/
noncomputable def lossProb (lam x b v : ℝ) : ℝ :=
  1 - beatProb (1 - x) (clockOf lam x b v)

/-- The matching kernel acting on functions, eq. (4) (p. 10):
`(M_x f)(a) = E[f(A(x)) (1 - e^{-(1-x)Y}) | A(0) = a]`. -/
noncomputable def matchingKernel (lam x : ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ p, f (startedAge a x p.1) * lossProb lam x (startedFirstAge a x p.1) p.2 ∂startedLaw lam

/-- The matching kernel acting on measures (p. 10):
`(νM_x)(H) = ∫ E[1{A(x) ∈ H}(1 - e^{-(1-x)Y}) | A(0) = a] ν(da)`. -/
noncomputable def matchingKernelMeasure (lam x : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  ((ν.prod (startedLaw lam)).withDensity
      (fun q => ENNReal.ofReal (lossProb lam x (startedFirstAge q.1 x q.2.1) q.2.2))).map
    (fun q => startedAge q.1 x q.2.1)

/-- The gap kernel acting on functions (§5.2, p. 14): `(G_t f)(a) = E[f(A(t)) | A(0) = a]`. -/
noncomputable def gapKernel (lam t : ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ p, f (startedAge a t p.1) ∂startedLaw lam

/-- The gap kernel acting on measures: `(νG_t)(H) = ∫ P[A(t) ∈ H | A(0) = a] ν(da)`. -/
noncomputable def gapKernelMeasure (lam t : ℝ) (ν : Measure ℝ) : Measure ℝ :=
  (ν.prod (startedLaw lam)).map (fun q => startedAge q.1 t q.2.1)

/-- The stationary age distribution `π = Exp(λ)` (p. 10). -/
noncomputable def stationaryAge (lam : ℝ) : Measure ℝ :=
  expMeasure lam

/-- Reachable measures (§5.3, p. 15): obtained from `π` by a finite sequence of matching kernels
`M_x`, `x ∈ [0, 1]`, and gap kernels `G_t`, `t ≥ 0`. -/
inductive Reachable (lam : ℝ) : Measure ℝ → Prop
  | stationary : Reachable lam (stationaryAge lam)
  | matching {ν : Measure ℝ} {x : ℝ} :
      Reachable lam ν → x ∈ Set.Icc (0 : ℝ) 1 → Reachable lam (matchingKernelMeasure lam x ν)
  | gap {ν : Measure ℝ} {t : ℝ} :
      Reachable lam ν → 0 ≤ t → Reachable lam (gapKernelMeasure lam t ν)

end OCEClocks.DisplayAds


