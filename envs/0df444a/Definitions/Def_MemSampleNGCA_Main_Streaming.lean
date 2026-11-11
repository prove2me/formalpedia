-- Prove2me | Definitions.Def_MemSampleNGCA_Main_Streaming
-- name    : MemSampleNGCA_Main_Streaming
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:38:40.196914+00:00
-- url     : https://prove2.me/theorems/1076f04c-a7d3-4807-b31d-b37454263440
-- title:
--   Single-pass streaming algorithms with B bits of memory, their output law, and the testing criterion (Definition 1.7, Problem 1.6)
-- statement:
--   A **single-pass streaming algorithm with $B$ bits of memory** on an observation space $\mathcal X$ (Definition 1.7) consists of a randomness space $\Omega$ with a probability measure $R$, a fixed start state $V_0\in\{0,1\}^B$, a randomized update map $\mathrm{Upd}:\{0,1\}^B\times\mathcal X\times\mathbb N\times\Omega\to\{0,1\}^B$ and a randomized output map $\mathrm{Out}:\{0,1\}^B\times\Omega\to\{0,1\}$. On samples $X_1,\dots,X_N$ it reads $X_i$ and a fresh seed $U_i\sim R$ and sets
--   $$V_i=\mathrm{Upd}(V_{i-1},X_i,i,U_i),\qquad i=1,\dots,N,$$
--   and then outputs $\widehat T=\mathrm{Out}(V_N,U_{\mathrm{out}})$ with a fresh $U_{\mathrm{out}}\sim R$; the seeds are i.i.d. and independent of the samples.
--
--   For a law $D$ on $\mathcal X$, `stateProb` is $P_{X_{1:N}\sim D^{\otimes N}}(V_k=v)$ and `outProb` is $P_{X_{1:N}\sim D^{\otimes N}}(\widehat T=b)$, both computed under $D^{\otimes N}\otimes R^{\otimes N}\otimes R$. For a null $R_0$ and a set of alternatives $\mathcal M$ (Problem 1.6), the **test error** is
--   $$P_{R_0^{\otimes N}}(\widehat T=1)+\sup_{D\in\mathcal M}P_{D^{\otimes N}}(\widehat T=0),$$
--   and the algorithm **solves** the testing problem with $N$ samples when this is at most $0.1$ (§1.3).
--
--   This is the computational model of every memory lower bound in the mission.
--
--   **Formalization Note.** $\{0,1\}^B$ is `Fin B → Bool` (2^B states, discrete σ-algebra). $\Omega$ is an arbitrary measurable space; `Upd` (for each index $i$, jointly in state, sample and seed) and `Out` are measurable, which is what makes the probabilities above exist. Lean sample `x ⟨k, _⟩` is the paper's $X_{k+1}$, and the update at that step receives the index $k+1\in[N]$. Probabilities are `ℝ≥0∞`-valued, the supremum is `⨆` in `ℝ≥0∞`, and $0.1$ is `1/10`.
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), pp. 5–6 (PDF 7–8), Problem 1.6, testing criterion of §1.3, Definition 1.7

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-! # Single-pass streaming algorithms with `B` bits of memory (Definition 1.7)

Pensia, Gupta, Verchand, Sharan, Vedantam, *Memory-Sample Tradeoffs in High-Dimensional
Statistics*, STOC 2027 submission (manuscript sha256 ac94994a…), Problem 1.6 and the testing
criterion of §1.3, Definition 1.7 (p. 5–6, PDF 7–8).

The memory state space `{0,1}^B` is `Fin B → Bool` (with its product, i.e. discrete,
σ-algebra). The randomness space is an arbitrary measurable space `Ω` carrying a probability
measure `R`; the update map may depend on the sample index `i ∈ [N] = {1, …, N}`.
Samples are `x : Fin N → X` and the internal random seeds are `u : Fin N → Ω` (one per update)
and `uout : Ω` (for the output); Lean index `k : Fin N` is the paper's sample `X_{k+1}`. -/

/-- A single-pass streaming algorithm with `B` bits of memory on observation space `X`, with
randomness space `Ω` (Definition 1.7): a fixed start state `V₀`, a measurable randomized update
map `Upd : {0,1}^B × X × ℕ × Ω → {0,1}^B`, a measurable randomized output map
`Out : {0,1}^B × Ω → {0,1}`, and the law `R` of each fresh random seed (a probability measure). -/
structure StreamingAlg (B : ℕ) (X : Type*) [MeasurableSpace X] (Ω : Type*) [MeasurableSpace Ω] where
  /-- The fixed start state `V₀ ∈ {0,1}^B`. -/
  start : Fin B → Bool
  /-- The update map `Upd(v, x, i, u)`. -/
  upd : (Fin B → Bool) → X → ℕ → Ω → (Fin B → Bool)
  /-- The output map `Out(v, u) ∈ {0,1}` (`true` = `1`). -/
  out : (Fin B → Bool) → Ω → Bool
  /-- The law `R` of every fresh random seed. -/
  R : Measure Ω
  isProb : IsProbabilityMeasure R
  /-- For each index `i`, `(v, x, u) ↦ Upd(v, x, i, u)` is jointly measurable. -/
  upd_meas : ∀ i : ℕ, Measurable (fun p : (Fin B → Bool) × X × Ω => upd p.1 p.2.1 i p.2.2)
  /-- `(v, u) ↦ Out(v, u)` is jointly measurable. -/
  out_meas : Measurable (fun p : (Fin B → Bool) × Ω => out p.1 p.2)

variable {B : ℕ} {X : Type*} [MeasurableSpace X] {Ω : Type*} [MeasurableSpace Ω]

namespace StreamingAlg

/-- The memory state `V_k` after reading the first `k` samples (`k ≤ N`):
`V_0 = start` and `V_{k+1} = Upd(V_k, X_{k+1}, k+1, U_{k+1})`. For `k > N` the state stays `V_N`. -/
def state (A : StreamingAlg B X Ω) {N : ℕ} (x : Fin N → X) (u : Fin N → Ω) :
    ℕ → (Fin B → Bool)
  | 0 => A.start
  | k + 1 =>
    if hk : k < N then A.upd (A.state x u k) (x ⟨k, hk⟩) (k + 1) (u ⟨k, hk⟩)
    else A.state x u k

/-- The joint law of the `N` samples (i.i.d. from `D`) and of the `N` update seeds (i.i.d. from
`R`, independent of the samples): `D^{⊗N} ⊗ R^{⊗N}`. -/
noncomputable def sampleLaw (A : StreamingAlg B X Ω) (N : ℕ) (D : Measure X) :
    Measure ((Fin N → X) × (Fin N → Ω)) :=
  (Measure.pi fun _ : Fin N => D).prod (Measure.pi fun _ : Fin N => A.R)

/-- `P_{X_{1:N} ∼ D^{⊗N}}(V_k = v)`: the probability that the memory state after `k` samples is
`v`, when the samples are i.i.d. from `D`. -/
noncomputable def stateProb (A : StreamingAlg B X Ω) (N : ℕ) (D : Measure X) (k : ℕ)
    (v : Fin B → Bool) : ℝ≥0∞ :=
  A.sampleLaw N D {ω | A.state ω.1 ω.2 k = v}

/-- `P_{X_{1:N} ∼ D^{⊗N}}(T̂ = b)`: the probability that the algorithm run on `N` i.i.d. samples
from `D` outputs `b`, with `T̂ = Out(V_N, U_out)` and `U_out ∼ R` independent of everything else. -/
noncomputable def outProb (A : StreamingAlg B X Ω) (N : ℕ) (D : Measure X) (b : Bool) : ℝ≥0∞ :=
  ((A.sampleLaw N D).prod A.R) {ω | A.out (A.state ω.1.1 ω.1.2 N) ω.2 = b}

/-- The error of the algorithm as a tester of `H₀ : D = R₀` against `H₁ : D ∈ 𝓜` (Problem 1.6):
`P_{R₀^{⊗N}}(T̂ = 1) + sup_{D ∈ 𝓜} P_{D^{⊗N}}(T̂ = 0)`. -/
noncomputable def testError (A : StreamingAlg B X Ω) (N : ℕ) (R₀ : Measure X)
    (alt : Set (Measure X)) : ℝ≥0∞ :=
  A.outProb N R₀ true + ⨆ D ∈ alt, A.outProb N D false

/-- The algorithm *solves* the testing problem 1.6 with `N` samples (§1.3, p. 6):
`P_{R₀^{⊗N}}(T̂ = 1) + sup_{D ∈ 𝓜} P_{D^{⊗N}}(T̂ = 0) ≤ 0.1`. -/
def Solves (A : StreamingAlg B X Ω) (N : ℕ) (R₀ : Measure X) (alt : Set (Measure X)) : Prop :=
  A.testError N R₀ alt ≤ 1 / 10

end StreamingAlg

end MemSampleNGCA.Main


