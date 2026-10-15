-- Prove2me | Definitions.Def_BreakingSample_Perturbed_Sampling
-- name    : BreakingSample_Perturbed_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:19.049014+00:00
-- url     : https://prove2.me/theorems/023a596d-4fed-40f8-b4ae-5ce493c74937
-- title:
--   §2.1, (3), (8), (10), and (45) — generative samples, empirical kernel, and perturbation laws
-- statement:
--   For every state-action pair $(s,a)$, a generative model supplies $N$ independent next-state samples $X^i_{s,a}$ with law $P(\cdot\mid s,a)$. Their empirical transition kernel is
--
--   $$\widehat P(s'\mid s,a)=\frac1N\sum_{i=1}^{N}{\bf1}\{X^i_{s,a}=s'\}.$$
--
--   This module gives the joint law of all samples as a finite product, the probability of a sample event, and the independent uniform laws for a scalar threshold and for the reward perturbation $\zeta\in[0,\xi]^{S\times A}$. The perturbation entries are independent and uniform on $[0,\xi]$.
--
--   **Formalization Note** The empirical formula is used under $N>0$. Joint failure probabilities sum over the finite sample space and use the auxiliary measure of each section.
-- source:
--   arXiv:2005.12900v8, §2.1, (3), p. 5; (8), p. 7; (10), p. 8; (45), p. 17

import Mathlib

namespace BreakingSample.Perturbed

open MeasureTheory

/-- A data set of the generative model (§2.1, p. 5): for each pair `(s,a)`, `N` next states
`s^i_{s,a}`, `i = 1, …, N` (here indexed by `Fin N`). -/
abbrev Samples (S A : Type*) (N : ℕ) : Type _ := S → A → Fin N → S

/-- The empirical kernel (3), p. 5: `P̂(s'|s,a) = (1/N) ∑ᵢ 1{s^i_{s,a} = s'}`. -/
noncomputable def empKernel {S A : Type*} [DecidableEq S] {N : ℕ} (x : Samples S A N)
    (s : S) (a : A) (s' : S) : ℝ :=
  ((Finset.univ.filter (fun i => x s a i = s')).card : ℝ) / N

/-- The probability of the data set `x` when all samples are independent and `s^i_{s,a} ∼ P(·|s,a)`. -/
noncomputable def sampleWeight {S A : Type*} [Fintype S] [Fintype A] {N : ℕ}
    (P : S → A → S → ℝ) (x : Samples S A N) : ℝ :=
  ∏ s, ∏ a, ∏ i, P s a (x s a i)

/-- The probability `ℙ(E)` of an event `E` of the data set. -/
noncomputable def sampleProb {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (N : ℕ) (E : Samples S A N → Prop) : ℝ := by
  classical exact ∑ x : Samples S A N, if E x then sampleWeight P x else 0

/-- The law `Unif(0, ξ)` of the threshold `ς` in (10), p. 8. -/
noncomputable def unifInterval (ξ : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc 0 ξ)

/-- The law of the perturbation `ζ = (ζ(s,a))` of (8), p. 7, and (45), p. 17: independent `Unif(0, ξ)`
entries, i.e. the uniform law on the cube `[0, ξ]^{S×A}`. -/
noncomputable def unifCube (S A : Type*) [Fintype S] [Fintype A] (ξ : ℝ) : Measure (S → A → ℝ) :=
  ProbabilityTheory.cond volume (Set.univ.pi fun _ : S => Set.univ.pi fun _ : A => Set.Icc 0 ξ)

/-- The probability of an event `E` of the data set and of an independent auxiliary draw `z ∼ μ`:
`∑_x ℙ(x) · μ{z | E x z}`. For a non-measurable section `μ` is the outer measure, so a bound
`jointProb … ≤ δ` on a failure event is never weaker than the measurable statement. -/
noncomputable def jointProb {S A Z : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [MeasurableSpace Z] (P : S → A → S → ℝ) (N : ℕ) (μ : Measure Z)
    (E : Samples S A N → Z → Prop) : ℝ :=
  ∑ x : Samples S A N, sampleWeight P x * (μ {z | E x z}).toReal

end BreakingSample.Perturbed


