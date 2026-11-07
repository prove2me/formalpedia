-- Prove2me | Definitions.Def_QubitFreqSensing_PulseProtocol
-- name    : QubitFreqSensing_PulseProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:41.322922+00:00
-- url     : https://prove2.me/theorems/de67385e-9528-4b2a-8b3c-9382c03187df
-- title:
--   Single-qubit $Y$-pulse sensing protocols: pulse blocks, randomized trials, repetition, detection probability
-- statement:
--   This module fixes the class of protocols of Theorem 1.1: one sensing qubit, no auxiliary qubits, instantaneous gates, and only Pauli $Y$ pulses between stretches of evolution under the unknown field $h$.
--
--   1. A **pulse block** consists of a start gate $G\in U(2)$, durations $d_1,\dots,d_m\ge 0$ ($m\ge1$) and a finish gate $F\in U(2)$. Run from absolute time $a$ after a wait $\tau\ge0$, it maps $|0\rangle$ to
--   $$
--   \psi_{\mathrm{fin}}=F\,U_h(s_{m-1},s_m)\,Y\cdots Y\,U_h(s_1,s_2)\,Y\,U_h(s_0,s_1)\,G\,U_h(a,a+\tau)\,|0\rangle ,
--   $$
--   where $s_0=a+\tau$ and $s_k=s_{k-1}+d_k$. The block has $m-1$ pulses $Y$. Measuring in the standard basis gives outcome $1$ with probability $p_1(h,a,\tau)=|\langle 1|\psi_{\mathrm{fin}}\rangle|^2$.
--   2. A **randomized trial** chooses branch $i$ with probability $p_i$ ($p_i\ge 0$, $\sum_i p_i=1$), draws its wait $\tau$ from a probability law $\mu_i$ supported in $[0,\tau^{\max}_i]$, and runs block $i$.
--   3. A **protocol** repeats one randomized trial $r$ times with fresh randomness, each trial starting at the absolute time where the previous one ended, and outputs "signal present" iff some trial gives outcome $1$. The probability that $k$ trials starting at time $t$ all give $0$ is
--   $$
--   \mathrm{miss}_0(t)=1,\qquad \mathrm{miss}_{k+1}(t)=\sum_i p_i\int \bigl(1-p_1^{(i)}(h,t,\tau)\bigr)\,\mathrm{miss}_k\Bigl(t+\tau+\sum_j d^{(i)}_j\Bigr)\,d\mu_i(\tau),
--   $$
--   and the detection probability is $1-\mathrm{miss}_r(0)$.
--
--   Protocol 1 of the paper is the instance with two branches $b\in\{0,1\}$ of probability $1/2$, the uniform wait law on $[0,D]$ (also defined here), start gate $e^{i\sigma_1\pi Y/4}$, durations the piece lengths of the sign pattern $f_b$, finish gate $e^{-i\sigma_1\pi Y/4}Y^{m-1}$, and $r=28$ repetitions.
--
--   **Formalization Note** Absolute time runs on across trials, so trial $k+1$ sees the phase where trial $k$ left it ("a trial starting at absolute time s sees phase ϕ + ωs", p.12). Gates may not depend on the signal. The integrals in $\mathrm{miss}$ are Bochner integrals of $[0,1]$-valued functions that are continuous in $\tau$ for continuous $h$ (sanity file), so they are genuine expectations.
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), Protocol 1 and its analysis paragraphs, pp.12–13; §3, p.11; Theorem 1.1, p.3

import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_QubitFreqSensing_Propagator

open MeasureTheory Matrix

namespace QubitFreqSensing

/-- **Pulse block** of a single-qubit sensing trial (Chen, Coladangelo, Li, Zhang, manuscript (STOC
2027 submission), Protocol 1, steps 2–4, p.12; §7, p.25). A block consists of a start gate, a list
of evolution durations `d₁, …, d_m ≥ 0` (`m ≥ 1`) separated by Pauli `Y` pulses, and a finish gate:
the trial evolves under the signal for `d₁`, applies `Y`, evolves for `d₂`, applies `Y`, …, evolves
for `d_m`, then applies the finish gate. Only the start and finish gates are free single-qubit
unitaries; between them the only control is `Y` ("The protocol uses finitely many Pauli Y gates,
alternating with evolution under the signal Hamiltonian", Theorem 1.1, p.3). -/
structure PulseBlock where
  /-- the gate applied after the wait (Protocol 1's `G₀`) -/
  start : Matrix.unitaryGroup (Fin 2) ℂ
  /-- the gate applied before the measurement (Protocol 1's `(G_{m-1}⋯G₀)†`) -/
  finish : Matrix.unitaryGroup (Fin 2) ℂ
  /-- the evolution times `d₁, …, d_m` between consecutive `Y` pulses -/
  durations : List ℝ
  durations_ne_nil : durations ≠ []
  durations_nonneg : ∀ d ∈ durations, 0 ≤ d

/-- Evolution through the alternation "evolve `d₁`, `Y`, evolve `d₂`, `Y`, …, evolve `d_m`"
starting at absolute time `t` (no `Y` after the last piece). -/
noncomputable def evolveAlt (h : ℝ → ℝ) : ℝ → List ℝ → (Fin 2 → ℂ) → (Fin 2 → ℂ)
  | _, [], ψ => ψ
  | t, [d], ψ => propagator h t (t + d) *ᵥ ψ
  | t, d :: d' :: ds, ψ =>
      evolveAlt h (t + d) (d' :: ds) (MIPRE.LCS.Pauli.Y *ᵥ (propagator h t (t + d) *ᵥ ψ))

/-- The state just before the measurement of a trial that starts at absolute time `a`, waits `τ`
under the signal, then runs the block `blk`: `finish · (alternation) · start · U_h(a, a+τ) |0⟩`. -/
noncomputable def finalState (h : ℝ → ℝ) (a τ : ℝ) (blk : PulseBlock) : Fin 2 → ℂ :=
  blk.finish.1 *ᵥ evolveAlt h (a + τ) blk.durations
    (blk.start.1 *ᵥ (propagator h a (a + τ) *ᵥ ket0))

/-- Probability that a trial (start time `a`, wait `τ`, block `blk`) gives outcome `1` when its
final state is measured in the standard basis: `|⟨1|ψ_final⟩|²`. -/
noncomputable def pOne (h : ℝ → ℝ) (a τ : ℝ) (blk : PulseBlock) : ℝ :=
  Complex.normSq (finalState h a τ blk 1)

/-- **Randomized trial** (Protocol 1, "One trial", p.12). With probability `prob i` the trial uses
branch `i`: it draws its wait `τ` from the probability law `waitLaw i`, supported in
`[0, waitMax i]`, and then runs the pulse block `block i`. Protocol 1 is the case of two branches
`b ∈ {0, 1}` of probability `1/2` with `τ ∼ Unif[0, D]`. -/
structure RandomTrial where
  n : ℕ
  prob : Fin n → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_sum : ∑ i, prob i = 1
  waitLaw : Fin n → Measure ℝ
  waitLaw_isProb : ∀ i, IsProbabilityMeasure (waitLaw i)
  waitMax : Fin n → ℝ
  waitLaw_support : ∀ i, waitLaw i (Set.Icc 0 (waitMax i))ᶜ = 0
  block : Fin n → PulseBlock

/-- **Single-qubit sensing protocol** (Protocol 1, p.12): one randomized trial repeated `reps`
times with fresh randomness and a newly prepared state; the decision is "signal present" iff some
trial gives outcome `1`. -/
structure Protocol where
  trial : RandomTrial
  reps : ℕ

/-- Probability that `k` consecutive trials, the first starting at absolute time `t`, all give
outcome `0`. Absolute time runs on: a trial of branch `i` with wait `τ` that starts at `t` ends at
`t + τ + Σ d`, where the next trial starts ("a trial starting at absolute time s sees phase
ϕ + ωs", p.12). -/
noncomputable def missProb (h : ℝ → ℝ) (R : RandomTrial) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, t => ∑ i, R.prob i * ∫ τ, (1 - pOne h t τ (R.block i)) *
      missProb h R k (t + τ + (R.block i).durations.sum) ∂(R.waitLaw i)

/-- Probability that the protocol outputs "signal present" under the field `h`, starting at
absolute time `0`: one minus the probability that all `reps` trials give outcome `0`.

**Formalization Note** The integrals in `missProb` are Bochner integrals of functions with values
in `[0, 1]` that are continuous in `τ` whenever `h` is continuous (sanity file), so they are genuine
expectations, not Lean's junk value `0`. -/
noncomputable def presentProb (h : ℝ → ℝ) (P : Protocol) : ℝ :=
  1 - missProb h P.trial P.reps 0

/-- The uniform law on `[0, D]` (Protocol 1, step 2, p.12: "Sample a random wait time
τ ∼ Unif[0, D]"). -/
noncomputable def uniformWait (D : ℝ) : Measure ℝ :=
  (ENNReal.ofReal D)⁻¹ • volume.restrict (Set.Icc 0 D)

end QubitFreqSensing


