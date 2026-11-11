-- Prove2me | Definitions.Def_LimitedEntanglementTomography_LowerBound_Protocol
-- name    : LimitedEntanglementTomography_LowerBound_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:15.930591+00:00
-- url     : https://prove2.me/theorems/8c52196c-3aec-4720-adba-adae85ac746a
-- title:
--   Adaptive protocols with measurements on at most $k$ copies, transcript laws, copy budget, success, and $\operatorname{tr} J_Y(\rho)$
-- statement:
--   A protocol for $d$-dimensional states with measurements on at most $k$ copies (Definition 1.1, §4.2) consists of:
--
--   1. internal randomness $\xi$ with an arbitrary probability law, independent of the unknown state $\rho$;
--   2. a standard Borel outcome space;
--   3. in each round $j$, as a measurable function of $(\xi,Y_{<j})$, a block size $t_j\in\{0,1,\dots,k\}$ ($t_j=0$: no measurement, which encodes stopping) and a POVM $M_j(\cdot\mid\xi,Y_{<j})$ on $t_j$ fresh copies whose effects depend measurably on the history.
--
--   The outcome of round $j$ has law $B\mapsto\operatorname{tr}\big(M_j(B\mid\xi,Y_{<j})\,\rho^{\otimes t_j}\big)$ given the history, and only the classical history is carried between rounds. The transcript is $Y=(\xi,Y_1,\dots,Y_T)$, and its law $P_\rho$ is computed by composing these kernels. The protocol uses at most $n$ copies when $\sum_jt_j\le n$ $P_\rho$-almost surely for every state $\rho$.
--
--   An estimator is a measurable map from transcripts to states. It solves Problem 1.2 at accuracy $\varepsilon$ when
--   $$P_\rho\big[D_{\mathrm{tr}}(\rho,\hat\rho(Y))\le\varepsilon\big]\ge\tfrac23\qquad\text{for every state }\rho .$$
--   The weighted block count of a transcript is $S=\sum_{j=1}^Tt_j\sqrt{\min\{t_j,d^2\}}$, and $\operatorname{tr}J_Y(\rho)$ is the Fisher information of the transcript at $\rho$ in the coordinates $\rho+\sum_b\theta_bF_b$: the supremum over measurable finite-valued maps $\varphi$ of the transcript of the Fisher information of $\varphi(Y)$, with outcome probabilities $P_{\rho_\theta}(\varphi^{-1}(a))$.
--
--   This is the class of protocols of the main theorem: adaptive, with random and history-dependent block sizes, early stopping, unlimited classical memory and no quantum memory.
--
--   **Formalization Note** Histories are $(\xi,(y_j)_{j\in\mathbb N})$ with $y_j\in\{\ast\}\sqcup\mathrm{Out}$; a horizon on the number of rounds loses nothing since $T\le n$. The round kernels are carried as data together with the equations that pin them to the Born laws on every state (and to the dummy outcome when $t_j=0$); they exist and are unique on states for every protocol of the source. The file proves (sorry-free) that the transcript law is a Markov kernel, so no degenerate zero law can arise. The copy budget is almost sure, not in expectation.
-- source:
--   Ufuk Keskin, Jason Luo, Mahbod Majid, Matthew Radzihovsky, Tight Lower Bounds for State Tomography with Limited Entanglement, STOC 2027 submission #1625 (October 2026), source.pdf SHA-256 bdd8884c95899a0c563507d1c005e0dee86e418d52478a2e9e6682bb1f9d29c3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1625.pdf, Definition 1.1 and Problem 1.2, printed p.2 / PDF p.4; §4.2 "Measurements and adaptive protocols" and Fact 4.5, printed pp.9–10, 12 / PDF pp.11–12, 14; weighted block count in eqs. (36), (51), (53)

import Mathlib
import Definitions.Def_LimitedEntanglementTomography_LowerBound_Measurement

open scoped ENNReal ComplexOrder
noncomputable section

/-!
# Adaptive protocols with measurements on at most `k` copies

Keskin, Luo, Majid, Radzihovsky, STOC 2027 submission #1625 (October 2026), Definition 1.1 and
Problem 1.2 (printed p.2 / PDF p.4) and the measurement model of §4.2 (printed pp.9–10 /
PDF pp.11–12).

A history is `(ξ, y)` with `ξ` the internal randomness and `y : ℕ → Unit ⊕ Out` the outcomes so
far; slot `j` holds `inr Y_j` once round `j` has measured, and `inl ()` otherwise. Round `j`
reads the current history, chooses a block size `t_j ≤ k` (`t_j = 0` means that no measurement is
made in that round, which encodes stopping), and measures a POVM `M_j(· | ξ, Y_{<j})` on `t_j`
fresh copies. The laws are computed by composing the Born kernels.
-/

namespace LimitedEntanglementTomography.LowerBound

open MeasureTheory ProbabilityTheory Matrix

/-- Definition 1.1 with §4.2: an adaptive protocol on `d`-dimensional states whose measurements
act on at most `k` copies.

* `Seed`, `seedLaw`: the internal randomness `ξ`, an arbitrary probability space, independent of
  the unknown state.
* `Out`: the outcome space, standard Borel.
* `rounds`: a horizon on the number of rounds.
* `blockSize j h`: the number `t_j ∈ {0, …, k}` of fresh copies measured in round `j` given the
  current history `h` (`0`: no measurement); measurable in `h`.
* `meas j t h`: the POVM on `t` copies used in round `j` when `t_j = t`; its effects are
  measurable functions of the history.
* `step j`: the outcome kernel of round `j`, a Markov kernel from `(input matrix, history)`;
  on every state `σ` it is the Born law `B ↦ tr(M_j(B) σ^{⊗t_j})` of `meas j t_j h`
  (`step_born`), and the dummy outcome when `t_j = 0` (`step_stop`). These two equations determine
  it on states. -/
structure Protocol (d k : ℕ) where
  Seed : Type
  Out : Type
  [seedMS : MeasurableSpace Seed]
  [outMS : MeasurableSpace Out]
  outStd : StandardBorelSpace Out
  seedLaw : Measure Seed
  seedLaw_prob : IsProbabilityMeasure seedLaw
  rounds : ℕ
  blockSize : ℕ → Seed × (ℕ → Unit ⊕ Out) → ℕ
  measurable_blockSize : ∀ j, Measurable (blockSize j)
  blockSize_le : ∀ j h, blockSize j h ≤ k
  meas : (j t : ℕ) → Seed × (ℕ → Unit ⊕ Out) → POVM (Fin t → Fin d) Out
  measurable_effect : ∀ j t B, MeasurableSet B → Measurable (fun h => (meas j t h).effect B)
  step : ℕ → Kernel (Op d × (Seed × (ℕ → Unit ⊕ Out))) (Unit ⊕ Out)
  step_markov : ∀ j, IsMarkovKernel (step j)
  step_stop : ∀ j σ h, blockSize j h = 0 → step j (σ, h) = Measure.dirac (Sum.inl ())
  step_born : ∀ j (σ : Op d) h (B : Set Out), WildeQIT.IsDensityOperator σ →
    1 ≤ blockSize j h → MeasurableSet B →
    step j (σ, h) (Sum.inr '' B) = ENNReal.ofReal
      (bornProb (meas j (blockSize j h) h) (ShadowTomography.ClassicalLB.tensorPow σ (blockSize j h)) B)

attribute [instance] Protocol.seedMS Protocol.outMS

namespace Protocol

variable {d k : ℕ}

/-- Histories `(ξ, Y)`; the transcript `Y = (ξ, Y₁, …, Y_T)` is the final history. -/
abbrev History (P : Protocol d k) := P.Seed × (ℕ → Unit ⊕ P.Out)

/-- The history before the first round: the seed and no outcomes. -/
def init (P : Protocol d k) (r : P.Seed) : P.History := (r, fun _ => Sum.inl ())

/-- Writing the outcome of round `j` into slot `j`. -/
def record (P : Protocol d k) (j : ℕ) (p : P.History × (Unit ⊕ P.Out)) : P.History :=
  (p.1.1, Function.update p.1.2 j p.2)

/-- The law of the history after `j` rounds, as a kernel in the input matrix: seed, then the
outcome kernels of rounds `0, …, j − 1` composed in order. -/
def lawUpTo (P : Protocol d k) : ℕ → Kernel (Op d) P.History
  | 0 => Kernel.const _ (P.seedLaw.map P.init)
  | j + 1 => ((P.lawUpTo j) ⊗ₖ (P.step j)).map (P.record j)

/-- Sanity check: the initial history map is measurable. -/
theorem measurable_init (P : Protocol d k) : Measurable P.init := by
  unfold init; fun_prop

/-- Sanity check: recording an outcome is measurable, so `lawUpTo` is a genuine composition. -/
theorem measurable_record (P : Protocol d k) (j : ℕ) : Measurable (P.record j) := by
  unfold record
  refine Measurable.prodMk (measurable_fst.comp measurable_fst) ?_
  rw [measurable_pi_iff]
  intro i
  by_cases hij : i = j
  · subst hij; simpa using measurable_snd
  · simp only [Function.update_of_ne hij]
    exact (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)

/-- Sanity check: every `lawUpTo j`, in particular the transcript law, is a Markov kernel (a
probability measure on transcripts for every input), so no degenerate zero law occurs. -/
instance isMarkovKernel_lawUpTo (P : Protocol d k) (j : ℕ) : IsMarkovKernel (P.lawUpTo j) := by
  induction j with
  | zero =>
    have := P.seedLaw_prob
    have : IsProbabilityMeasure (P.seedLaw.map P.init) :=
      Measure.isProbabilityMeasure_map P.measurable_init.aemeasurable
    simp only [lawUpTo]; infer_instance
  | succ j ih =>
    have := P.step_markov j
    simp only [lawUpTo]
    exact Kernel.IsMarkovKernel.map _ (P.measurable_record j)

/-- The transcript law `P_ρ` of the protocol on input `ρ`. -/
def law (P : Protocol d k) : Kernel (Op d) P.History := P.lawUpTo P.rounds

/-- The history seen by round `j` inside a full transcript: outcomes of rounds `< j` only. -/
def histAt (P : Protocol d k) (j : ℕ) (h : P.History) : P.History :=
  (h.1, fun i => if i < j then h.2 i else Sum.inl ())

/-- The block size `t_j` used in round `j` of the transcript `h`. -/
def blockAt (P : Protocol d k) (j : ℕ) (h : P.History) : ℕ := P.blockSize j (P.histAt j h)

/-- The total number of copies `∑_j t_j` used along the transcript `h`. -/
def copiesUsed (P : Protocol d k) (h : P.History) : ℕ :=
  ∑ j ∈ Finset.range P.rounds, P.blockAt j h

/-- Definition 1.1: the protocol uses at most `n` copies almost surely, under every input
state. -/
def UsesAtMost (P : Protocol d k) (n : ℕ) : Prop :=
  ∀ ρ : Op d, WildeQIT.IsDensityOperator ρ → ∀ᵐ h ∂(P.law ρ), P.copiesUsed h ≤ n

/-- §5 and §7: the weighted block count `∑_{j=1}^T t_j √(min{t_j, d²})` of the transcript `h`. -/
def blockWeight (P : Protocol d k) (h : P.History) : ℝ :=
  ∑ j ∈ Finset.range P.rounds,
    (P.blockAt j h : ℝ) * Real.sqrt (min (P.blockAt j h : ℝ) ((d : ℝ) ^ 2))

/-- Problem 1.2: an estimator, a measurable map from transcripts to states. -/
structure Estimator (P : Protocol d k) where
  toFun : P.History → Op d
  measurable_toFun : Measurable toFun
  isState : ∀ h, WildeQIT.IsDensityOperator (toFun h)

/-- Problem 1.2: `D_tr(ρ, ρ̂) ≤ ε` with probability at least `2/3`, for every input state `ρ`. -/
def Solves (P : Protocol d k) (est : Estimator P) (ε : ℝ) : Prop :=
  ∀ ρ : Op d, WildeQIT.IsDensityOperator ρ →
    ENNReal.ofReal (2 / 3) ≤ P.law ρ {h | traceDist ρ (est.toFun h) ≤ ε}

/-- §4.2: `tr J_Y(ρ)`, the trace of the classical Fisher information of the transcript at the
state `ρ`, in the coordinates `ρ_θ = ρ + ∑ θ_b F_b`, as an extended nonnegative real: the
supremum over measurable maps `φ` of the transcript into a finite set of the Fisher information
of `φ(Y)`, whose outcome probabilities are `P_{ρ_θ}(φ⁻¹(a))`. -/
def fisherTrace (P : Protocol d k) (F : Fin (d ^ 2 - 1) → Op d) (ρ : Op d) : ℝ≥0∞ :=
  ⨆ (m : ℕ) (φ : P.History → Fin m) (_ : Measurable φ),
    finiteFisherTrace F ρ (fun a σ => (P.law σ (φ ⁻¹' {a})).toReal)

end Protocol

end LimitedEntanglementTomography.LowerBound


