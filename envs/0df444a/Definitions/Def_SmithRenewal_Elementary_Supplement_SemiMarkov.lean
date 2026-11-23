-- Prove2me | Definitions.Def_SmithRenewal_Elementary_Supplement_SemiMarkov
-- name    : SmithRenewal_Elementary_Supplement_SemiMarkov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:55:25.682627+00:00
-- url     : https://prove2.me/theorems/4410fe95-a501-404e-829e-a97b4e20b8c5
-- title:
--   §2.2 — countable semi-Markov construction, occupation, entry probability, and elapsed recurrence
-- statement:
--   Let $S$ be the countable state set and $p_{ij}$ the stochastic matrix of its embedded chain. For every active edge $i\to j$, let $\Omega_{ij}$ be a probability law of a finite nonnegative wait, with $\Omega_{ij}(\{0\})<1$. The holding law may depend on both endpoints and may have infinite mean. Starting from any initial entry distribution $\alpha$, independently draw fresh next-state choices and waits at each step. If $J_n$ is the state at step $n$, choose $J_{n+1}$ with probabilities $p_{J_n,j}$ and then wait $D_n$ with law $\Omega_{J_n,J_{n+1}}$. Put $T_0=0$ and $T_n=\sum_{k<n}D_k$. The state occupation event is
--
--   $$
--   \{x_t\in A_\mu\}=\bigcup_{n\ge0}\{J_n=\mu,\ T_n\le t<T_{n+1}\}.
--   $$
--
--   For a target $\mu$, define the edge and state holding means, eventual entry probability, and elapsed recurrence mean by
--
--   $$
--   m_{\mu\nu}=\int u\,\Omega_{\mu\nu}(du),\qquad
--   m_\mu=\sum_\nu p_{\mu\nu}m_{\mu\nu},\qquad
--   Q_\mu=\mathbb P_\alpha(\exists n\ge0:J_n=\mu),\qquad
--   l_\mu=\mathbb E_\mu T_{\tau_\mu^+},\quad
--   \tau_\mu^+=\inf\{n\ge1:J_n=\mu\}.
--   $$
--
--   Non-return has elapsed duration $+\infty$. Persistence means $\mathbb P_\mu(\tau_\mu^+<\infty)=1$; nonperiodicity means its elapsed return duration is not almost surely an integer multiple of any common positive real span. These definitions supply the actual process probabilities and recurrence quantities used by the companion theorem, without assuming a limit formula.
--
--   **Formalization Note** The general stochastic chain is imported from the published countable-chain definition. The sample law is an explicit product of an initial state, fresh row choices, and fresh edge waits. Atoms at zero and self-transitions are retained. Half-open holding intervals implement the after-transition convention; after an accumulation of epochs a cemetery value is used, so no original state is occupied. Means and probabilities take values in $[0,\infty]$, and no global nonexplosion condition is assumed. Auxiliary laws on inactive edges may be arbitrary probability measures and never affect the process.
-- source:
--   Smith, Renewal Theory and Its Ramifications, J. R. Statist. Soc. B 20(2):243–283 (1958), DOI 10.1111/j.2517-6161.1958.tb00294.x, §2.2, pp. 260–261, unnumbered construction and recurrence definitions; §2.1, p. 259, periodicity convention

import Mathlib
import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace SmithRenewal.Elementary.Supplement

/-- Smith, Renewal Theory and Its Ramifications (1958), §2.2, pp. 260–261 (PDF 18–19),
unnumbered semi-Markov construction and standing wait assumptions.

**Formalization Note** The general embedded chain is the published `Chain S` (stochastic
PMF rows). Edge laws are probability measures on finite nonnegative reals. Only active edges
must not be concentrated at zero. Inactive-edge laws are immaterial and can be filled with
any probability law. No finite-mean or nonexplosion condition is built into this object. -/
structure SemiMarkov (S : Type*) where
  transition : KellyStochasticNetworks.MaxWeight.Chain S
  wait : S → S → Measure ℝ≥0
  wait_probability : ∀ i j, IsProbabilityMeasure (wait i j)
  wait_nonzero : ∀ i j, transition i j ≠ 0 → wait i j {0} < 1

/-- Independent random tapes: an initial state, a fresh next-state draw for each step/state,
and a fresh wait draw for each step/ordered edge. Smith §2.2, pp. 260–261.
**Formalization Note** Unused tape coordinates have no effect on the constructed path. -/
abbrev Sample (S : Type*) := S × ((ℕ × S → S) × (ℕ × S × S → ℝ≥0))

variable {S : Type*} [MeasurableSpace S]

/-- Smith §2.2, p. 261: independent successive selections of states and waits.
**Formalization Note** This is an actual product probability law, rather than an axiom about
occupation probabilities. `α` is the arbitrary initial entry distribution at time zero. -/
noncomputable def law (M : SemiMarkov S) (α : PMF S) : Measure (Sample S) :=
  α.toMeasure.prod
    ((Measure.infinitePi (fun k : ℕ × S => (M.transition k.2).toMeasure)).prod
      (Measure.infinitePi (fun k : ℕ × S × S => M.wait k.2.1 k.2.2)))

/-- The construction uses genuine probability products (Smith §2.2, pp. 260–261).
**Formalization Note** Supplies the elementary probability-measure instance for `law`. -/
instance law_probability (M : SemiMarkov S) (α : PMF S) : IsProbabilityMeasure (law M α) := by
  have : ∀ i j, IsProbabilityMeasure (M.wait i j) := M.wait_probability
  unfold law
  infer_instance

/-- Smith §2.2, pp. 260–261: recursively select the next state from the current row.
**Formalization Note** `state ω 0` is the state entered at time zero; visited states are
Markov dependent even though the random tape coordinates used for fresh draws are independent. -/
def state (ω : Sample S) : ℕ → S
  | 0 => ω.1
  | n + 1 => ω.2.1 (n, state ω n)

/-- Smith §2.2, p. 261: the wait in the present state depends on the chosen next state.
**Formalization Note** Lifetime `n` belongs to the edge `state n → state (n+1)`. -/
def lifetime (n : ℕ) (ω : Sample S) : ℝ :=
  ω.2.2 (n, state ω n, state ω (n + 1))

/-- Smith §2.2, p. 261: transition epochs, starting with an entry at zero.
**Formalization Note** These are the epochs of the constructed semi-Markov path, not an
i.i.d. renewal sequence. No renewal-process predicate is assumed for these waits. -/
noncomputable def epoch (n : ℕ) (ω : Sample S) : ℝ :=
  ∑ k ∈ Finset.range n, lifetime k ω

/-- Smith §2.2, p. 261: the state occupied at time `t`.
**Formalization Note** The half-open intervals select the state after all finitely many
zero-time transitions at an epoch. If epochs accumulate and no finite holding interval
contains `t`, the path is in a cemetery state, so no original state is occupied. -/
def Occupies (μ : S) (t : ℝ) (ω : Sample S) : Prop :=
  ∃ n : ℕ, state ω n = μ ∧ epoch n ω ≤ t ∧ t < epoch (n + 1) ω

/-- Smith §2.2, p. 261: `prob {x_t ∈ A_μ}`, from the constructed path law.
**Formalization Note** A probability is retained in `ℝ≥0∞`; no possibly infinite quantity
is converted to a real number. Negative times have empty occupation events. -/
noncomputable def occupation (M : SemiMarkov S) (α : PMF S) (μ : S) (t : ℝ) : ℝ≥0∞ :=
  law M α {ω | Occupies μ t ω}

/-- Smith §2.2, p. 261: `m_μν = E T_μν`.
**Formalization Note** A finite random wait may have infinite expectation. -/
noncomputable def edgeMean (M : SemiMarkov S) (μ ν : S) : ℝ≥0∞ :=
  ∫⁻ u : ℝ≥0, (u : ℝ≥0∞) ∂M.wait μ ν

/-- Smith §2.2, p. 261: `m_μ = Σ_ν p_μν E T_μν`.
**Formalization Note** The nonnegative integral and series allow infinite means, and inactive
edges contribute zero even if their arbitrary auxiliary law has infinite mean. -/
noncomputable def meanWait (M : SemiMarkov S) (μ : S) : ℝ≥0∞ :=
  ∑' ν, M.transition μ ν * edgeMean M μ ν

/-- Smith §2.2, p. 261: `Q_μ`, probability of an entry in finite time, counting time zero.
**Formalization Note** Each finite index has finite elapsed time. No first entry is presumed
certain; a visit after an accumulation of infinitely many transitions is not a finite entry. -/
noncomputable def entryProbability (M : SemiMarkov S) (α : PMF S) (μ : S) : ℝ≥0∞ :=
  law M α {ω | ∃ n : ℕ, state ω n = μ}

/-- Smith §2.2, p. 261: elapsed time to the first strictly subsequent entry into `μ`.
**Formalization Note** The least positive index counts self-transitions and zero-duration
returns. Non-return has value `∞`, without using a default natural-number hitting index. -/
noncomputable def returnTime (μ : S) (ω : Sample S) : ℝ≥0∞ := by
  classical
  exact if h : ∃ n : ℕ, 0 < n ∧ state ω n = μ then
    ENNReal.ofReal (epoch (Nat.find h) ω) else ∞

/-- Smith §2.2, p. 261: `l_μ`, expected elapsed recurrence time starting with an entry into `μ`.
**Formalization Note** This is not an expected number of chain steps; both non-return and an
infinite mean of finite return durations are represented by the extended value `∞`. -/
noncomputable def meanReturn (M : SemiMarkov S) (μ : S) : ℝ≥0∞ :=
  ∫⁻ ω, returnTime μ ω ∂law M (PMF.pure μ)

/-- Smith §2.2, p. 261: persistence of the target in the embedded chain.
**Formalization Note** Persistence is probability-one return at a positive chain index; it
places no bound on the expected number of steps or on the elapsed-time return mean. -/
def Persistent (M : SemiMarkov S) (μ : S) : Prop :=
  law M (PMF.pure μ) {ω | ∃ n : ℕ, 0 < n ∧ state ω n = μ} = 1

/-- Smith §2.2, p. 261, hypothesis (i), read with §2.1, p. 259: nonperiodic entry events.
**Formalization Note** Periodicity is concentration of return durations on the nonnegative
integer multiples of a positive real span. It is not the period of the embedded chain,
and no density or absolute-continuity hypothesis is imposed. Used only for persistent targets. -/
def Nonperiodic (M : SemiMarkov S) (μ : S) : Prop :=
  ∀ d : ℝ, 0 < d → ¬ (∀ᵐ ω ∂law M (PMF.pure μ),
    ∃ k : ℕ, returnTime μ ω = ENNReal.ofReal ((k : ℝ) * d))

end SmithRenewal.Elementary.Supplement


