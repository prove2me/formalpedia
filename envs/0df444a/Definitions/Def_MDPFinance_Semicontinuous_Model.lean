-- Prove2me | Definitions.Def_MDPFinance_Semicontinuous_Model
-- name    : MDPFinance_Semicontinuous_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:22:27.32532+00:00
-- url     : https://prove2.me/theorems/62936535-a9ed-42d3-b032-4e4721096753
-- title:
--   A (non-stationary) Markov Decision Model with planning horizon $N$
-- statement:
--   A **Markov Decision Model** with planning horizon $N \in \mathbb{N}$ consists of a state space
--   $E$ and an action space $A$, each a measurable space, together with, for every stage
--   $n = 0, 1, \dots, N-1$: a measurable set $D_n \subseteq E \times A$ of admissible state-action
--   pairs (containing the graph of some measurable selection $E \to A$, so $D_n(x) := \{a : (x,a)
--   \in D_n\}$ is always nonempty); a stochastic transition kernel $Q_n(\cdot \mid x,a)$ on $E$; a
--   measurable one-stage reward $r_n : D_n \to \mathbb{R}$; and a measurable terminal reward
--   $g_N : E \to \mathbb{R}$.
--
--   $$
--   (E, A, D_n, Q_n, r_n, g_N)_{n=0,\dots,N-1}.
--   $$
--
--   This is Bäuerle and Rieder's Definition 2.1.1, restated (identically to chunk
--   `02a-model-bellman-equation`'s formalization of the same definition) because drafts in this
--   mission series cannot import one another's Lean files; every other definition and theorem of
--   this mission is built on top of this one item.
--
--   **Formalization Note.** Time is indexed by $\mathbb{N}$ rather than $\mathrm{Fin}\ N$: `D`, `Q`,
--   `r` are total functions of $n$, constrained only for $n < N$; at $n \ge N$ they are
--   unconstrained "junk", which avoids `Fin`-cast bookkeeping without changing any statement's
--   content, since every theorem here only ever quantifies over $n < N$ explicitly.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 14, Definition 2.1.1

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Semicontinuous

/-- A (non-stationary) Markov Decision Model with planning horizon `N` (Bäuerle–Rieder,
Definition 2.1.1, p. 14, PDF 29), restated in this chunk's own sub-namespace since drafts in
this series cannot import one another. See `MDPFinance.Bellman.MarkovDecisionModel`
(chunk `02a`) for the identical definition with the same provenance. -/
structure MarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] (N : ℕ) where
  /-- `D n ⊆ E × A`, the admissible state-action pairs at time `n` (meaningful for `n < N`). -/
  D : ℕ → Set (E × A)
  hD_meas : ∀ n < N, MeasurableSet (D n)
  /-- `D n` contains the graph of a measurable decision rule. -/
  hD_sel : ∀ n < N, ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D n
  /-- The transition kernel `Q_n(·|x,a)`. -/
  Q : ℕ → Kernel (E × A) E
  hQ_prob : ∀ n < N, ∀ xa, IsProbabilityMeasure (Q n xa)
  /-- The one-stage reward `r_n(x,a)`. -/
  r : ℕ → E × A → ℝ
  hr_meas : ∀ n < N, Measurable (r n)
  /-- The terminal reward `g_N(x)`. -/
  g : E → ℝ
  hg_meas : Measurable g

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- `D_n(x) = {a ∈ A | (x,a) ∈ D_n}`, the admissible actions in state `x` at time `n`. -/
def MarkovDecisionModel.Dx (M : MarkovDecisionModel E A N) (n : ℕ) (x : E) : Set A :=
  {a | (x, a) ∈ M.D n}

end MDPFinance.Semicontinuous


