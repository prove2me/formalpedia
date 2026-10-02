-- Prove2me | Definitions.Def_MDPFinance_StructuredModels_Model
-- name    : MDPFinance_StructuredModels_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:32:02.041075+00:00
-- url     : https://prove2.me/theorems/c663c1dd-72a0-4bae-b419-649856fa38e7
-- title:
--   A (non-stationary) Markov Decision Model with planning horizon $N$ (restated)
-- statement:
--   A **Markov Decision Model** with planning horizon $N$ consists of measurable state and action
--   spaces $E$, $A$, and for each stage $n = 0,\dots,N-1$: a measurable set $D_n \subseteq E
--   \times A$ of admissible state-action pairs (containing the graph of some measurable selection
--   $E \to A$); a stochastic transition kernel $Q_n(\cdot \mid x,a)$; a measurable one-stage
--   reward $r_n$; and a terminal reward $g_N$ at time $N$. $D_n(x) := \{a \in A : (x,a) \in D_n\}$
--   denotes the admissible actions at state $x$.
--
--   **Formalization Note.** Identical to `MDPFinance.Bellman.MarkovDecisionModel` of chunk
--   `02a` (Definition 2.1.1); restated here because drafts in this series cannot import one
--   another's definitions.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 14, Definition 2.1.1

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.StructuredModels

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

end MDPFinance.StructuredModels


