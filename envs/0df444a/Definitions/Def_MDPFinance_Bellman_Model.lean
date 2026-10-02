-- Prove2me | Definitions.Def_MDPFinance_Bellman_Model
-- name    : MDPFinance_Bellman_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:06:10.267155+00:00
-- url     : https://prove2.me/theorems/1f99b4af-019a-46bf-b723-b327e3e0cab8
-- title:
--   A (non-stationary) Markov Decision Model with planning horizon $N$
-- statement:
--   This definition fixes the vocabulary of the whole chapter: a finite-horizon Markov Decision
--   Model, following Bäuerle and Rieder's Definition 2.1.1.
--
--   A **Markov Decision Model** with planning horizon $N \in \mathbb{N}$ consists of a state space
--   $E$ and an action space $A$, each a measurable space, together with, for every stage
--   $n = 0, 1, \dots, N-1$:
--
--   - a measurable set $D_n \subseteq E \times A$ of admissible state-action pairs, required to
--     contain the graph of some measurable map $E \to A$ (so that the set $D_n(x) := \{a \in A :
--     (x,a) \in D_n\}$ of admissible actions in state $x$ is always nonempty and a measurable
--     selection exists);
--   - a stochastic transition kernel $Q_n(\cdot \mid x, a)$ on $E$, defined for $(x,a) \in D_n$,
--     giving the law of the state at time $n+1$;
--   - a measurable one-stage reward function $r_n : D_n \to \mathbb{R}$;
--
--   and, at the terminal time $N$, a measurable terminal reward function $g_N : E \to \mathbb{R}$.
--
--   $$
--   (E, A, D_n, Q_n, r_n, g_N)_{n=0,\dots,N-1}.
--   $$
--
--   This is the primitive data every later result of the chapter is stated in terms of: the value
--   function, the Bellman equation, and the notion of an optimal policy are all built from
--   $(D_n, Q_n, r_n, g_N)$ alone.
--
--   **Formalization Note.** Time is indexed by $\mathbb{N}$ rather than by $\mathrm{Fin}\ N$: `D`,
--   `Q`, `r` are total functions of $n : \mathbb{N}$, but only their values at $n < N$ are
--   constrained by the structure's fields (`hD_meas`, `hD_sel`, `hQ_prob`, `hr_meas`); at $n \ge N$
--   they are unconstrained "junk". This avoids `Fin`-cast bookkeeping in the many nested recursions
--   built on top of this model later in the mission, at no cost to fidelity for $n < N$, which is
--   the only range the book ever uses.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 14, Definition 2.1.1

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

/-- `IM E` (Bäuerle–Rieder p. 19, PDF 34): the measurable functions `E → [-∞, ∞)`, i.e. `EReal`
valued, measurable, and never equal to `⊤`. Value functions and solutions of the Bellman
equation live here rather than in `E → ℝ`, since a supremum over unboundedly bad rewards can be
`-∞`. -/
def IM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

/-- A (non-stationary) Markov Decision Model with planning horizon `N` (Bäuerle–Rieder,
Definition 2.1.1, p. 14, PDF 29). Time is indexed by `ℕ` rather than `Fin N`; only `n < N`
carries meaning; `D`, `Q`, `r` are unconstrained (junk) for `n ≥ N`. `D n` is the measurable set
of admissible state-action pairs at time `n`, required to contain the graph of some measurable
decision rule; `Q n` is the stochastic transition kernel; `r n` the one-stage reward; `g` the
terminal reward at time `N`. -/
structure MarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] (N : ℕ) where
  /-- `D n ⊆ E × A`, the admissible state-action pairs at time `n` (meaningful for `n < N`). -/
  D : ℕ → Set (E × A)
  hD_meas : ∀ n < N, MeasurableSet (D n)
  /-- `D n` contains the graph of a measurable decision rule (Bäuerle–Rieder's standing
  assumption on `D_n`, ensuring `F_n` is nonempty). -/
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

end MDPFinance.Bellman


