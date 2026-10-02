-- Prove2me | Definitions.Def_MDPFinance_Bellman_History
-- name    : MDPFinance_Bellman_History
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:07:43.022758+00:00
-- url     : https://prove2.me/theorems/be25f920-f88c-404f-b339-b1a4e86afbea
-- title:
--   Histories and history-dependent policies
-- statement:
--   The **history space** $H_n$ records everything observed up to time $n$: $H_0 := E$ and
--   $H_n := H_{n-1} \times A \times E$ for $n \ge 1$, so an element $h_n = (x_0, a_0, x_1, \dots,
--   x_n) \in H_n$ is a full history of states and actions up to time $n$. The **current state**
--   $x_n$ is recovered from $h_n$ by the projection $\mathrm{histState}_n : H_n \to E$.
--
--   A **history-dependent decision rule at stage $n$** (Definition 2.2.2a) is a measurable map
--   $f_n : H_n \to A$ with $f_n(h_n) \in D_n(x_n)$ for every history $h_n$ with current state $x_n$
--   — i.e. the chosen action may depend on the whole past, not only on the current state. A
--   **history-dependent $N$-stage policy** (Definition 2.2.2b) is a sequence
--   $\pi = (f_0, \dots, f_{N-1})$ of such rules; the set of all history-dependent $N$-stage policies
--   is denoted $\Pi_N$.
--
--   This vocabulary makes precise the sense in which the ordinary (Markov) policies of Definition
--   2.1.5 are a restricted class: $F_0 \times \cdots \times F_{N-1} \subseteq \Pi_N$, since every
--   state-dependent decision rule $f_n : E \to A$ gives rise to the history-dependent rule
--   $h_n \mapsto f_n(x_n)$. Theorem 2.2.3 (not part of this mission's milestone list — see
--   `MODERATION_NOTES.md`) shows that this restriction is lossless: Markov policies already attain
--   the supremum of the expected reward over all of $\Pi_N$.
--
--   **Formalization Note.** `Hist E A n` is defined by structural recursion on $n$ with a
--   correspondingly recursive `MeasurableSpace` instance; a history-dependent policy is a dependent
--   function over `n : Fin N`, since the domain $H_n$ genuinely depends on $n$ (unlike a Markov
--   policy, which can be encoded as a single $\mathbb{N}$-indexed function into the fixed type
--   $E \to A$).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 18, Definition 2.2.2

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

universe u

variable (E A : Type u) [MeasurableSpace E] [MeasurableSpace A]

/-- The history space `H_n` (Bäuerle–Rieder, p. 18, PDF 33): `H_0 := E`,
`H_n := H_{n-1} × A × E`. An element of `Hist E A n` is a history
`h_n = (x_0, a_0, x_1, …, x_n)` up to time `n`. -/
def Hist : ℕ → Type _
  | 0 => E
  | (n + 1) => Hist n × A × E

instance instHistMeasurableSpace : (n : ℕ) → MeasurableSpace (Hist E A n)
  | 0 => ‹MeasurableSpace E›
  | (n + 1) =>
      @Prod.instMeasurableSpace (Hist E A n) (A × E) (instHistMeasurableSpace n)
        (@Prod.instMeasurableSpace A E ‹MeasurableSpace A› ‹MeasurableSpace E›)

variable {E A}

/-- The current state `x_n` extracted from a history `h_n ∈ H_n`. -/
def histState : (n : ℕ) → Hist E A n → E
  | 0, x => x
  | (_ + 1), (_, _, x) => x

lemma measurable_histState (n : ℕ) : Measurable (histState (E := E) (A := A) n) := by
  induction n with
  | zero => exact measurable_id
  | succ n _ => exact measurable_snd.comp measurable_snd

variable {N : ℕ}

/-- A history-dependent decision rule at stage `n` (Bäuerle–Rieder, Definition 2.2.2a, p. 18,
PDF 33): a measurable `f : H_n → A` with `f(h_n) ∈ D_n(x_n)` for every history `h_n` with current
state `x_n`. -/
def IsHistDecisionRule (M : MarkovDecisionModel E A N) (n : ℕ) (f : Hist E A n → A) : Prop :=
  Measurable f ∧ ∀ h, (histState n h, f h) ∈ M.D n

/-- A history-dependent `N`-stage policy (Bäuerle–Rieder, Definition 2.2.2b, p. 18, PDF 33): a
sequence `π = (f_0, …, f_{N-1})` where `f_n` is a history-dependent decision rule at stage `n`.
`Π_N` in the book's notation. Formalized as a dependent function over `n < N` rather than a
single `ℕ`-indexed function, since the domain `Hist E A n` itself depends on `n`. -/
def HistPolicy (M : MarkovDecisionModel E A N) : Type _ :=
  (n : Fin N) → {f : Hist E A n → A // IsHistDecisionRule M n f}

end MDPFinance.Bellman


