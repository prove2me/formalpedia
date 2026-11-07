-- Prove2me | Definitions.Def_QuarticGap_QueryAlg
-- name    : QuarticGap_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:51.91144+00:00
-- url     : https://prove2.me/theorems/04613b86-10bd-499d-b30d-bb49cfd6ade1
-- title:
--   Randomized adaptive classical query algorithms, query counts and output law
-- statement:
--   A **randomized adaptive classical query algorithm** with queries $Q$, answers $\mathrm{Ans}$ and outputs $Y$ is a rule that, given the transcript of past (query, answer) pairs, draws its next action: another query, or halting with an output. Given a law $r(q)$ for the answer to each query $q$, a run is the resulting random process, and $\tau$ is its number of queries, with $\tau = \infty$ when it never halts.
--
--   The item defines
--
--   1. the **tail** $P(\tau > t)$ and the **expected number of queries** $\sum_{t} P(\tau > t)$, as an element of $[0,\infty]$;
--   2. "makes at most $q$ queries over all runs", that is $P(\tau > q) = 0$, for a natural or a real bound $q$;
--   3. the **output probability** of each $j \in Y$ and the **sampling error**, the total variation distance of the output law from a target.
--
--   This is the single classical model of the mission: it covers both the sampling and query access of Definition 2.1 and direct queries to a Boolean function, by changing $r$.
--
--   **Formalization Note** Computation is unrestricted, and the input reaches the algorithm only through the answers. Private coins lose nothing: an algorithm with coins has perfect recall of its transcript, so it has a behaviour strategy with the same law (Kuhn). An algorithm whose runs may not halt has a sub-distribution as output law; the missing mass is an outcome on which the target has no mass, and it counts $\frac12(1 - \sum_j P(\text{output } j))$ in the error.
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Definition 2.3, p.16; §3.3, p.24

import Mathlib
import Definitions.Def_QuarticGap_lenSqDist

open scoped ENNReal

namespace QuarticGap

/-- A randomized adaptive classical query algorithm with queries `Q`, answers `Ans` and outputs `Y`,
as a behaviour strategy: given the transcript of past (query, answer) pairs, it either asks a query
or halts with an output, with a probability law (arXiv:2610.42069, Definition 2.3, p.16, §3.3, p.24).

**Formalization Note** The source says "randomized classical algorithm". Computation is unrestricted
and the step depends on nothing but the transcript, so the input reaches the algorithm only through
the answers. A step with a finite query alphabet loses no generality: an algorithm with private
coins is a mixture of deterministic ones and, having perfect recall of its transcript, has a
behaviour strategy with the same law of (transcript, output) (Kuhn). -/
structure QueryAlg (Q Ans Y : Type*) where
  /-- The law of the next action given the transcript so far. -/
  step : List (Q × Ans) → PMF (Q ⊕ Y)

namespace QueryAlg

variable {Q Ans Y : Type*}

/-- One step of the run: a halted run stays halted; a running one draws its next action and, on a
query `q`, draws the answer from `r q` and extends the transcript. -/
noncomputable def advance (A : QueryAlg Q Ans Y) (r : Q → PMF Ans) :
    List (Q × Ans) ⊕ Y → PMF (List (Q × Ans) ⊕ Y)
  | .inr y => PMF.pure (.inr y)
  | .inl tr => (A.step tr).bind fun o =>
      match o with
      | .inl q => (r q).bind fun a => PMF.pure (.inl (tr ++ [(q, a)]))
      | .inr y => PMF.pure (.inr y)

/-- Law of the state after `t` steps of `A` against the answer law `r`: either the run is still going
with a transcript of exactly `t` queries, or it has halted with an output. -/
noncomputable def law (A : QueryAlg Q Ans Y) (r : Q → PMF Ans) : ℕ → PMF (List (Q × Ans) ⊕ Y)
  | 0 => PMF.pure (.inl [])
  | t + 1 => (law A r t).bind (advance A r)

/-- `P(τ > t)`, where `τ` is the number of queries of a run (`τ = ∞` for a run that never halts).
A transcript at step `t + 1` means that query number `t + 1` was made. -/
noncomputable def tailProb (A : QueryAlg Q Ans Y) (r : Q → PMF Ans) (t : ℕ) : ℝ≥0∞ :=
  ∑' tr, law A r (t + 1) (.inl tr)

/-- Expected number of queries `∑_t P(τ > t)`, in `ℝ≥0∞`, so that it is `∞` when it diverges
(arXiv:2610.42069, Definition 2.3, p.16). -/
noncomputable def expQueries (A : QueryAlg Q Ans Y) (r : Q → PMF Ans) : ℝ≥0∞ :=
  ∑' t, tailProb A r t

/-- "Makes at most `q` queries on this input, over all runs" (arXiv:2610.42069, Definition 2.3, p.16):
no run of positive probability makes more than `q` queries. -/
def MakesAtMost (A : QueryAlg Q Ans Y) (r : Q → PMF Ans) (q : ℕ) : Prop :=
  tailProb A r q = 0

/-- "Makes at most `B` queries over all runs", for a real bound `B`: no run of positive probability
has `τ > B`. A run has `τ ≥ t + 1 > B` exactly when `tailProb t` charges it with `B < t + 1`. No floor
enters, and the negation says that some run of positive probability makes more than `B` queries. -/
def MakesAtMostReal (A : QueryAlg Q Ans Y) (r : Q → PMF Ans) (B : ℝ) : Prop :=
  ∀ t : ℕ, B < (t : ℝ) + 1 → tailProb A r t = 0

/-- Probability that a run halts with output `j`. Halted runs are absorbed, so `law t (inr j)` is
nondecreasing in `t` and the supremum is its limit. -/
noncomputable def outProb (A : QueryAlg Q Ans Y) (r : Q → PMF Ans) (j : Y) : ℝ :=
  (⨆ t, law A r t (.inr j)).toReal

/-- Total variation distance between the output law of `A` and the distribution `p`
(arXiv:2610.42069, Definition 2.3, p.16).

**Formalization Note** The output law of a general algorithm can be a sub-distribution, when runs
fail to halt with positive probability. The missing mass is an outcome of its own, on which `p` puts
no mass, so it counts `½ (1 − ∑_j outProb j)`. For an algorithm that halts almost surely this is `TV`
as in the source. -/
noncomputable def sampleErr [Fintype Y] (A : QueryAlg Q Ans Y) (r : Q → PMF Ans) (p : Y → ℝ) : ℝ :=
  tv (outProb A r) p + (1 / 2) * (1 - ∑ j, outProb A r j)

end QueryAlg

end QuarticGap


