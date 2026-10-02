-- Prove2me | Definitions.Def_MDPFinance_Stationary_Policy
-- name    : MDPFinance_Stationary_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:42:06.056977+00:00
-- url     : https://prove2.me/theorems/0d43803e-2989-41f4-b990-a72d09af6151
-- title:
--   Decision rules and policy sequences for a stationary model
-- statement:
--   A **decision rule** for a stationary model $M$ is a measurable $f : E \to A$ with $f(x) \in
--   D(x)$ for all $x$ (write $F$ for the set of all such). A **policy sequence of length $n$**
--   is $\pi = (f_0,\dots,f_{n-1}) \in F^n$.
--
--   **Formalization Note.** $\pi$ is represented as a total function $\mathbb{N} \to E \to A$;
--   only $\pi(k)$ for $k < n$ is constrained to be a decision rule.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 39, PDF 54, §2.5 introduction (unnumbered)

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- A decision rule for a stationary Markov Decision Model (Bäuerle–Rieder, p. 39, PDF 54): a
measurable `f : E → A` with `f(x) ∈ D(x)` for all `x` (the set of all such is written `F`). -/
def IsDecisionRule (M : StationaryMarkovDecisionModel E A) (f : E → A) : Prop :=
  Measurable f ∧ ∀ x, (x, f x) ∈ M.D

/-- A **policy sequence of length `n`**, `π : ℕ → E → A` with `π k` a decision rule for every
`k < n` (Bäuerle–Rieder's `π = (f_0,…,f_{n-1}) ∈ F^n`, p. 39, PDF 54). `π` is left as a total
function on `ℕ`; only `π k` for `k < n` is constrained. -/
def IsPolicySeq (M : StationaryMarkovDecisionModel E A) (n : ℕ) (π : ℕ → E → A) : Prop :=
  ∀ k < n, IsDecisionRule M (π k)

end MDPFinance.Stationary


