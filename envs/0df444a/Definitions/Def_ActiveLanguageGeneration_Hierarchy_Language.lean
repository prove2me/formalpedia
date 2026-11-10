-- Prove2me | Definitions.Def_ActiveLanguageGeneration_Hierarchy_Language
-- name    : ActiveLanguageGeneration_Hierarchy_Language
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T21:15:52.304324+00:00
-- url     : https://prove2.me/theorems/28b70987-cdbd-471c-87e6-b19089d2e5f5
-- title:
--   Infinite languages, finite-history interaction and R/NR correctness
-- statement:
--   Let $U$ be a string universe. A language $L$ is an infinite subset of $U$, a language collection $C$ is an arbitrary family of such languages, and a generator is a deterministic function $G:U^\star\to U$ of the finite received history. A full enumeration $x_1,x_2,\ldots$ of $L$ is injective and has range exactly $L$.
--
--   At time $t\ge1$, write $b_t=G(x_1,\ldots,x_t)$, $S_t=\{x_1,\ldots,x_t\}$ and $B_{t-1}=\{b_j:1\le j<t\}$. The two correctness conventions are
--
--   $$
--   \mathrm{R}:\ b_t\in L\setminus S_t,\qquad
--   \mathrm{NR}:\ b_t\in L\setminus(S_t\cup B_{t-1}).
--   $$
--
--   Every previous output contributes to $B_{t-1}$, including incorrect outputs and those before eventual correctness starts. A future input may equal an earlier output. These definitions supply the common operational interface for both hierarchy results. They assert no generator exists and assume no family is countable.
--
--   **Formalization Note** A language is a subtype of sets carrying infinitude, collections are sets of languages, and histories are lists, oldest first. Stream index $n$ denotes paper time $t=n+1$; the input history includes indices $0$ through $n$, and prior outputs use exactly $j<n$. The hierarchy theorems impose the source's countably infinite universe assumption; these operations themselves make sense on any type. There is no computational resource bound or target-language input.
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, §2 and Definitions 2.1, 2.2, 2.7, printed pp.4–6 (PDF pp.5–7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Mathlib

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy

/-- Section 2, printed p.4: a language is an infinite subset of the string universe.
The hierarchy theorems assume `[Countable U] [Infinite U]`, exactly the standing universe assumption. -/
abbrev Language (U : Type) := {L : Set U // L.Infinite}

/-- An arbitrary family of infinite languages; no countability assumption on the family. -/
abbrev LanguageCollection (U : Type) := Set (Language U)

/-- One deterministic function of the received finite history, oldest example first.
No target-language identifier, oracle, future input, or computability restriction is supplied. -/
abbrev Generator (U : Type) := List U → U

/-- A full presentation has no repetitions and enumerates every member of the language. -/
def IsEnumeration {U : Type} (L : Language U) (x : ℕ → U) : Prop :=
  Function.Injective x ∧ Set.range x = L.val

/-- At index `n` the paper's time is `t = n + 1`: exactly `n + 1` inputs have arrived. -/
def inputHistory {U : Type} (x : ℕ → U) (n : ℕ) : List U :=
  (List.range (n + 1)).map x

/-- The output after the currently received example, with no access to later inputs. -/
def outputAt {U : Type} (G : Generator U) (x : ℕ → U) (n : ℕ) : U :=
  G (inputHistory x n)

/-- All examples received through index `n`, inclusive. -/
def seenInputs {U : Type} (x : ℕ → U) (n : ℕ) : Set U :=
  {z | ∃ j ≤ n, x j = z}

/-- Every earlier output, including incorrect outputs before any success threshold.
There is no output for the empty history in this set. -/
def priorOutputs {U : Type} (G : Generator U) (x : ℕ → U) (n : ℕ) : Set U :=
  {z | ∃ j < n, outputAt G x j = z}

/-- Section 2.4: R permits repeated outputs, NR excludes every earlier output. -/
inductive Repetition where
  | R
  | NR

/-- Definitions 2.1, 2.2, 2.7: correctness after input `n + 1`.
A future input may equal an earlier output. No global freshness condition is imposed. -/
def CorrectAt {U : Type} (mode : Repetition) (G : Generator U)
    (L : Language U) (x : ℕ → U) (n : ℕ) : Prop :=
  match mode with
  | .R => outputAt G x n ∈ L.val \ seenInputs x n
  | .NR => outputAt G x n ∈ L.val \ (seenInputs x n ∪ priorOutputs G x n)

end ActiveLanguageGeneration.Hierarchy


