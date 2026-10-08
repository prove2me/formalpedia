-- Prove2me | Definitions.Def_SchedComplexity_TotalCompletion_Knapsack
-- name    : SchedComplexity_TotalCompletion_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:29:08.434996+00:00
-- url     : https://prove2.me/theorems/cf9639d7-e439-4dcb-953a-28c080db6339
-- title:
--   KNAPSACK (Theorem 2(b)): positive integers $a_1,\dots,a_t,b$; is there $S\subseteq T$ with $\sum_{j\in S}a_j=b$? and its binary language
-- statement:
--   **KNAPSACK** (Brucker, Lenstra and Rinnooy Kan, Theorem 2(b)). An instance consists of positive integers $a_1,\dots,a_t$ and $b$. Write $T=\{1,\dots,t\}$. The instance has a **solution** if there is a subset $S\subseteq T$ with
--
--   $$\sum_{j\in S} a_j = b.$$
--
--   The **KNAPSACK language** consists of the binary codes of the instances that have a solution. The code of an instance is the sequence of numbers $b, a_1, \dots, a_t$, each written in binary and followed by a separator symbol, over the four-letter alphabet of the published definition `ProjSchedTW.Complexity.Encoding`. The code determines the instance. Codes of tuples in which some entry is $0$ are not in the language.
--
--   KNAPSACK is the source problem of most reductions in Theorem 4 of the paper; this language is the domain of the reduction to single-machine total completion time with one release date.
--
--   **Formalization Note** Items are indexed by `Fin t` (0-based: index $i$ is the paper's $a_{i+1}$). The paper writes $S\subset T$ for (non-strict) inclusion. Positivity of every entry is part of the language, as in the paper; the published `subsetSumLang` of the Neumann–Schwindt–Zimmermann formalization allows zero entries and is therefore not reused.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 14, Theorem 2(b)

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_Tardiness_Knapsack

namespace SchedComplexity.TotalCompletion

open ProjSchedTW.Complexity (BSym encNats)

/-- KNAPSACK (Brucker, Lenstra & Rinnooy Kan 1975, Theorem 2(b), p. 14): the numbers
`a_1, …, a_t, b` are an instance when they are positive integers. The items are indexed by
`Fin t` (0-based: index `i` is the paper's `a_{i+1}`). -/
def IsKnapsackInstance {t : ℕ} (a : Fin t → ℕ) (b : ℕ) : Prop :=
  (∀ i, 0 < a i) ∧ 0 < b

/-- The code of a KNAPSACK instance: the numbers `b, a_1, …, a_t` in binary (`encNats`). The
code determines `(t, a, b)`: separators delimit the numbers, the first is `b`, and the number of
remaining ones is `t`. -/
def knapsackCode {t : ℕ} (a : Fin t → ℕ) (b : ℕ) : List BSym :=
  encNats (b :: List.ofFn a)

/-- The KNAPSACK language: codes of the instances (all of `a_1, …, a_t, b` positive) that have a
solution. Codes of instances with a zero entry are not in the language. -/
def knapsackLang : CookPvsNP.Lang BSym :=
  { x | ∃ (t : ℕ) (a : Fin t → ℕ) (b : ℕ),
      IsKnapsackInstance a b ∧ SchedComplexity.Tardiness.KnapsackYes a b ∧ x = knapsackCode a b }

end SchedComplexity.TotalCompletion


