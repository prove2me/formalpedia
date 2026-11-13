-- Prove2me | Definitions.Def_RvsCert_randQC
-- name    : RvsCert_randQC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:21.186502+00:00
-- url     : https://prove2.me/theorems/a5e84d66-750c-4591-8cf6-d8a51350893c
-- title:
--   Bounded-error randomized query complexity $R(f)$
-- statement:
--   A **randomized decision tree** is a probability distribution over deterministic decision trees, each of which queries single input bits adaptively and outputs a bit. For a Boolean function $f$, $R(f)$ is the least $T$ such that some randomized decision tree
--
--   1. makes at most $T$ queries on every input, for every tree in its support, and
--   2. outputs $f(x)$ with probability at least $2/3$ on **every** input $x$.
--
--   $R(f)$ takes values in $\mathbb N\cup\{\infty\}$, with $\infty$ if no such $T$ exists.
--
--   **Formalization Note** Built on the published `QAlgorithms.RandDecisionTree`, `RandMakesAtMost` and `successProb`. The value lies in `ℕ∞`, so an upper bound $R(f)\le T$ with $T$ finite is never vacuous.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Theorem 1, p.1; Lemma 3, p.3 (standard notion, [BdW02])

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical

namespace RvsCert

open scoped ENNReal

/-- **Bounded-error randomized query complexity** `R(f)` (standard, [BdW02]; Theorem 1, p.1 and
Lemma 3, p.3 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): the least `T` such that some randomized decision tree
(a probability distribution over deterministic decision trees querying single bits) makes at most
`T` queries on every input and every tree of its support, and outputs `f x` with probability at
least `2/3` on **every** input `x`.

**Formalization Note.** Uses the published `QAlgorithms.RandDecisionTree`, `RandMakesAtMost`
(worst case over the support and inputs) and `successProb`. The value lies in `ℕ∞`: an empty
feasible set gives `⊤`, so an upper bound `randQC f ≤ T` is never vacuous. -/
noncomputable def randQC {ι : Type} (f : (ι → Bool) → Bool) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : ∃ R : QAlgorithms.RandDecisionTree ι Bool Bool,
      QAlgorithms.RandMakesAtMost R T ∧ ∀ x : ι → Bool, 2 / 3 ≤ QAlgorithms.successProb R x (f x)),
    (T : ℕ∞)

end RvsCert


