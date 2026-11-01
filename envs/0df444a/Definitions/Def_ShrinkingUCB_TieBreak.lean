-- Prove2me | Definitions.Def_ShrinkingUCB_TieBreak
-- name    : ShrinkingUCB_TieBreak
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:35.619799+00:00
-- url     : https://prove2.me/theorems/19aa5cb6-fc2c-49b4-9d03-9ed62e2b145b
-- title:
--   Tie-breaking rule on the observed history
-- statement:
--   The **observation** of a period is the set of pairs $(i,r_{t,i})$, $i\in S_t$: the offered products with their outcomes. The **observed history** is the list of the observations of the past periods.
--
--   A **tie-breaking rule** is a deterministic function that receives the observed history, the products selected so far in the current period (in order) and a set $C$ of tied products, and returns a member of $C$ whenever $C$ is nonempty.
--
--   It resolves the phrase "add a product $j\in\arg\max$" in step 2(b)ii of ConsUCB. A rule receives no unobserved outcome, which is how the decision in period $t$ is "based on all the past information".
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, §2, p.9; §4.1, p.15

import Mathlib

namespace ShrinkingUCB

/-- The observation of one period: the offered products paired with their outcomes. The set
`S_t` and the outcomes `r_{t,i}`, `i ∈ S_t`, can be read off it, and nothing else about the
table. -/
abbrev Observation (N : ℕ) : Type := Finset (Fin N × Bool)

/-- The observed history: the observations of the past periods, oldest first. -/
abbrev History (N : ℕ) : Type := List (Observation N)

/-- A tie-breaking rule for step 2(b)ii of ConsUCB (arXiv:1903.07844v2, p.15), "add a product
`j ∈ arg max`": a deterministic function of the observed history, the selections made so far in
the current period, in order, and the tied set, returning a member of the tied set when that set
is nonempty.

**Formalization Note.** A rule receives neither the outcome `ω` nor any unobserved entry of the
reward table, which is p.9's "based on all the past information". -/
structure TieBreak (N : ℕ) where
  /-- The product chosen from a tied set. -/
  choose : History N → List (Fin N) → Finset (Fin N) → Fin N
  choose_mem : ∀ h s C, C.Nonempty → choose h s C ∈ C

end ShrinkingUCB


