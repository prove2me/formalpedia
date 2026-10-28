-- Prove2me | Definitions.Def_Kurodoko_NPC_OneInThreeSat
-- name    : Kurodoko_NPC_OneInThreeSat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:33:08.491984+00:00
-- url     : https://prove2.me/theorems/0cdde6b0-2b72-4fbb-9313-b33a2911bd42
-- title:
--   §3, p. 695 — one-in-three SAT as a language over the published CNF code
-- statement:
--   This file defines one-in-three satisfiability, the problem the hardness proof of Kölker (2012, §3) reduces from (Schaefer 1978).
--
--   A formula $F$ is a list of clauses, each a list of literals $x$ or $\neg x$ over variables $x\in\mathbb N$. An assignment $\tau:\mathbb N\to\{\mathrm{true},\mathrm{false}\}$ is a **one-in-three assignment** of $F$ when in every clause exactly one literal occurrence is true:
--   $$\#\{\,j : \text{the } j\text{-th literal of } C \text{ is true under } \tau\,\}=1\qquad\text{for every clause } C\in F.$$
--   A literal that appears twice in a clause is counted twice. The **one-in-three SAT language** is the set of codes of formulas whose clauses all have exactly three literals and which have a one-in-three assignment.
--
--   **Formalization Note** Formulas, literals and the code `encodeCNF` (sign, then the variable in unary, clauses closed by an end marker) are those of the published `CookPvsNP_defs`. Negated literals and repeated variables in a clause are allowed.
-- source:
--   Kölker, Kurodoko is NP-Complete, J. Inf. Process. 20(3) (2012), p. 695 (PDF 2), §3: "by showing how to compute a reduction from one-in-three-SAT. This problem was shown to be NP-complete in Ref. [5]"

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace Kurodoko.NPC

open CookPvsNP

/-! # One-in-three SAT (Kölker 2012, §3, p. 695; Schaefer 1978)

A formula is a published `CookPvsNP.CNF`: a list of clauses, each a list of literals
`(b, x)` (`b = true` for the variable `x`, `b = false` for its negation). -/

/-- `F` has a one-in-three assignment: some truth assignment makes, in every clause, exactly one
literal occurrence true (a literal repeated in a clause is counted once per occurrence). -/
def OneInThree (F : CNF) : Prop :=
  ∃ τ : ℕ → Bool, ∀ C ∈ F, (C.filter fun ℓ => decide (τ ℓ.2 = ℓ.1)).length = 1

/-- The one-in-three SAT language: codes `encodeCNF F` of formulas `F` whose clauses all have
exactly three literals and which have a one-in-three assignment. -/
def oneInThreeLang : Lang SatSym :=
  { s | ∃ F : CNF, (∀ C ∈ F, C.length = 3) ∧ OneInThree F ∧ s = encodeCNF F }

end Kurodoko.NPC


