-- Prove2me | Definitions.Def_DetCCHard_Is3CNF
-- name    : DetCCHard_Is3CNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:21.903432+00:00
-- url     : https://prove2.me/theorems/0fea9487-32d1-4aac-a388-10a9e47c4fc5
-- title:
--   3-CNF formulas and their number of variables
-- statement:
--   A **3-CNF formula** is a CNF formula (published `CookPvsNP.CNF`: a list of clauses, each a list of literals) in which every clause has at most three literals. The **number of variables** $N$ of a formula is the number of distinct variable indices occurring in it; it is the size parameter of sparse 3-SAT (§4.1: $N$ variables and at most $c_s N$ clauses).
--
--   **Formalization Note** "At most three" covers the "exactly three" reading, so statements quantified over these formulas specialize to it.
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), §1.1, p.3, and §4.1, p.13

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace DetCCHard

/-- A **3-CNF formula** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256
ad552d13…a4a03, §1.1, p.3): a CNF formula (published `CookPvsNP.CNF`) each of whose clauses has at
most three literals.

**Formalization Note** "At most three" rather than "exactly three": every formula with exactly
three literals per clause is covered, so statements quantified over these formulas specialize to
the exactly-three reading. -/
def Is3CNF (Φ : CookPvsNP.CNF) : Prop := ∀ C ∈ Φ, C.length ≤ 3

/-- The **number of variables** `N` of a CNF formula (§4.1, p.13, sparse 3-SAT): the number of
distinct variable indices occurring in it. -/
def numVars (Φ : CookPvsNP.CNF) : ℕ := (Φ.flatten.map Prod.snd).toFinset.card

end DetCCHard


