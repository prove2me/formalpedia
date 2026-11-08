-- Prove2me | Definitions.Def_OneOfManyCC_Formula
-- name    : OneOfManyCC_Formula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:08.398313+00:00
-- url     : https://prove2.me/theorems/6bcfe1d2-0246-4dbb-b022-26466ba9f926
-- title:
--   Formulas with AND and OR gates and leaves from a given set
-- statement:
--   A **formula** over a leaf set $L$ is a binary tree whose inner nodes are AND and OR gates and whose leaves are elements of $L$. Its **depth** is the maximum number of gates on a path from the root to a leaf. Given a function on a domain $Z$ for each leaf, the formula computes a function $Z\to\{0,1\}$ by evaluating the gates.
--
--   These formulas are used in the majority amplification of Lemma 3.7 and as the walking plan of the proof of Theorem 1.2.
--
--   **Formalization Note** There are no negations at inner nodes.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.1, p.6; §3.3, p.8, Lemma 3.7

import Mathlib

namespace OneOfManyCC

/-- **A formula with AND and OR gates and leaves from `L`**, as in Lemma 3.7 of
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §3.3, p.8:
"formulas of depth at most d with AND and OR gates and leaves from F".

**Formalization Note.** There are no negations at inner nodes. -/
inductive Formula (L : Type) : Type
  | leaf (l : L) : Formula L
  | and (φ ψ : Formula L) : Formula L
  | or (φ ψ : Formula L) : Formula L

namespace Formula

variable {L Z : Type}

/-- The depth: "the maximum number of gates on a path from the root to a leaf" (§3.1, p.6). -/
def depth : Formula L → ℕ
  | leaf _ => 0
  | and φ ψ => max φ.depth ψ.depth + 1
  | or φ ψ => max φ.depth ψ.depth + 1

/-- The value of the formula at `z`, where the leaf `l` has the function `v l`. -/
def eval (v : L → Z → Bool) : Formula L → Z → Bool
  | leaf l, z => v l z
  | and φ ψ, z => φ.eval v z && ψ.eval v z
  | or φ ψ, z => φ.eval v z || ψ.eval v z

end Formula

end OneOfManyCC


