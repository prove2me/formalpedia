-- Prove2me | Definitions.Def_KarpLiptonOM_Gate
-- name    : KarpLiptonOM_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:02.252048+00:00
-- url     : https://prove2.me/theorems/2e566323-de8c-48fc-87d8-ae9a8348a809
-- title:
--   Boolean gate (constant, NOT, AND, OR)
-- statement:
--   A **gate** of a Boolean circuit is a constant $0$ or $1$, a negation $\lnot w_i$, or a conjunction or disjunction $w_i \wedge w_j$, $w_i \vee w_j$ of two wires. In a circuit with $n$ inputs, wire $i < n$ is the $i$-th input and wire $n + g$ is the value of the $g$-th gate (indices from $0$).
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (circuits)

import Mathlib

namespace KarpLiptonOM

/-- A gate of a Boolean circuit (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20, "circuits with `n` inputs and at most `s`
gates"): a constant, a negation, or a binary AND/OR. Wire `i < n` is input `i`; wire `n + g` is
gate `g` (0-based). `Gate.refs` lists the wires a gate reads. -/
inductive Gate where
  | const (b : Bool)
  | not (i : ℕ)
  | and (i j : ℕ)
  | or (i j : ℕ)
  deriving DecidableEq

/-- The wires read by a gate. -/
def Gate.refs : Gate → List ℕ
  | .const _ => []
  | .not i => [i]
  | .and i j => [i, j]
  | .or i j => [i, j]

end KarpLiptonOM


