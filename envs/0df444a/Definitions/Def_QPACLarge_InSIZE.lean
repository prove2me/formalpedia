-- Prove2me | Definitions.Def_QPACLarge_InSIZE
-- name    : QPACLarge_InSIZE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:40.550435+00:00
-- url     : https://prove2.me/theorems/e60463fa-6db7-45a6-a338-0edc6d483e85
-- title:
--   Membership in $\mathrm{SIZE}[s]$
-- statement:
--   For a size bound $s$, a Boolean function $f : \{0,1\}^n \to \{0,1\}$ belongs to $\mathrm{SIZE}[s]$ if it is computed by a Boolean circuit with at most $s$ gates.
--
--   The class $\mathrm{SIZE}[\mathrm{poly}]$ of the mission's conditional clause consists of the families whose length-$n$ members lie in $\mathrm{SIZE}[n^c + c]$ for one constant $c$.
--
--   **Formalization Note** Circuits are the published straight-line programs over AND, OR and NOT (`QAlgorithms.BoolCircuit n 1`, size = number of gates). The basis has no constant gates, so no function on $0$ inputs is in any $\mathrm{SIZE}[s]$; the paper's concept classes are indexed by $n \ge 1$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 1.1, p.6; Section 2.1, p.14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical

namespace QPACLarge

open QAlgorithms

/-- **Membership in `SIZE[s]`.**
Oliveira, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 1.1, p.6 (also Section 2.1,
p.14): "For a size bound `s : ℕ → ℕ`, we let `SIZE[s(n)]` denote the set of Boolean functions
`f : {0,1}ⁿ → {0,1}` computed by a Boolean circuit of size at most `s(n)`."

`InSIZE f s` says that `f` is computed by a well-formed Boolean circuit (AND, OR, NOT gates) with
at most `s` gates.

**Formalization Note.** Circuits are the published `QAlgorithms.BoolCircuit n 1` (de Wolf's
straight-line programs over AND/OR/NOT, size = number of gates). The basis has no constant gates,
so no circuit has zero inputs: at `n = 0` no function is in any `SIZE[s]`. -/
def InSIZE {n : ℕ} (f : Qubits n → Bool) (s : ℕ) : Prop :=
  ∃ C : BoolCircuit n 1, C.WellFormed ∧ C.size ≤ s ∧ ∀ x, C.eval x 0 = f x

end QPACLarge


