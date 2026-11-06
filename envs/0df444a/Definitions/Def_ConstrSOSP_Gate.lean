-- Prove2me | Definitions.Def_ConstrSOSP_Gate
-- name    : ConstrSOSP_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:08.844722+00:00
-- url     : https://prove2.me/theorems/dc8db569-4f46-45c8-b287-fc221c3314db
-- title:
--   Gate of a Boolean circuit (∧, ∨, ¬)
-- statement:
--   A **gate** of a Boolean circuit is one of $\wedge$ (AND) and $\vee$ (OR), each with fan-in $2$, or $\neg$ (NOT), with fan-in $1$. A gate names the wires it reads.
--
--   These are the only gates allowed in the circuits of LocalOpt and Iter.
--
--   **Formalization Note** Wires are numbered $0,1,2,\dots$; in a circuit with $n$ inputs the wires $0,\dots,n-1$ carry the inputs and the $k$-th gate writes wire $n+k$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib

namespace ConstrSOSP

/-- **A gate of a Boolean circuit** (Kontogiannis, Panageas & Pollatos, *The Computational
Complexity of Avoiding Strict Saddle Points in Constrained Optimization*, arXiv:2604.02285,
version of 2 November 2026, §4.1, p.17: "a Boolean circuit C : {0, 1}^d → {0, 1}^d with d inputs
and d outputs, is allowed to use the logic gates ∧ (AND), ∨ (OR) and ¬ (NOT), where the ∧ and ∨
gates have fan-in 2, and the ¬ gate has fan-in 1").

`andG i j` and `orG i j` read the wires `i` and `j`; `notG i` reads the wire `i`.

**Formalization Note** Wires are numbered `0, 1, 2, …`: in a circuit with `n` inputs the wires
`0, …, n − 1` carry the inputs, and the `k`-th gate (from `0`) writes the wire `n + k`. -/
inductive Gate where
  | andG (i j : ℕ)
  | orG (i j : ℕ)
  | notG (i : ℕ)

end ConstrSOSP


