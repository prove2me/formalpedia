-- Prove2me | Definitions.Def_NKtLB_Supplement_SIZEO
-- name    : NKtLB_Supplement_SIZEO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:34:05.986936+00:00
-- url     : https://prove2.me/theorems/3e6fd567-8491-4352-9906-f8768b73ee4f
-- title:
--   $\mathsf{SIZE}^O[s]$
-- statement:
--   "For a language $O$ and a function $s:\mathbb N\to\mathbb N$, we let $\mathsf{SIZE}^O[s]$ denote the set of languages computed by Boolean circuits with oracle access to $O$ and of size at most $s(n)$" (p.12): for every $n$, some oracle circuit of size at most $s(n)$ decides $L$ on all inputs of length $n$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12

import Mathlib
import Definitions.Def_NKtLB_Supplement_OCircuit

namespace NKtLB.Supplement

/-- **`SIZE^O[s]`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12): "For a language `O` and a function `s : ℕ → ℕ`, we let
`SIZE^O[s]` denote the set of languages computed by Boolean circuits with oracle access to `O` and of
size at most `s(n)`." For every `n` some oracle circuit of size `≤ s(n)` decides `L` on `{0,1}^n`. -/
def SIZEO (O : Set (List Bool)) (s : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∀ n : ℕ, ∃ C : OCircuit, C.size ≤ s n ∧
    ∀ x : List Bool, x.length = n → (C.eval O x = true ↔ x ∈ L)}

end NKtLB.Supplement


