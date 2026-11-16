-- Prove2me | Definitions.Def_NKtLB_Supplement_NPpoly
-- name    : NKtLB_Supplement_NPpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:31:46.890011+00:00
-- url     : https://prove2.me/theorems/0c58a65b-b377-4c8e-ad35-10bd940aaeae
-- title:
--   $\mathsf{NP}/\mathsf{poly}$
-- statement:
--   $\mathsf{NP}/\mathsf{poly}$ is the class of languages $L$ for which there are a nondeterministic machine $M$, constants $k,c$ and advice strings $a_n$ with $|a_n|\le c\,n^k+c$ such that $x\in L$ iff some guess $w$ of length $c|x|^k+c$ makes $M(x;a_{|x|};w)$ accept within $c|x|^k+c$ steps.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`. The advice is on the auxiliary tape.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorems 4, 5, 80, 82 (standard)

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB.Supplement

/-- **`NP/poly`** (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorems 4, 5, 80, 82, pp.9–10, 51, 53; standard): languages decided
by a nondeterministic polynomial-time machine with polynomial advice. There are `M`, `k`, `c` and an
advice sequence `a` with `|a(n)| ≤ c·n^k + c` such that, with `τ = c·|x|^k + c`, `x ∈ L` iff some guess
`w ∈ {0,1}^τ` makes `M` (input `x`, advice `a(|x|)` on the auxiliary tape) halt within `τ` steps with
output `1`. -/
def NPpoly : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (k c : ℕ) (a : ℕ → List Bool), (∀ n, (a n).length ≤ c * n ^ k + c) ∧
    ∀ x : List Bool, (x ∈ L ↔ ∃ w : List Bool, w.length = c * x.length ^ k + c ∧
      M.HaltsWith ∅ ⟨x, a x.length, w, []⟩ (c * x.length ^ k + c) [Sym.one])}

end NKtLB.Supplement


