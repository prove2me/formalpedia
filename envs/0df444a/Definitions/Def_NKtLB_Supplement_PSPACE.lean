-- Prove2me | Definitions.Def_NKtLB_Supplement_PSPACE
-- name    : NKtLB_Supplement_PSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:33:02.542369+00:00
-- url     : https://prove2.me/theorems/11228d23-fba4-462b-af0d-2d656084bcc0
-- title:
--   $\mathsf{PSPACE}$
-- statement:
--   $\mathsf{PSPACE}$ is the class of languages decided by a deterministic machine in polynomial space and unbounded time. On every input $x$ the machine halts with the correct answer, and until then every work tape uses at most $S=c(|x|+1)^k+c$ cells, every read/write head stays within $S$ and every read-only head within $|x|+S$.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`. The head-position bounds keep heads from acting as unbounded counters.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 126, p.98 (standard)

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB.Supplement

/-- **`PSPACE`** (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 126, p.98; standard): languages decided in polynomial space.
There are `M`, `k`, `c` such that on every input `x` (oracle `∅`) `M` halts at some step `t` with
output `1` if `x ∈ L` and `0` otherwise, and up to step `t` every read/write tape holds at most
`S = c·(|x| + 1)^k + c` cells, every read/write head stays within `S` and every read-only head within
`|x| + S`.

**Formalization Note.** The head-position bounds keep head positions from serving as unbounded
counters; the time is unrestricted. -/
def PSPACE : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (k c : ℕ), ∀ x : List Bool, ∃ t : ℕ,
    (x ∈ L → M.HaltsWith ∅ ⟨x, [], [], []⟩ t [Sym.one]) ∧
    (x ∉ L → M.HaltsWith ∅ ⟨x, [], [], []⟩ t [Sym.zero]) ∧
    ∀ j ≤ t,
      (∀ i, ((M.run ∅ ⟨x, [], [], []⟩ j).rwTape i).length ≤ c * (x.length + 1) ^ k + c) ∧
      (∀ i, (M.run ∅ ⟨x, [], [], []⟩ j).rwHead i ≤ c * (x.length + 1) ^ k + c) ∧
      (∀ i, (M.run ∅ ⟨x, [], [], []⟩ j).roHead i ≤ x.length + (c * (x.length + 1) ^ k + c))}

end NKtLB.Supplement


