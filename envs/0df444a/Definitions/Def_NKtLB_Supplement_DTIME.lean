-- Prove2me | Definitions.Def_NKtLB_Supplement_DTIME
-- name    : NKtLB_Supplement_DTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:26:42.593927+00:00
-- url     : https://prove2.me/theorems/89edc926-2e41-438e-893d-f5c5c90d10a3
-- title:
--   $\mathsf{DTIME}[T]$ — deterministic time
-- statement:
--   $\mathsf{DTIME}[T(n)]$ is the class of languages $L$ decided by a deterministic machine in time $O(T(n))$: on every input $x$ the machine halts within $c\cdot T(|x|)+c$ steps with output $1$ if $x\in L$ and $0$ otherwise.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`. Not defined in the paper.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 123, p.90 (standard)

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB.Supplement

/-- **`DTIME[T(n)]`** (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 123, p.90; standard, not defined in the paper): the
languages decided by a deterministic machine of the model of §3.2 in time `O(T(n))`. There are a
machine `M` and `c ∈ ℕ` such that on every input `x` (empty auxiliary, guess and randomness tapes,
oracle `∅`) `M` halts within `c·T(|x|) + c` steps with output `1` if `x ∈ L` and `0` otherwise.

**Formalization Note.** `O(T)` is read `c·T + c`, as the base `NTIME`. -/
def DTIME (T : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (c : ℕ), ∀ x : List Bool,
    (x ∈ L → M.HaltsWith ∅ ⟨x, [], [], []⟩ (c * T x.length + c) [Sym.one]) ∧
    (x ∉ L → M.HaltsWith ∅ ⟨x, [], [], []⟩ (c * T x.length + c) [Sym.zero])}

end NKtLB.Supplement


