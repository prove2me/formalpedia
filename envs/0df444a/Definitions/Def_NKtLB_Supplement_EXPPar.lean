-- Prove2me | Definitions.Def_NKtLB_Supplement_EXPPar
-- name    : NKtLB_Supplement_EXPPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:30:46.797286+00:00
-- url     : https://prove2.me/theorems/29c7d170-2169-4f4f-af7d-7e87850cc797
-- title:
--   $\mathsf{EXP}^{\|O}$ — exponential time with non-adaptive queries
-- statement:
--   $\mathsf{EXP}^{\|O}$ is the class of languages decided by a deterministic machine running in time $c\cdot 2^{|x|^k}+c$ (for some $k,c$) with non-adaptive access to $O$. $\mathsf{EXP}^{\|\mathsf{NP}}=\bigcup_{A\in\mathsf{NP}}\mathsf{EXP}^{\|A}$.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 4 (ii), p.9; Theorem 80, p.51

import Mathlib
import Definitions.Def_NKtLB_Supplement_AdaptRounds

namespace NKtLB.Supplement

/-- **`EXP^{∥O}`** (for `EXP^{∥NP}`, Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 4 (ii), p.9 and Theorem 80, p.51): languages decided
in deterministic time `2^{n^{O(1)}}` with non-adaptive access to `O`. There are `k`, `M` and `c` such
that, with `τ = c·2^{|x|^k} + c`, `M^O(x)` halts within `τ` steps with output `1` if `x ∈ L` and `0`
otherwise, and its first `τ` steps make one round of queries (`AdaptRounds … 1`). -/
def EXPPar (O : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ (k : ℕ) (M : Machine) (c : ℕ), ∀ x : List Bool,
    AdaptRounds M O ⟨x, [], [], []⟩ (c * 2 ^ (x.length ^ k) + c) 1 ∧
    (x ∈ L → M.HaltsWith O ⟨x, [], [], []⟩ (c * 2 ^ (x.length ^ k) + c) [Sym.one]) ∧
    (x ∉ L → M.HaltsWith O ⟨x, [], [], []⟩ (c * 2 ^ (x.length ^ k) + c) [Sym.zero])}

end NKtLB.Supplement


