-- Prove2me | Definitions.Def_NKtLB_Supplement_BPEXPPar
-- name    : NKtLB_Supplement_BPEXPPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:31:20.544581+00:00
-- url     : https://prove2.me/theorems/4ac41661-9aa4-4af7-8a90-23d4edec1f3c
-- title:
--   $\mathsf{BPEXP}^{\|O}$ — bounded-error exponential time with non-adaptive queries
-- statement:
--   $\mathsf{BPEXP}^{\|O}$ is the class of languages decided with two-sided error $1/3$ by a randomized machine running in time $c\cdot 2^{|x|^k}+c$ with non-adaptive access to $O$ (on every random string). $\mathsf{BPEXP}^{\|\mathsf{NP}}=\bigcup_{A\in\mathsf{NP}}\mathsf{BPEXP}^{\|A}$.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 4 (ii), p.9; Theorem 82, p.53

import Mathlib
import Definitions.Def_NKtLB_Supplement_AdaptRounds
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`BPEXP^{∥O}`** (for `BPEXP^{∥NP}`, Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 4 (ii), p.9 and Theorem 82, p.53): languages
decided with two-sided error `1/3` in time `2^{n^{O(1)}}` by a randomized machine with non-adaptive
access to `O`. There are `k`, `M`, `c` such that, with `τ = c·2^{|x|^k} + c` and `r ∈ {0,1}^τ`: the
first `τ` steps of `M^O(x; r)` make one round of queries for every `r`; `x ∈ L` implies acceptance
probability `≥ 2/3`, `x ∉ L` implies it is `≤ 1/3` (acceptance: halting within `τ` steps with output
`1`). -/
def BPEXPPar (O : Set (List Bool)) : Set (Set (List Bool)) :=
  {L | ∃ (k : ℕ) (M : Machine) (c : ℕ), ∀ x : List Bool,
    (∀ r : List Bool, r.length = c * 2 ^ (x.length ^ k) + c →
      AdaptRounds M O ⟨x, [], [], r⟩ (c * 2 ^ (x.length ^ k) + c) 1) ∧
    (x ∈ L → (2 / 3 : ℝ) ≤ prob (c * 2 ^ (x.length ^ k) + c)
        (fun r => M.HaltsWith O ⟨x, [], [], r⟩ (c * 2 ^ (x.length ^ k) + c) [Sym.one])) ∧
    (x ∉ L → prob (c * 2 ^ (x.length ^ k) + c)
        (fun r => M.HaltsWith O ⟨x, [], [], r⟩ (c * 2 ^ (x.length ^ k) + c) [Sym.one]) ≤ (1 / 3 : ℝ))}

end NKtLB.Supplement


