-- Prove2me | Definitions.Def_NKtLB_Supplement_PrBPP
-- name    : NKtLB_Supplement_PrBPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:33:26.136199+00:00
-- url     : https://prove2.me/theorems/bc800b0a-6365-4ad0-a9f5-84ca2cfdbbd2
-- title:
--   $\mathsf{pr}\text{-}\mathsf{BPP}^O$ — promise bounded-error polynomial time with an oracle
-- statement:
--   A promise problem (a "property") $P=(\mathrm{YES},\mathrm{NO})$ is in $\mathsf{pr}\text{-}\mathsf{BPP}^O$ if a randomized polynomial-time machine with oracle access to $O$ accepts every $x\in\mathrm{YES}$ with probability at least $2/3$ and every $x\in\mathrm{NO}$ with probability at most $1/3$.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 126, p.98

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`pr-BPP^O`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 126, p.98: "any dense `pr-BPP^O` property `P`"): promise problems
`(YES, NO)` solved with two-sided error `1/3` in polynomial time by a randomized machine with
(adaptive) access to `O`. There are `M`, `k`, `c` such that, with `τ = c·|x|^k + c`, `x ∈ YES` implies
`Pr_{r∼{0,1}^τ}[M^O(x; r)` halts within `τ` steps with output `1] ≥ 2/3`, and `x ∈ NO` implies that
probability is `≤ 1/3`. -/
def PrBPP (O : Set (List Bool)) : Set (Set (List Bool) × Set (List Bool)) :=
  {P | ∃ (M : Machine) (k c : ℕ), ∀ x : List Bool,
    (x ∈ P.1 → (2 / 3 : ℝ) ≤ prob (c * x.length ^ k + c)
        (fun r => M.HaltsWith O ⟨x, [], [], r⟩ (c * x.length ^ k + c) [Sym.one])) ∧
    (x ∈ P.2 → prob (c * x.length ^ k + c)
        (fun r => M.HaltsWith O ⟨x, [], [], r⟩ (c * x.length ^ k + c) [Sym.one]) ≤ (1 / 3 : ℝ))}

end NKtLB.Supplement


