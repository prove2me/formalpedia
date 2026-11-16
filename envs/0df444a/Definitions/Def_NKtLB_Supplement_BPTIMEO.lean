-- Prove2me | Definitions.Def_NKtLB_Supplement_BPTIMEO
-- name    : NKtLB_Supplement_BPTIMEO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:29:31.613201+00:00
-- url     : https://prove2.me/theorems/8a394958-b125-44a4-9e7d-f465a3e10d07
-- title:
--   $\mathsf{BPTIME}^O[T]$ — bounded-error time with an oracle
-- statement:
--   $\mathsf{BPTIME}^O[T(n)]$ is the class of languages $L$ decided with two-sided error by a randomized machine with (adaptive) access to the oracle $O$ in time $\tau=c\cdot T(n)+c$: the machine accepts every $x\in L$ with probability at least $2/3$ and every $x\notin L$ with probability at most $1/3$, over a uniform random string of length $\tau$.
--
--   Then $\mathsf{BPP}^{\mathsf{NP}}=\bigcup_k\bigcup_{A\in\mathsf{NP}}\mathsf{BPTIME}^A[n^k]$ and $\mathsf{BPTIME}^{\mathsf{NP}}[n^{\mathrm{poly}(\log n)}]=\bigcup_c\bigcup_{A\in\mathsf{NP}}\mathsf{BPTIME}^A[n^{(\log n)^c}]$.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`. Acceptance means halting within $\tau$ steps with output $1$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 4, p.9 (standard)

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`BPTIME^O[T(n)]`** (for `BPP^{NP}` and `BPTIME^{NP}[n^{poly(log n)}]`, Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 4, p.9;
standard): languages decided with two-sided error `1/3` by a randomized machine with (adaptive)
access to the oracle `O` in time `O(T(n))`. There are `M` and `c` such that, with `τ = c·T(|x|) + c`
and `r ∈ {0,1}^τ` on the randomness tape, `x ∈ L` implies `Pr_r[M^O(x; r)` halts within `τ` steps with
output `1] ≥ 2/3`, and `x ∉ L` implies that probability is `≤ 1/3`. -/
def BPTIMEO (O : Set (List Bool)) (T : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (c : ℕ), ∀ x : List Bool,
    (x ∈ L → (2 / 3 : ℝ) ≤
        prob (c * T x.length + c) (fun r => M.HaltsWith O ⟨x, [], [], r⟩ (c * T x.length + c) [Sym.one])) ∧
    (x ∉ L →
        prob (c * T x.length + c) (fun r => M.HaltsWith O ⟨x, [], [], r⟩ (c * T x.length + c) [Sym.one])
          ≤ (1 / 3 : ℝ))}

end NKtLB.Supplement


