-- Prove2me | Definitions.Def_NKtLB_Supplement_PrBPTIMEPar
-- name    : NKtLB_Supplement_PrBPTIMEPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:30:10.804548+00:00
-- url     : https://prove2.me/theorems/44025644-ad95-4d5f-8d81-ccfac816df0b
-- title:
--   $\mathsf{pr}\text{-}\mathsf{BPTIME}[T]^{\|O}$ — promise bounded-error time with non-adaptive queries
-- statement:
--   A promise problem $(\mathrm{YES},\mathrm{NO})$ is in $\mathsf{pr}\text{-}\mathsf{BPTIME}[T(n)]^{\|O}$ if a randomized machine, running in time $\tau=c\cdot T(n)+c$ and making only non-adaptive queries to $O$, accepts every $x\in\mathrm{YES}$ with probability at least $2/3$ and every $x\in\mathrm{NO}$ with probability at most $1/3$. Its behaviour on other inputs is unconstrained.
--
--   Then $\mathsf{pr}\text{-}\mathsf{BPTIME}[T]^{\|\mathsf{NP}}=\bigcup_{A\in\mathsf{NP}}\mathsf{pr}\text{-}\mathsf{BPTIME}[T]^{\|A}$.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`. Non-adaptivity (one round of `AdaptRounds`) is required on every input and every random string.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 7, p.11; p.9

import Mathlib
import Definitions.Def_NKtLB_Supplement_AdaptRounds
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`pr-BPTIME[T(n)]^{∥O}`** (for `pr-BPTIME[n^{poly(log n)}]^{∥NP}`, Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 7, p.11; "We
use `∥NP` to denote parallel access to an NP-oracle", p.9): promise problems `(YES, NO)` solved with
two-sided error `1/3` in time `O(T(n))` by a randomized machine whose oracle queries to `O` are
non-adaptive. There are `M` and `c` such that, with `τ = c·T(|x|) + c`: for every `x` and every
`r ∈ {0,1}^τ` the first `τ` steps of `M^O(x; r)` make one round of queries (`AdaptRounds … 1`);
`x ∈ YES` implies acceptance probability `≥ 2/3` and `x ∈ NO` implies it is `≤ 1/3`.

**Formalization Note.** Acceptance: halting within `τ` steps with output `1`. Non-adaptivity is
required on every input and random string (the machine is a non-adaptive oracle machine). -/
def PrBPTIMEPar (O : Set (List Bool)) (T : ℕ → ℕ) : Set (Set (List Bool) × Set (List Bool)) :=
  {P | ∃ (M : Machine) (c : ℕ), ∀ x : List Bool,
    (∀ r : List Bool, r.length = c * T x.length + c →
      AdaptRounds M O ⟨x, [], [], r⟩ (c * T x.length + c) 1) ∧
    (x ∈ P.1 → (2 / 3 : ℝ) ≤
        prob (c * T x.length + c) (fun r => M.HaltsWith O ⟨x, [], [], r⟩ (c * T x.length + c) [Sym.one])) ∧
    (x ∈ P.2 →
        prob (c * T x.length + c) (fun r => M.HaltsWith O ⟨x, [], [], r⟩ (c * T x.length + c) [Sym.one])
          ≤ (1 / 3 : ℝ))}

end NKtLB.Supplement


