-- Prove2me | Definitions.Def_NKtLB_Supplement_AMTIME
-- name    : NKtLB_Supplement_AMTIME
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:27:01.299405+00:00
-- url     : https://prove2.me/theorems/b83b5786-5353-4d74-9f76-8ce4256255fe
-- title:
--   $\mathsf{AMTIME}[T]$ — Arthur–Merlin time
-- statement:
--   $\mathsf{AMTIME}[T(n)]$ is the class of languages with public-coin Arthur–Merlin protocols of running time $O(T(n))$. Arthur sends a uniformly random string $r$, Merlin replies with a string $w$, and a deterministic verifier decides in time $\tau=c\cdot T(|x|)+c$ whether to accept $(x,r,w)$:
--   $$
--   x\in L\ \Rightarrow\ \Pr_r[\exists w:\ \text{accept}]\ge 2/3,\qquad x\notin L\ \Rightarrow\ \Pr_r[\exists w:\ \text{accept}]\le 1/3 .
--   $$
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`. Arthur's string is on the randomness tape and Merlin's reply on the guess tape, both of length $\tau$. Acceptance means halting within $\tau$ steps with output $1$. Not defined in the paper.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorems 9, 59, 65 (standard)

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`AMTIME[T(n)]`** (used in Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorems 9, 59, 65, pp.12, 39, 43; standard, not defined in
the paper): public-coin Arthur–Merlin protocols with running time `O(T(n))`. There are a verifier
`M` and `c ∈ ℕ` such that, with `τ = c·T(|x|) + c`, Arthur's random string `r ∈ {0,1}^τ` (randomness
tape) and Merlin's reply `w ∈ {0,1}^τ` (guess tape), `M` is run on input `x` for `τ` steps and
accepts if it halts with output `1`; and
* if `x ∈ L` then `Pr_r[∃w, M accepts (x, r, w)] ≥ 2/3`,
* if `x ∉ L` then `Pr_r[∃w, M accepts (x, r, w)] ≤ 1/3`.

**Formalization Note.** `O(T)` is read `c·T + c` (as the base `NTIME`); Merlin's reply depends on
`r` (the `∃w` is inside the probability). -/
def AMTIME (T : ℕ → ℕ) : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (c : ℕ), ∀ x : List Bool,
    (x ∈ L → (2 / 3 : ℝ) ≤ prob (c * T x.length + c) (fun r => ∃ w : List Bool,
        w.length = c * T x.length + c ∧
        M.HaltsWith ∅ ⟨x, [], w, r⟩ (c * T x.length + c) [Sym.one])) ∧
    (x ∉ L → prob (c * T x.length + c) (fun r => ∃ w : List Bool,
        w.length = c * T x.length + c ∧
        M.HaltsWith ∅ ⟨x, [], w, r⟩ (c * T x.length + c) [Sym.one]) ≤ (1 / 3 : ℝ))}

end NKtLB.Supplement


