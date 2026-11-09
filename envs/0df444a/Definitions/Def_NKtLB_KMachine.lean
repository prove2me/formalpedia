-- Prove2me | Definitions.Def_NKtLB_KMachine
-- name    : NKtLB_KMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:59:37.649674+00:00
-- url     : https://prove2.me/theorems/970a2447-458c-4a15-b931-c2ea9ff20ed1
-- title:
--   $K^t_M(x)$: Kolmogorov complexity with respect to a machine
-- statement:
--   For a machine $M$, a time bound $t$ and a string $x$, $K^t_M(x)$ is the minimum length of a string $p$ such that $M$ on input $p$ outputs $x$ within $t$ steps:
--   $$
--   K^t_M(x)=\min\{|p| : M(p)\text{ outputs }x\text{ within }t\text{ steps}\}.
--   $$
--   It is the measure in the definition of a time-efficient universal machine.
--
--   **Formalization Note** The auxiliary, guess and randomness tapes are empty and the oracle is $\emptyset$. The value lies in $\mathbb N\cup\{\infty\}$, with $\infty$ when no $p$ exists.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB

/-- **`K^t_M(x)`, Kolmogorov complexity with respect to a machine** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21): "For a
machine `M`, time bound `t`, and string `x`, we let `K^t_M(x)` be the minimum length of a string
`p ∈ {0,1}^*` such that `M` outputs `x` on input string `p` when running for at most `t` steps."

**Formalization Note.** `p` is on the input tape, the auxiliary, guess and randomness tapes are
empty and the oracle is `∅`. The value is in `ℕ∞`: `⊤` when no such `p` exists. -/
noncomputable def KMachine (M : Machine) (t : ℕ) (x : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (_ : M.HaltsWith ∅ ⟨p, [], [], []⟩ t (bitsSym x)), (p.length : ℕ∞)

end NKtLB


