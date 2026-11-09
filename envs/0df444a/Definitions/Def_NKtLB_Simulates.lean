-- Prove2me | Definitions.Def_NKtLB_Simulates
-- name    : NKtLB_Simulates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:02:59.681244+00:00
-- url     : https://prove2.me/theorems/7f30454f-a6e8-43dd-97dd-f8e6d0ece187
-- title:
--   Simulation of every machine through the program format
-- statement:
--   A machine $U$ with a machine code $\langle\cdot\rangle$ **simulates** every machine if for each machine $M$ there is a constant $c_M$ such that, for every oracle $O$, all strings $\alpha,x,w,r$ and every time bound $t$:
--
--   1. if $M(\alpha;x;w;r)$ halts within $t$ steps with output $z$, then $U$ on input $s_\alpha01\langle M\rangle\alpha$, with the same auxiliary string, guess, random string and oracle, halts within $c_M\,t\,(\lceil\log t\rceil+1)+c_M$ steps with output $z$;
--   2. if the first $t$ steps of $M$ make only queries of length at most $\ell$, so do the first $t$ steps of $U$ on that input.
--
--   This is the paper's assumption that $U$, given $\langle M\rangle,\alpha,x,w,r$, "runs in time $\tilde O(|M|,t)$ and outputs the string produced by $M(\alpha;x;w;r)$".
--
--   **Formalization Note** $\tilde O(|M|,t)$ is read as $c_M\,t(\lceil\log t\rceil+1)+c_M$. Quasi-linear overhead is what the proof of Theorem 8 needs (Eq. (30)). Clause 2 says that $U$ passes the queries of $M$ through unchanged and simulates at most one step of $M$ per step of its own. The paper uses this implicitly whenever it builds a program with oracle access to $L^{\le\ell}$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_prog

namespace NKtLB

/-- **`U` simulates every machine through the program format** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.2, p.21): "We also assume an
encoding function `⟨·⟩` for machines … such that `U`, when given (the encoding of) a machine `M`, an
input `α`, an auxiliary string `x`, a non-deterministic guess `w`, and a random string `r`, runs in
time `Õ(|M|, t)` and outputs the string produced by `M(α; x; w; r)`, where … `t` is the number of
steps `M` runs on `(α; x; w; r)`."

For every machine `M` there is `c` such that, for every oracle `O` and all `α, x, w, r, t`:
1. if `M` halts within `t` steps with output `z`, then `U`, with `prog code M α` on its input tape
   and the same auxiliary, guess and randomness tapes and oracle, halts within
   `c · t · (⌈log₂ t⌉ + 1) + c` steps with output `z`;
2. if the first `t` steps of `M` make only oracle queries of length at most `ℓ`, so do the first
   `t` steps of `U` on `prog code M α`.

**Formalization Note.** `Õ(|M|, t)` is read as `c_M · t · (⌈log t⌉ + 1) + c_M` with `c_M` depending
only on `M`; the proof of Theorem 8 (eq. (30), p.76) needs quasi-linear overhead. Clause 2 says that
`U` passes `M`'s queries through and simulates at most one step of `M` per step of its own; the paper
uses it implicitly whenever it builds a program "with oracle access to `L^{≤ℓ}`". -/
def Simulates (U : Machine) (code : Machine → List Bool) : Prop :=
  ∀ M : Machine, ∃ c : ℕ, ∀ (O : Set (List Bool)) (α x w r : List Bool) (t : ℕ),
    (∀ z : List Sym, M.HaltsWith O ⟨α, x, w, r⟩ t z →
      U.HaltsWith O ⟨prog code M α, x, w, r⟩ (c * (t * (Nat.clog 2 t + 1)) + c) z) ∧
    (∀ ℓ : ℕ∞, M.QueryBounded O ℓ ⟨α, x, w, r⟩ t →
      U.QueryBounded O ℓ ⟨prog code M α, x, w, r⟩ t)

end NKtLB


