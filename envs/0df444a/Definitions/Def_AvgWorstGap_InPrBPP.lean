-- Prove2me | Definitions.Def_AvgWorstGap_InPrBPP
-- name    : AvgWorstGap_InPrBPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:01.323048+00:00
-- url     : https://prove2.me/theorems/35bd2d71-e33e-43da-9eb4-c4a5ae9c1d21
-- title:
--   Promise problems, $\mathsf{prBPTIME}$, $\mathsf{prBPP}$ and $\mathsf{BPP}$
-- statement:
--   A **promise problem** is a pair $(\mathrm{YES},\mathrm{NO})$ of sets of binary strings. A randomized machine $M$ **decides it in time $T$** if on every input $z$ and every random string $r\in\{0,1\}^{T(|z|)}$ the machine halts within $T(|z|)$ steps, and:
--
--   1. for $z\in\mathrm{YES}$ it outputs $1$ with probability at least $2/3$;
--   2. for $z\in\mathrm{NO}$ it outputs $0$ with probability at least $2/3$.
--
--   $\mathsf{prBPTIME}[T]$ is the class of promise problems some machine decides in time $T$. $\mathsf{prBPP}$ is the union over polynomials $p$ of $\mathsf{prBPTIME}[p]$. A language $L$ is in $\mathsf{BPP}$ if $(L,\overline L)\in\mathsf{prBPP}$. The module also defines "halts within $T$ steps with output bit $[P]$" (output $1$ if $P$ holds, $0$ otherwise).
--
--   **Formalization Note** The deciders have no oracle; the input is on the input tape, and the auxiliary and guess tapes are empty.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), standard; "A decides Π on z", §2.5, p.18

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_prob

namespace AvgWorstGap

open NKtLB

/-- A **promise problem** `(YES, NO)` over binary strings. -/
structure PromiseProblem where
  yes : Set (List Bool)
  no : Set (List Bool)

/-- The one-symbol output word of a bit. -/
def bitOut (b : Bool) : List Sym := [Sym.ofBool b]

/-- **`M` halts within `T` steps with the truth value of `P` as its output bit**: output `1` if `P`
holds and `0` otherwise. -/
def HaltsWithBit (M : Machine) (O : Set (List Bool)) (inp : Inputs) (T : ℕ) (P : Prop) : Prop :=
  (P ∧ M.HaltsWith O inp T (bitOut true)) ∨ (¬ P ∧ M.HaltsWith O inp T (bitOut false))

/-- **A randomized machine decides a promise problem in time `T`** (the standard bounded-error
definition; arXiv:2610.19162, version of October 30, 2026, p.18 writes "A decides Π on z" for
"`A(z) = 1` if `z ∈ YES`, `0` if `z ∈ NO`, either otherwise"): on every input `z` and every random
string `r ∈ {0,1}^{T(|z|)}` the machine halts within `T(|z|)` steps; for `z ∈ YES` it outputs `1`
with probability at least `2/3`, for `z ∈ NO` it outputs `0` with probability at least `2/3`.

**Formalization Note.** No oracle; input on the input tape, auxiliary and guess tapes empty,
randomness on the randomness tape. -/
def DecidesWithin (M : Machine) (T : ℕ → ℕ) (P : PromiseProblem) : Prop :=
  ∀ z : List Bool,
    (∀ r : List Bool, r.length = T z.length → (M.run ∅ ⟨z, [], [], r⟩ (T z.length)).state = M.halt) ∧
    (z ∈ P.yes →
      2 / 3 ≤ prob (T z.length) (fun r => M.HaltsWith ∅ ⟨z, [], [], r⟩ (T z.length) (bitOut true))) ∧
    (z ∈ P.no →
      2 / 3 ≤ prob (T z.length) (fun r => M.HaltsWith ∅ ⟨z, [], [], r⟩ (T z.length) (bitOut false)))

/-- **`prBPTIME[T]`**: some randomized machine decides the promise problem in time `T`. -/
def InPrBPTIME (P : PromiseProblem) (T : ℕ → ℕ) : Prop := ∃ M : Machine, DecidesWithin M T P

/-- **`prBPP`**: decidable in randomized time `p(n)` for a polynomial `p`. -/
def InPrBPP (P : PromiseProblem) : Prop :=
  ∃ p : Polynomial ℕ, InPrBPTIME P (fun n => p.eval n)

/-- **`BPP`** (for a language `L`): the promise problem `(L, Lᶜ)` is in `prBPP`. -/
def InBPP (L : Set (List Bool)) : Prop := InPrBPP ⟨L, Lᶜ⟩

end AvgWorstGap


