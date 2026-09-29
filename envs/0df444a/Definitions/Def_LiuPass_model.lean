-- Prove2me | Definitions.Def_LiuPass_model
-- name    : LiuPass_model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T22:23:19.432417+00:00
-- url     : https://prove2.me/theorems/8f65df09-e026-4b0d-821e-04ff59996e21
-- title:
--   Liu–Pass: universal machine, PPT algorithms and $K^t$
-- statement:
--   This file fixes the computational model of Liu–Pass, *On One-way Functions and Kolmogorov
--   Complexity* (Section 2).
--
--   Strings are finite lists of bits; $1^n$ denotes the all-ones string of length $n$, and a bit
--   string is read as a natural number most-significant-bit first when an algorithm's output is
--   interpreted numerically. A function $p : \mathbb{N} \to \mathbb{N}$ is *polynomial* if
--   $p(n) \le c n^k + c$ for some constants $k, c$, and $\mu : \mathbb{N} \to \mathbb{R}$ is
--   *negligible* if for every $k$ it is eventually at most $n^{-k}$. Probabilities over uniform
--   strings are defined by counting: for a predicate $P$,
--   $$\Pr[x \leftarrow \{0,1\}^n : P(x)] = \frac{\#\{v \in \{0,1\}^n : P(v)\}}{2^n},$$
--   and similarly for two independent uniform strings.
--
--   The paper fixes once and for all a universal Turing machine $U$ that emulates any machine with
--   polynomial overhead, writes $U(\Pi, 1^t)$ for the output of the description $\Pi$ emulated for
--   $t$ steps, and measures all running times on $U$. That standing convention is recorded here as a
--   structure: a partial, step-indexed evaluation $U(\Pi, 1^t)$ that is monotone in $t$ (once the
--   machine halts with an output, running longer does not change it), a pairing of a description
--   with an input whose length overhead is a constant, a constant-size program that immediately
--   returns its input, a self-simulation program with polynomial time overhead, a padding program
--   that copies a prefix of its input and applies a subprogram to the remaining suffix, and
--   universality: every function computable within a polynomial time bound has a program on $U$
--   running in polynomial time.
--
--   Relative to such a machine, a string function is computable in time $T$ if some description
--   computes it on every input within $T(|w|)$ steps, and polynomial-time computable if $T$ may be
--   taken polynomial; a probabilistic polynomial-time algorithm is a two-argument polynomial-time
--   function $\mathrm{out}(r, x)$ of a random tape $r$ and an input $x$, together with a polynomial
--   bound on the number of coins tossed at each security parameter. A generator is *rate-1
--   efficient* if its running time on inputs of length $n$ is at most $n + O(n^{\varepsilon})$ for a
--   constant $\varepsilon < 1$.
--
--   Finally, the $t$-time-bounded Kolmogorov complexity is
--   $$K^t(x) = \min\{\,|\Pi| \;:\; U(\Pi, 1^{t(|x|)}) = x\,\},$$
--   the length of the shortest description that outputs $x$ within $t(|x|)$ steps.
--
--   **Formalization Note** The universal machine is a parameter, not a construction: every statement
--   of the mission is quantified over all machines satisfying the interface above. The minimum
--   defining $K^t$ is an infimum over natural numbers, so it evaluates to $0$ when no description
--   outputs $x$ within the time bound; Fact 2.1 is what excludes that case.
-- source:
--   Yanyi Liu, Rafael Pass, On One-way Functions and Kolmogorov Complexity, arXiv:2009.11514v1 (FOCS 2020), https://arxiv.org/abs/2009.11514, Section 2 (pp. 7-9): the universal machine convention of Section 2.2 and the PPT/negligibility conventions of Section 2

import Mathlib

/-!
# Liu–Pass, *On One-way Functions and Kolmogorov Complexity* — the computational model

This file fixes the computational model underlying the paper
(Y. Liu, R. Pass, arXiv:2009.11514v1, Section 2).

The paper fixes once and for all a universal Turing machine `U` "that can emulate any Turing
machine `M` with polynomial overhead", writes `U (Π, 1^t)` for the output of the description `Π`
emulated on `U` for `t` steps, and measures every algorithm's running time in `U`-steps.  Here
that standing convention is recorded as the structure `LiuPass.UMachine`: a step-bounded
evaluation function together with the properties of a universal machine that the paper uses.
Every statement of the mission is universally quantified over such a machine.

Main definitions:

* `LiuPass.UMachine` — a universal machine with time-bounded semantics;
* `LiuPass.ComputesInTime`, `LiuPass.PolyTimeComputable`, `LiuPass.PPT` — deterministic and
  probabilistic polynomial-time algorithms relative to `U`;
* `LiuPass.Kt` — the `t`-time-bounded Kolmogorov complexity `K^t` (Section 2.2);
* `LiuPass.Rate1Efficient` — running time `n + O(n^ε)` with `ε < 1` (Definition 5.1).
-/

namespace LiuPass

open Finset
open scoped Classical

/-- A finite binary string. -/
abbrev BitStr := List Bool

/-- The all-ones string `1^n`, used as the unary encoding of `n`. -/
def unary (n : ℕ) : BitStr := List.replicate n true

/-- The natural number a bit string denotes, most significant bit first.  Used to read the
numerical output of a heuristic. -/
def bitsToNat (x : BitStr) : ℕ := x.foldl (fun a b => 2 * a + (if b then 1 else 0)) 0

/-- `p` is bounded by a polynomial. -/
def IsPoly (p : ℕ → ℕ) : Prop := ∃ k c : ℕ, ∀ n, p n ≤ c * n ^ k + c

/-- `μ` is negligible: it is eventually below `1 / n ^ k` for every `k`. -/
def Negligible (mu : ℕ → ℝ) : Prop := ∀ k : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, mu n ≤ 1 / (n : ℝ) ^ k

/-- `Pr[x ← {0,1}^n : P x]`. -/
noncomputable def prUnif (n : ℕ) (P : BitStr → Prop) : ℝ :=
  ((univ.filter fun v : Fin n → Bool => P (List.ofFn v)).card : ℝ) / 2 ^ n

/-- `Pr[x ← {0,1}^n, r ← {0,1}^m : P x r]`, for two independent uniform strings. -/
noncomputable def prUnif₂ (n m : ℕ) (P : BitStr → BitStr → Prop) : ℝ :=
  ((univ.filter fun v : (Fin n → Bool) × (Fin m → Bool) =>
      P (List.ofFn v.1) (List.ofFn v.2)).card : ℝ) / 2 ^ (n + m)

/-- `F` is computed within the time bound `T` in Mathlib's fuel-bounded model of partial
recursive functions.  This is used only to express the universality of `U`: every function that
some machine computes in polynomial time also has a `U`-program running in polynomial time. -/
def CodeComputableInTime (F : BitStr → BitStr) (T : ℕ → ℕ) : Prop :=
  ∃ c : Nat.Partrec.Code, ∀ w : BitStr,
    Nat.Partrec.Code.evaln (T w.length) c (Encodable.encode w) = some (Encodable.encode (F w))

/-- The fixed universal machine of Liu–Pass, Section 2.2.

`run Π t = some x` means that the description `Π`, emulated on the machine for `t` steps, halts
and outputs `x`; `run Π t = none` means it has not halted within `t` steps.  The remaining fields
record the properties of a universal machine with polynomial overhead that the paper relies on:
a description can be paired with an input at constant additive cost in length, there is a
constant-size program that just copies its input (this is what makes `K^t (x) ≤ |x| + c`), the
machine simulates its own time-bounded evaluation with polynomial overhead, it can copy an
untouched prefix of its input and run a subprogram on the remaining suffix (the padding trick),
and it has a polynomial-time program for every polynomial-time computable function. -/
structure UMachine where
  /-- `run Π t` is the output of the description `Π` emulated for `t` steps, if it halts. -/
  run : BitStr → ℕ → Option BitStr
  /-- Once the machine has halted with an output, running it longer changes nothing. -/
  run_mono : ∀ (Pi : BitStr) (t t' : ℕ) (x : BitStr), t ≤ t' → run Pi t = some x →
    run Pi t' = some x
  /-- Pairing a program with an input. -/
  pair : BitStr → BitStr → BitStr
  /-- The constant length overhead of pairing. -/
  pairOverhead : ℕ
  pair_length_le : ∀ Pi w : BitStr, (pair Pi w).length ≤ Pi.length + w.length + pairOverhead
  /-- A program that halts immediately, returning its input. -/
  idProg : BitStr
  run_idProg : ∀ (w : BitStr) (t : ℕ), 1 ≤ t → run (pair idProg w) t = some w
  /-- A program simulating the machine's own time-bounded evaluation. -/
  sim : BitStr
  /-- The polynomial overhead of that simulation. -/
  simTime : ℕ → ℕ
  simTime_poly : IsPoly simTime
  run_sim : ∀ (Pi : BitStr) (t : ℕ),
    run (pair sim (pair Pi (unary t))) (simTime (Pi.length + t)) = some ((run Pi t).getD [])
  /-- Given a program `Π` and a length `k`, a program that copies the first `k` bits of its input
  and runs `Π` on the rest. -/
  padProg : BitStr → ℕ → BitStr
  /-- The constant time overhead of the padding construction. -/
  padOverhead : ℕ
  run_padProg : ∀ (Pi : BitStr) (k t : ℕ) (w y : BitStr),
    run (pair Pi (w.drop k)) t = some y →
    run (pair (padProg Pi k) w) (w.length + t + padOverhead) = some (w.take k ++ y)
  /-- Universality with polynomial overhead. -/
  univ_prog : ∀ (F : BitStr → BitStr) (T : ℕ → ℕ), IsPoly T → CodeComputableInTime F T →
    ∃ T' : ℕ → ℕ, IsPoly T' ∧ ∃ Pi : BitStr, ∀ w : BitStr,
      run (pair Pi w) (T' w.length) = some (F w)

/-- `U` computes the string function `F` within the time bound `T`, as a function of the input
length. -/
def ComputesInTime (U : UMachine) (T : ℕ → ℕ) (F : BitStr → BitStr) : Prop :=
  ∃ Pi : BitStr, ∀ w : BitStr, U.run (U.pair Pi w) (T w.length) = some (F w)

/-- `F` is computable in polynomial time on `U`. -/
def PolyTimeComputable (U : UMachine) (F : BitStr → BitStr) : Prop :=
  ∃ T : ℕ → ℕ, IsPoly T ∧ ComputesInTime U T F

/-- A two-argument string function is computable in polynomial time on `U`. -/
def PolyTimeComputable₂ (U : UMachine) (F : BitStr → BitStr → BitStr) : Prop :=
  ∃ T : ℕ → ℕ, IsPoly T ∧ ∃ Pi : BitStr, ∀ r w : BitStr,
    U.run (U.pair Pi (U.pair r w)) (T (r.length + w.length)) = some (F r w)

/-- A probabilistic polynomial-time algorithm: `out r x` is the output on input `x` when the
random tape is `r`, and on a security parameter `n` the algorithm tosses `tape n` coins. -/
structure PPT (U : UMachine) where
  /-- The number of random bits used on security parameter `n`. -/
  tape : ℕ → ℕ
  /-- `out r x` is the output on input `x` with random tape `r`. -/
  out : BitStr → BitStr → BitStr
  tape_poly : IsPoly tape
  out_poly : PolyTimeComputable₂ U out

/-- Rate-1 efficiency (Definition 5.1): the running time on inputs of length `n` is
`n + O(n^ε)` for some constant `ε < 1`. -/
def Rate1Efficient (U : UMachine) (G : BitStr → BitStr) : Prop :=
  ∃ (eps : ℝ) (c : ℕ), 0 ≤ eps ∧ eps < 1 ∧
    ComputesInTime U (fun n => n + c * ⌈(n : ℝ) ^ eps⌉₊ + c) G

/-- The `t`-time-bounded Kolmogorov complexity `K^t (x)` (Section 2.2): the length of the
shortest description that outputs `x` on `U` within `t (|x|)` steps. -/
noncomputable def Kt (U : UMachine) (t : ℕ → ℕ) (x : BitStr) : ℕ :=
  sInf {l : ℕ | ∃ Pi : BitStr, Pi.length = l ∧ U.run Pi (t x.length) = some x}

end LiuPass


