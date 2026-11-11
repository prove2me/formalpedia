-- Prove2me | Definitions.Def_QNatProofs_OracleAlg
-- name    : QNatProofs_OracleAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:19.304049+00:00
-- url     : https://prove2.me/theorems/e6cf6531-2de7-46b7-85fc-86895a6d8663
-- title:
--   Uniform probabilistic classical oracle algorithms, their running time and distinguishing advantage
-- statement:
--   A **classical oracle algorithm** $B$ is uniform, probabilistic and adaptive. On an input string it reads a number of fair coins that depends on the input length. It then runs in rounds: in each round one fixed multi-stack Turing machine computes, from the input, the oracle answers received so far and the coins (written in that order), either an output bit (and halts) or the next oracle query. $B$ **runs in time at most $t$** on an input against oracles $\{0,1\}^a \to \{0,1\}^b$ if, for every function $F : \{0,1\}^a \to \{0,1\}^b$ used as the oracle (queries of another length get the empty answer) and every coin string, it halts and the number of coins plus the machine steps of all rounds plus the total length of the queries and answers is at most $t$. A **query-free** algorithm never queries; it is a plain probabilistic classical algorithm.
--
--   For a keyed family $\{F_k:\{0,1\}^a\to\{0,1\}^b\}_{k\in\mathcal K}$ the **distinguishing advantage** of $B$ on an input is
--   $$
--   \Big|\Pr_{k\leftarrow\mathcal K}\big[B^{F_k}=1\big]-\Pr_{U}\big[B^{U}=1\big]\Big|,
--   $$
--   with $U$ a uniformly random function $\{0,1\}^a\to\{0,1\}^b$ and probabilities also over the coins of $B$.
--
--   This is the adversary model of Definition 3.2, Fact 3.2 and Theorem 3.3.
--
--   **Formalization Note** The model is the formal reading of "classical oracle algorithm running in time $t$", which the paper does not specify further. A query of the wrong length is answered by the empty string.
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 3.2, p.16; Fact 3.2, p.16; Theorem 3.3, p.15

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Algorithms

set_option autoImplicit false

namespace QNatProofs

open PPADSIS.SubexpSIS

/-- A **classical oracle algorithm** (uniform, probabilistic, adaptive), the model of the oracle
distinguishers of Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…), Definition 3.2
(p.16), Fact 3.2 (p.16) and Theorem 3.3 (p.15).

On input `inp` it reads `coins |inp|` fair coins `c`. It then proceeds in rounds: in each round
it computes `next` on its configuration (the input, the oracle answers received so far and the
coins, each written as a self-delimiting string). An output `true :: b :: _` halts with output bit
`b`; an output `false :: q` queries the oracle at `q` and continues with the answer appended;
any other output halts with output `0`. One fixed multi-stack Turing machine (Mathlib's `FinTM2`)
computes `next` on every configuration `cfg` within `cost cfg` steps. -/
structure OracleAlg where
  /-- The number of fair coins read on an input of the given length. -/
  coins : ℕ → ℕ
  /-- The next-move function. -/
  next : List Bool → List Bool
  /-- A bound on the number of machine steps of one round, for each configuration. -/
  cost : List Bool → ℕ
  /-- One fixed machine computes `next` within `cost` steps on every configuration. -/
  timed : TimeBoundedOn id next cost

/-- The configuration of a round: the input, the answers received so far, and the coins.

**Formalization Note** The coins come last, so a round that only needs the input and the
answers (to choose the next query) does not have to read past the coins. -/
def OracleAlg.config (inp c : List Bool) (ans : List (List Bool)) : List Bool :=
  encStr inp ++ ans.flatMap encStr ++ encStr c

/-- `B` **makes no oracle queries**: its next-move function never outputs a query `false :: q`,
so it halts in its first round. This is a plain probabilistic classical algorithm, such as the
distinguisher `A` of Theorem 3.3 (Li, Parham, arXiv:2610.06826 (held copy sha256 b604fa11…),
p.15), which receives an amplitude list and no oracle. -/
def OracleAlg.IsQueryFree (B : OracleAlg) : Prop :=
  ∀ cfg q : List Bool, B.next cfg ≠ false :: q

/-- Run `B` on input `inp` with coins `c` and oracle `O` for at most `f` rounds, starting from the
answers `ans`. The result is `some (b, τ)` if it halts with output bit `b` within `f` rounds, where
`τ` is its time: the sum over the rounds of `1 + cost` plus the lengths of the queries and the
answers. -/
def OracleAlg.exec (B : OracleAlg) (O : List Bool → List Bool) (inp c : List Bool) :
    ℕ → List (List Bool) → Option (Bool × ℕ)
  | 0, _ => none
  | f + 1, ans =>
    let cfg := OracleAlg.config inp c ans
    match B.next cfg with
    | true :: b :: _ => some (b, 1 + B.cost cfg)
    | false :: qry =>
        (B.exec O inp c f (ans ++ [O qry])).map fun r =>
          (r.1, r.2 + 1 + B.cost cfg + qry.length + (O qry).length)
    | _ => some (false, 1 + B.cost cfg)

/-- A function `{0,1}^a → {0,1}^b` as an oracle on bit strings: a query of length `a` is answered
by the value, any other query by the empty string. -/
def liftFn {a b : ℕ} (F : (Fin a → Bool) → (Fin b → Bool)) (q : List Bool) : List Bool :=
  if h : q.length = a then List.ofFn (F fun i => q.get (i.cast h.symm)) else []

/-- `B` **runs in time at most `t`** on input `inp` against oracles `{0,1}^a → {0,1}^b`: for every
function `F : {0,1}^a → {0,1}^b` (given as the oracle `liftFn F`) and every coin string of the
prescribed length it halts, and its time (the number of coins read plus the time of all rounds) is
at most `t`.

**Formalization Note** The time bound is required for the oracles of the distinguishing game
(every function `{0,1}^a → {0,1}^b`, which includes every key of a keyed family), not for
arbitrary string functions, whose answers could be arbitrarily long. -/
def OracleAlg.TimeBounded (B : OracleAlg) (a b : ℕ) (inp : List Bool) (t : ℝ) : Prop :=
  ∀ (F : (Fin a → Bool) → (Fin b → Bool)) (c : List Bool), c.length = B.coins inp.length →
    ∃ (f : ℕ) (bit : Bool) (τ : ℕ), B.exec (liftFn F) inp c f [] = some (bit, τ) ∧
      ((c.length + τ : ℕ) : ℝ) ≤ t

open Classical in
/-- `Pr[B^O(inp) = 1]` over the coins of `B`. -/
noncomputable def OracleAlg.accept (B : OracleAlg) (O : List Bool → List Bool)
    (inp : List Bool) : ℝ :=
  coinAvg (B.coins inp.length) fun c =>
    if ∃ (f τ : ℕ), B.exec O inp (List.ofFn c) f [] = some (true, τ) then 1 else 0

/-- The **distinguishing advantage** of `B` on input `inp` between the keyed family
`{F_k}_{k ∈ κ}` with a uniformly random key and a uniformly random function
`{0,1}^a → {0,1}^b`: `|Pr_k[B^{F_k}(inp) = 1] − Pr_U[B^U(inp) = 1]|`. -/
noncomputable def oracleAdv (B : OracleAlg) (inp : List Bool) {κ : Type} [Fintype κ] {a b : ℕ}
    (F : κ → (Fin a → Bool) → (Fin b → Bool)) : ℝ :=
  |(∑ k : κ, B.accept (liftFn (F k)) inp) / Fintype.card κ -
    (∑ U : (Fin a → Bool) → (Fin b → Bool), B.accept (liftFn U) inp) /
      Fintype.card ((Fin a → Bool) → (Fin b → Bool))|

end QNatProofs


