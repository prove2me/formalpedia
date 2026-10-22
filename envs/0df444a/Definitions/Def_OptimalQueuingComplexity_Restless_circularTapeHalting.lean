-- Prove2me | Definitions.Def_OptimalQueuingComplexity_Restless_circularTapeHalting
-- name    : OptimalQueuingComplexity_Restless_circularTapeHalting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-02T11:40:21.26697+00:00
-- url     : https://prove2.me/theorems/fbb7f0e3-872f-4f51-aa8e-81f966bcb492
-- title:
--   The circular-tape process and its halting problem (proof of Theorem 4)
-- statement:
--   An instance consists of a circular tape with squares $1, \dots, n$, each holding a value in $\{1, \dots, A\}$; a rule $F : \{1,\dots,A\}^2 \to \{1,\dots,A\}$ with $F(1,1) = 1$; and an initial configuration $v(0) = (v_1(0), \dots, v_n(0))$. A head visits the squares cyclically: at time $t$ it points at the square $i$ with $i \equiv t \pmod n$ (square $n$ at time $0$), replaces the value there by $F(v_{i-1 \bmod n}, v_i)$ (the predecessor of square $1$ is square $n$), and moves to the next square. Thus
--   $$v_i(t+1) = \begin{cases} F\bigl(v_{i-1 \bmod n}(t),\, v_i(t)\bigr), & i \equiv t \pmod n,\\ v_i(t), & \text{otherwise.}\end{cases}$$
--   The process **halts** if at some time $t$ all squares have the value $1$.
--
--   **CIRCULAR-TAPE HALTING** is the decision problem: given such an instance with $n \ge 1$, does the process halt? Instances are encoded as $\mathrm{encNat}(n)$, $\mathrm{encNat}(A)$, the $A^2$ entries of the table of $F$ row by row, and the $n$ initial values.
--
--   This is the problem from which the paper reduces to RESTLESS BANDITS; it abstracts a space-bounded Turing machine computing in place on a circular tape.
--
--   **Formalization Note.** Squares are `Fin n` (index $j$ is square $j+1$) and values are `Fin A` (index $a$ is value $a+1$, so the paper's value $1$ is the index $0$). The paper's display prints the first case as "if $i = t \bmod n$" next to $v_i(t)$, which would update every square but one; the prose above it says that only the square under the head is updated. The formalization follows the prose, and fixes the head at square $i \equiv t \pmod n$ at time $t$, as the display indicates. Well-formedness ($n \ge 1$ and $F(1,1) = 1$) is part of the problem: an ill-formed instance is a no-instance.
-- source:
--   Papadimitriou & Tsitsiklis, The Complexity of Optimal Queuing Network Control, Math. Oper. Res. 24(2) (1999), p. 303, proof of Theorem 4 (the circular-tape process and its halting)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

namespace OptimalQueuingComplexity.Restless

/-- An instance of the **circular-tape halting problem** (Papadimitriou & Tsitsiklis 1999,
proof of Theorem 4, p. 303): "a circular tape, with squares `1, …, n`; each square can take values
in a set `{1, …, A}`", a rule `F`, and an initial configuration of the tape.

* The squares `1, …, n` are `Fin n`: the index `j : Fin n` is square `j + 1`.
* The values `1, …, A` are `Fin A`: the index `a : Fin A` is the value `a + 1`; in particular
  the paper's value `1` is the index `0`.
* `F a b` is the paper's `F(a, b)`, given as a full table on `{1, …, A}²`.
* `v0 j` is the value of square `j + 1` at time `0`. -/
structure TapeInstance where
  /-- number of squares of the circular tape -/
  n : ℕ
  /-- number of values a square can take -/
  A : ℕ
  /-- the update rule `F : {1,…,A} × {1,…,A} → {1,…,A}` -/
  F : Fin A → Fin A → Fin A
  /-- the initial configuration `v(0)` of the tape -/
  v0 : Fin n → Fin A

/-- The binary encoding of a tape instance: `encNat n`, `encNat A`, the table of `F` row by row
(`A²` entries, each an `encFin`), and the `n` initial values (each an `encFin`). Its length is
polynomial in `n + A²·log A` and conversely. -/
def TapeInstance.enc (I : TapeInstance) : List Bool :=
  encNat I.n ++ encNat I.A ++ encTable (encTable encFin) I.F ++ encTable encFin I.v0

/-- Well-formedness: the tape has at least one square, and `F(1, 1) = 1` (value `1` is the
index `0`). With `n ≥ 1` the initial configuration forces `A ≥ 1`. -/
def TapeInstance.WellFormed (I : TapeInstance) : Prop :=
  0 < I.n ∧ ∀ a : Fin I.A, a.val = 0 → I.F a a = a

/-- The square preceding square `j` on the circular tape: square `i − 1` for `i > 1`, and
square `n` for square `1` (in `Fin n`: `j − 1 mod n`). -/
def TapeInstance.pred (I : TapeInstance) (j : Fin I.n) : Fin I.n :=
  ⟨(j.val + I.n - 1) % I.n, Nat.mod_lt _ j.pos⟩

/-- The configuration of the tape at time `t`. The head is at the square `i` with
`i ≡ t (mod n)` at time `t` (square `n` at time `0`); that square is updated to
`F(v_{i−1 mod n}(t), v_i(t))` and every other square keeps its value:
`v_i(t+1) = v_i(t)` if `i ≢ t (mod n)`, and `v_i(t+1) = F(v_{i−1 mod n}(t), v_i(t))` otherwise.
Then the head moves to the next square (from square `n` back to square `1`). In `Fin n`, square
`j + 1` is the one under the head iff `(j + 1) mod n = t mod n`. -/
def TapeInstance.config (I : TapeInstance) : ℕ → Fin I.n → Fin I.A
  | 0 => I.v0
  | t + 1 => fun j =>
      if (j.val + 1) % I.n = t % I.n then I.F (I.config t (I.pred j)) (I.config t j)
      else I.config t j

/-- The process **halts** if at some time all squares have the value `1` (the index `0`). -/
def TapeInstance.Halts (I : TapeInstance) : Prop :=
  ∃ t : ℕ, ∀ j : Fin I.n, (I.config t j).val = 0

/-- **CIRCULAR-TAPE HALTING** (p. 303): given a well-formed instance — an initial configuration
of the tape and a rule `F` with `F(1, 1) = 1` — does the process eventually halt? -/
def circularTapeHalting (I : TapeInstance) : Prop :=
  I.WellFormed ∧ I.Halts

end OptimalQueuingComplexity.Restless


