-- Prove2me | Definitions.Def_ExactPatternStream_StreamRun
-- name    : ExactPatternStream_StreamRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:03:22.477194+00:00
-- url     : https://prove2.me/theorems/6f92c21f-5c14-499c-9748-2c9d41c61d77
-- title:
--   §1 — the stream run of a program, its space, the correct answers
-- statement:
--   The input of Exact Pattern Matching is $(P[0],\dots,P[m-1],T[0],\dots,T[n-1])$ over $\Sigma=\{1,\dots,|\Sigma|\}$, and the algorithm knows $n,m,|\Sigma|$ in advance. For every $i\in[m-1\,.\,.\,n)$, after processing $T[i]$, it must output YES if $P=T(i-m\,.\,.\,i]$ and NO otherwise.
--
--   This definition runs a word-RAM program on such a stream: $n,m,|\Sigma|$ are its first input words; each stream character is delivered once the machine has blocked on an empty input; $c_j$ is the completed state after $j$ characters, and none if no completed state is reached. Space is $w$ bits per cell ever written. The correct answers are `truthList`.
--
--   **Formalization Note** The paper names no machine; the program is `DynBrooks.Program` (referenced). `Fin σ` in statements, $a+1$ in the stream. YES is the word $1$ and NO the word $0$. "Probability at least $c$" means a measurable subevent has measure at least $c$.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), §1, p.1 (PDF 2)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_ExactPatternStream_Strings

namespace ExactPatternStream

open MeasureTheory
open scoped ENNReal

/-! # The stream run of a program

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), §1, p.1 (PDF 2): the task "Exact
Pattern Matching" and its output convention.

**Formalization Note.** The paper names no machine. A program is a `DynBrooks.Program`: a finite list of
instructions, fixed before the word size, that has a coin tape it cannot rewind, a `read` that consumes
once and blocks until a word is delivered, and a `write` to an unreadable output. Space is `w` bits for
every cell ever written. The program knows `n, m, |Σ|` in advance: they are the first words it reads. `Σ`
is `{1, …, |Σ|}` in the stream (`p.1`) and `Fin σ` in statements, so a word is `a.val + 1`. YES is the word
`1` and NO is `0`. `streamState … j` is the completed state after `j` characters have been processed, and
is `none` if the run never reaches one (for instance after an endless rejection sampling loop). -/

/-- `ℓ(n) = max{1, ⌈log₂(n+1)⌉}`, the unit of the word size. -/
def ell (n : ℕ) : ℕ := max 1 (Nat.clog 2 (n + 1))

/-- The start of a run: program counter `0`, all cells zero, nothing written, nothing output. -/
def initConfig (w : ℕ) (input : List ℕ) : DynBrooks.Config w where
  pc := 0
  mem := fun _ => 0
  input := input
  coinPos := 0
  output := []
  written := ∅

/-- Space in bits: the word size times the number of cells ever written. -/
def spaceBits (w : ℕ) (c : DynBrooks.Config w) : ℕ := w * c.written.card

/-- The event `E` has probability at least `c` under `μ`: a measurable subevent has measure `≥ c`. -/
def ProbAtLeast {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω) (c : ℝ≥0∞) : Prop :=
  ∃ A, MeasurableSet A ∧ A ⊆ E ∧ c ≤ μ A

variable {σ : ℕ}

/-- The stream `(P[0], …, P[m-1], T[0], …, T[n-1])` as words `1..σ`. -/
def streamWords (P T : List (Fin σ)) : List ℕ := (P ++ T).map fun a => a.val + 1

/-- The start of a stream run: `n, m, |Σ|` are delivered first. -/
def startConfig (w : ℕ) (P T : List (Fin σ)) : DynBrooks.Config w :=
  initConfig w [T.length, P.length, σ]

/-- The completed state `c_j` after `j` characters of the stream, on tape `ω`. -/
noncomputable def streamState (Q : DynBrooks.Program) {w : ℕ} (P T : List (Fin σ))
    (ω : ℕ → BitVec w) : ℕ → Option (DynBrooks.Config w)
  | 0 => DynBrooks.complete Q ω (startConfig w P T)
  | j + 1 => (streamState Q P T ω j).bind fun c =>
      DynBrooks.complete Q ω (DynBrooks.feed c [(streamWords P T).getD j 0])

/-- `P = T(i - m . . i]`: the pattern ends at position `i` of the text. -/
def EndsAt (P T : List (Fin σ)) (i : ℕ) : Prop :=
  P.length ≤ i + 1 ∧ slice T (i + 1 - P.length) (i + 1) = P

instance (P T : List (Fin σ)) (i : ℕ) : Decidable (EndsAt P T i) := by
  unfold EndsAt; infer_instance

/-- The correct answers, for `i = m - 1, …, n - 1`: `1` for YES, `0` for NO. -/
def truthList (P T : List (Fin σ)) : List ℕ :=
  (List.range (T.length + 1 - P.length)).map fun a =>
    if EndsAt P T (P.length - 1 + a) then 1 else 0

end ExactPatternStream


