-- Prove2me | Definitions.Def_FasterPrimeEnum_RunsWithin
-- name    : FasterPrimeEnum_RunsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:37:57.983884+00:00
-- url     : https://prove2.me/theorems/04557406-b202-40e0-8d0d-30854c69e33a
-- title:
--   A machine run within time $\tau$; standard binary words
-- statement:
--   A machine $A$ **runs within time** $\tau$ on an input word, with a given output word on its tape $\mathrm{out}$, if, started with the input on its input tape and all other tapes blank, it reaches after at most $\tau$ steps a halted configuration whose tape $\mathrm{out}$ holds exactly the output word, with the head on its first cell.
--
--   The **standard binary word** of a natural number $n$ is its list of binary digits, most significant first; the word of $0$ is the single digit $0$.
--
--   These are the time measure and the number format of the paper: time is the number of steps of a multitape Turing machine, and integers are written in standard binary.
--
--   **Formalization Note** The machine is the published `PrimitiveMachine` of `SubexponentialSAT`: a deterministic multitape machine over the alphabet blank, $0$, $1$ that reads one tape per step and either halts or writes or moves on that tape. It simulates the paper's multitape machines, and is simulated by them, with a constant-factor loss in time. Since the whole halted output tape is pinned, the output is a function of the input.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), §1.3, p.3 (model); §1.4, p.4 (standard binary notation)

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

namespace FasterPrimeEnum

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **A run within time `τ`** — the machine reading of "runs in time …" in D. Harvey,
*Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), §1.3, p.3:
"we will work in the standard multitape Turing model. In this model, time complexity refers to the
number of steps (or "bit operations") performed by the Turing machine."

Started on `input` (written on its input tape, all other tapes blank), the machine `A` reaches,
after some number `time ≤ τ` of steps, a halted configuration whose tape `out` holds exactly the
word `output`, with the head on its first cell.

**Formalization Note.** The machine model is the published `SubexponentialSAT` one:
`PrimitiveMachine` is a deterministic multitape machine over the alphabet `Option Bool`
(blank, 0, 1) that reads one tape per step and either halts or writes or moves on that tape. It
simulates the paper's multitape machines with a constant-factor loss in time, and conversely.
The predicate pins the halted configuration and the whole output tape, so the output is
determined by the input. There is no space clause (the paper bounds time only). -/
def RunsWithin (A : PrimitiveMachine) (out : Fin A.tapeCount) (input output : List Bool)
    (τ : ℝ) : Prop :=
  ∃ (time : ℕ) (final : A.Cfg),
    Trace A.step time (A.init input) final ∧
    (∃ b : Bool, final.state = Sum.inl b) ∧
    final.tapes out = Turing.Tape.mk₁ (output.map some) ∧
    (time : ℝ) ≤ τ

/-- **Standard binary notation** (p.4: "the primes are written in standard binary notation"):
the binary digits of `n`, most significant bit first, with `binWord 0 = [false]`. It is the
reverse of the published `countWord` (least significant bit first). -/
def binWord (n : ℕ) : List Bool := (countWord n).reverse

end FasterPrimeEnum


