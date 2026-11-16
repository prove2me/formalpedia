-- Prove2me | Definitions.Def_SuperRamanujan227_Main_Supplement_Computation
-- name    : SuperRamanujan227_Main_Supplement_Computation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:43:09.202208+00:00
-- url     : https://prove2.me/theorems/c3bfd194-1e4e-40b4-adc0-f6a54e832f3e
-- title:
--   Binary graph encodings and measured finite-machine execution
-- statement:
--   Natural numbers are written in binary and framed by replacing each digit $b$ with $(1,b)$ and appending a terminating $0$. Concatenation gives an unambiguous encoding of $(n,d)$ and of $(n,d,s)$, where a positive rational $s$ is encoded by its reduced numerator and positive denominator. A graph output lists all $n^2$ adjacency multiplicities in row-major order with the same framing. Let $L(s)$ be the sum of the unframed binary lengths of that numerator and denominator. With these fixed encodings,
--
--   $$
--   \operatorname{Runs}(M,u,v,t)\quad\Longleftrightarrow\quad M\text{ halts on }u\text{ with output }v\text{ in at most }t\text{ steps}.
--   $$
--
--   Here $M$ is Mathlib's finite multi-stack Turing machine with binary input and output alphabets, and the relation uses its actual execution semantics. Instructions have fixed finite cost, so step time and ordinary bit time differ by a machine-dependent constant. This interface contains no spectral correctness assumption, efficiency oracle, or graph-selection axiom. Existential constants and degrees in the theorem statements bound a single machine uniformly before any input is supplied.
-- source:
--   Gil Cohen, Gal Maor, STOC 2027 submission #227 (October 2026), pp. 5, 13–16, Theorems 1.2, 4.1, 4.5 and exact-arithmetic implementation discussion

import Mathlib
import Definitions.Def_SuperRamanujan227_Main_Multigraph

namespace SuperRamanujan227.Main.Supplement

/-- A binary self-delimiting natural: double each binary digit as (true,digit), then false.
This fixes an injective binary input/output encoding without a unit-cost arithmetic oracle. -/
def natBits (a : ℕ) : List Bool :=
  (Computability.encodeNat a).flatMap (fun b => [true, b]) ++ [false]

/-- Binary input for the construction problems. -/
def graphInput (n d : ℕ) : List Bool := natBits n ++ natBits d

/-- Reduced rational numerator and denominator; used only for positive rationals. -/
def thresholdInput (n d : ℕ) (s : ℚ) : List Bool :=
  graphInput n d ++ natBits s.num.natAbs ++ natBits s.den

/-- Total binary length of the reduced numerator and denominator (without framing). -/
def rationalBits (s : ℚ) : ℕ :=
  (Computability.encodeNat s.num.natAbs).length + (Computability.encodeNat s.den).length

/-- Row-major binary adjacency multiplicities, including diagonal entries counted twice. -/
def graphOutput {n : ℕ} (G : Multigraph n) : List Bool :=
  (List.finRange n).flatMap fun u => (List.finRange n).flatMap fun v => natBits (G.adj u v)

/-- Actual execution of one fixed finite machine, with an upper bound on its stack-machine
steps. Each instruction has fixed finite cost; this is equivalent to bit time up to a
machine-dependent constant. No correctness or efficiency premise is built into this relation. -/
def Runs (M : Turing.TM2ComputableAux Bool Bool) (input output : List Bool) (t : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (input.map M.inputAlphabet.symm)
    (some (output.map M.outputAlphabet.symm)) t)

end SuperRamanujan227.Main.Supplement


