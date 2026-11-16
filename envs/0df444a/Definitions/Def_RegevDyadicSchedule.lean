-- Prove2me | Definitions.Def_RegevDyadicSchedule
-- name    : RegevDyadicSchedule
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T10:24:32.568465+00:00
-- url     : https://prove2.me/theorems/0694a2e9-d543-4475-abe3-e4599e9272aa
-- title:
--   Binary dyadic width scan for Gaussian lattice sampling
-- statement:
--   For rational initial and requested widths $W,r$ and a natural dimension $n$, these definitions specify a finite dyadic scan. Its loop bound is the sum of the binary lengths of the absolute numerator of $W$ and the denominator of $r$. At index $j$ the candidate is $W/2^j$, and the comparison is performed over rationals by testing $2n(W/2^j)^2\le r^2(n+2)^2$.
--
--   The returned pair consists of the first satisfying index and its candidate width when such an index occurs in the scan. Otherwise `findIdx` returns the scan length, and the width computation caps its exponent at the number of available ticks. The definitions are total also on inputs that do not satisfy the positivity hypotheses used in the correctness theorem.
-- source:
--   Oded Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, Theorem 3.1 and Lemmas 3.2, 3.3, 3.14. This binary dyadic schedule is an explicit fixed-family implementation interface, not a verbatim definition in the paper.

import Definitions.Def_InfoLossLAR_FirstBridgeBundle_01

set_option autoImplicit false
namespace InfoLossLAR.WorstCase.NativeDyadicSchedule
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Integration9_9.TM2NativeFiniteDraw

/-- Initial width, requested width and dimension. -/
abbrev Input := (ℚ × ℚ) × ℕ

/-- Unary loop bound derived from binary lengths, never from numeric magnitude. -/
def ticks (x : Input) : List Unit :=
  (Nat.bits x.1.1.num.natAbs).map (fun _ => ()) ++
  (Nat.bits x.1.2.den).map (fun _ => ())

def width (x : Input × ℕ) : ℚ :=
  x.1.1.1 / (dyadicPower ((ticks x.1).take x.2) : ℚ)

/-- Crossing is tested by comparing rational squares. -/
def crossingTest (x : Input × ℕ) : Bool :=
  decide ((2 : ℚ) * (x.1.2 : ℚ) * width x^2 ≤
    x.1.1.2^2 * ((x.1.2 : ℚ)+2)^2)

def crossingIndex (x : Input) : ℕ :=
  (List.range ((ticks x).length+1)).findIdx (fun j => crossingTest (x,j))

def selectedWidth (x : Input) : ℚ := width (x,crossingIndex x)

/-- The binary index and the selected rational source width. -/
def result (x : Input) : ℕ × ℚ := (crossingIndex x, selectedWidth x)

end InfoLossLAR.WorstCase.NativeDyadicSchedule


